{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D024 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0181 ; wl0207 ; wl0217 ; wl0219 ; wl0220 ; wl0221 ; wl0222 ; wl0241 ; wl0244 ; wl0245 ; wl0246 ; wl0247 ; wl0256 ; wl0263 ; wl0274 ; wl0305 ; wl0312 ; wl0315 ; wl0317 ; wl0319 ; wl0322 ; wl0341 ; wl0405 ; wl0406 ; wl0407 ; wl0464 ; wl0508 ; wl0698 ; wl0729 ; wl0770 ; wl0872 ; wl1000 ; wl1037 ; wl1172 ; wl1173 ; wl1190 ; wl1206 ; wl1220 ; wl1221 ; wl1222 ; wl1223 ; wl1224 ; wl1233 ; wl1249 ; wl1269 ; wl1283 ; wl1284 ; wl1285 ; wl1286 ; wl1287 ; wl1288 ; wl1289 ; wl1290 ; wl1291 ; wp0034 ; wp0035 ; wp0036 ; wp0053 ; wp0060 ; wp0061 ; wp0062 ; wp0063 ; wp0064 ; wp0065 ; wp0066 ; wp0069 ; wp0070 ; wp0072 ; wp0074 ; wp0081 ; wp0087 ; wp0088 ; wp0089 ; wp0090 ; wp0094 ; wp0095 ; wp0097 ; wp0103 ; wp0167 ; wp0261 ; wp0272 ; wp0278 ; wp0301 ; wp0312 ; wp0313 ; wp0314 ; wp0575 ; wp0580 ; wp0582 ; wp0584 ; wp0617 ; wp0632 ; wp0633 ; wp0647 ; wp0785 ; wp0805 ; wp0806 ; wp0827 ; wp0842 ; wp0843 ; wp0845 ; wp0974 ; wp0977 ; wp0979 ; wp0980 ; wp0981 ; wp0982 ; wp1003 ; wp1005 ; wp1006 ; wp1007 ; wp1008 ; wp1017 ; wp1018 ; wp1020 ; wp1025 ; wp1026 ; wp1027 ; wp1041 ; wp1042 ; wp1110 ; wp1111 ; wp1112 ; wp1113 ; wp1114 ; wp1115 ; wp1116 ; wp1117 ; wp1118 ; wp1119 ; wp1120)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-Xb-box-at243243 ; lem-box-cP-at122441 ; lem-box-cP-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-box-tQ-at3443)
open import Examples.Groups.Clifford+CS.Five.D.D006 using (lem-box-perm-1324-at122441)
open import Examples.Groups.Clifford+CS.Five.D.D007 using (lem-box-perm-1324-at243243 ; lem-box-perm-1423-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D009 using (lem-F0-at14213243)
open import Examples.Groups.Clifford+CS.Five.D.D012 using (lem-box-perm-4213-at122441)
open import Examples.Groups.Clifford+CS.Five.D.D014 using (lem-S2-SBOX⟨0·1·42·3⟩)
open import Examples.Groups.Clifford+CS.Five.D.D015 using (lem-S2-SBOX⟨0·2·43·1⟩)
open import Examples.Groups.Clifford+CS.Five.D.D016 using (lem-box-perm-1324-at12233441)
open import Examples.Groups.Clifford+CS.Five.D.D017 using (lem-CKc-box-at12233441 ; lem-CKc-box-at13213442 ; lem-box-perm-3421-at122441 ; lem-box-perm-4312-at13213442)
open import Examples.Groups.Clifford+CS.Five.D.D018 using (lem-CKc-box-at233442 ; lem-box-perm-1342-at233442)
open import Examples.Groups.Clifford+CS.Five.D.D020 using (lem-F0-at01143043 ; lem-box-cP-at03243240 ; lem-box-perm-1324-at03243240 ; lem-box-perm-4213-at03243240)
open import Examples.Groups.Clifford+CS.Five.D.D022 using (lem-S2-SBOX⟨3·1·42·0⟩)
open import Examples.Groups.Clifford+CS.Five.D.D023 using (lem-CKc-box-at0312203441 ; lem-CKc-box-at033440 ; lem-S2-SBOX⟨3·0·41·2⟩ ; lem-box-perm-1324-at033440 ; lem-box-perm-3421-at03243240 ; lem-box-perm-4312-at0312203441 ; lem-nf-rel-266at0)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CX12-CCZ034)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-TOFF013-CSd24)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-comm-CCZ024-CX13 ; lem-comm-SWAP24-BOX⟨0·13⟩)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-comm-CCZ014-CX23 ; lem-comm-CCZ034-CX12 ; lem-comm-CCZ134-CX02 ; lem-comm-TOFF013-CS24 ; lem-comm-TOFF013-CX24 ; lem-comm-TOFF023-CX14 ; lem-comm-TOFF302-CS14 ; lem-comm-TOFF302-CSd14 ; lem-comm-TOFF302-CX14)
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


-- CXbc-box @3443: 17 steps
lem-CXbc-box-at3443 : Ws → ⟪ (CX24 ∷ Bx0-1243 ∷ CX24 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1243 ∷ CCZ123 ∷ []) ⟫ʷ
lem-CXbc-box-at3443 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX24 ∷ Bx0-1243 ∷ CX24 ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CX24 ∷ CCZ023 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CCZ034 ∷ CX12 ∷ CS13 ∷ CX24 ∷ [])
  b0 = at 1 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-box-tQ-at3443 c4) ▸
       at 0 2 (Toff012 ∷ CX24 ∷ []) (wp0977 c4) ▸
       at 1 2 (CCZ034 ∷ CX24 ∷ CCZ023 ∷ []) (sym (wp1017 c4)) ▸
       at 3 2 (Toff012 ∷ CCZ023 ∷ CCZ123 ∷ []) (wl1283 (lit c4)) ▸
       at 2 2 (Toff012 ∷ CX24 ∷ []) (wp0977 c4) ▸
       at 5 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0207 (lit c4)) ▸
       at 9 2 (CCZ034 ∷ CS13 ∷ []) (sym (wp0312 c4)) ▸
       at 8 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸ done

  b1 : Chain (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CX24 ∷ CCZ023 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CCZ034 ∷ CX12 ∷ CS13 ∷ CX24 ∷ []) (Bx0-1243 ∷ CX24 ∷ CCZ123 ∷ CX24 ∷ [])
  b1 = at 7 2 (CCZ034 ∷ CS23⁻ ∷ []) (sym (wp0313 c4)) ▸
       at 6 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸
       at 5 2 (CCZ034 ∷ CS23 ∷ []) (sym (wp0314 c4)) ▸
       at 6 5 (CCZ123 ∷ []) (sym (wl0207 (lit c4))) ▸
       at 4 2 (CCZ034 ∷ CCZ023 ∷ []) (wp0575 c4) ▸
       at 3 2 (CCZ034 ∷ CX24 ∷ CCZ023 ∷ []) (sym (wp1017 c4)) ▸
       at 4 3 (CX24 ∷ []) (wp1018 c4) ▸
       at 0 4 (Bx0-1243 ∷ []) (sym (lem-box-tQ-at3443 c4)) ▸ done

  b2 : Chain (Bx0-1243 ∷ CX24 ∷ CCZ123 ∷ CX24 ∷ []) (Bx0-1243 ∷ CCZ123 ∷ [])
  b2 = at 1 3 (CCZ123 ∷ []) (sym (wl0315 (lit c4))) ▸ done


-- CXcb-box @3443: 18 steps
lem-CXcb-box-at3443 : Ws → ⟪ (CX42 ∷ Bx0-1243 ∷ CX42 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1243 ∷ CCZ134 ∷ []) ⟫ʷ
lem-CXcb-box-at3443 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX42 ∷ Bx0-1243 ∷ CX42 ∷ []) (Toff012 ∷ CCZ034 ∷ CX42 ∷ Toff014 ∷ CS34 ∷ CX14 ∷ Toff012 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ CCZ034 ∷ CX42 ∷ [])
  b0 = at 1 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-box-tQ-at3443 c4) ▸
       at 0 2 (Toff012 ∷ CX42 ∷ Toff014 ∷ []) (wp1113 c4) ▸
       at 2 2 (CCZ034 ∷ Toff014 ∷ CCZ134 ∷ []) (sym (wp1114 c4)) ▸
       at 1 2 (CCZ034 ∷ CX42 ∷ []) (sym (wp1020 c4)) ▸
       at 4 1 (CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ []) (wl0698 (lit c4)) ▸
       at 8 2 (Toff012 ∷ CS13 ∷ []) (wl1284 (lit c4)) ▸
       at 7 2 (Toff012 ∷ CX14 ∷ []) (wp0974 c4) ▸
       at 6 2 (Toff012 ∷ CS34⁻ ∷ []) (sym (c₃ (Toff) (CS • CS • CS))) ▸ done

  b1 : Chain (Toff012 ∷ CCZ034 ∷ CX42 ∷ Toff014 ∷ CS34 ∷ CX14 ∷ Toff012 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ CCZ034 ∷ CX42 ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ CX42 ∷ CCZ134 ∷ CX42 ∷ [])
  b1 = at 5 2 (Toff012 ∷ CX14 ∷ []) (wp0974 c4) ▸
       at 4 2 (Toff012 ∷ CS34 ∷ []) (sym (c₃ (Toff) (CS))) ▸
       at 5 5 (CCZ134 ∷ []) (sym (wl0698 (lit c4))) ▸
       at 3 2 (Toff012 ∷ Toff014 ∷ []) (sym (wp0580 c4)) ▸
       at 2 2 (Toff012 ∷ CX42 ∷ Toff014 ∷ []) (wp1113 c4) ▸
       at 3 3 (CX42 ∷ []) (wp1115 c4) ▸
       at 4 2 (CCZ034 ∷ CCZ134 ∷ []) (sym (wp0103 c4)) ▸
       at 3 2 (CCZ034 ∷ CX42 ∷ []) (sym (wp1020 c4)) ▸ done

  b2 : Chain (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ CX42 ∷ CCZ134 ∷ CX42 ∷ []) (Bx0-1243 ∷ CCZ134 ∷ [])
  b2 = at 0 4 (Bx0-1243 ∷ []) (sym (lem-box-tQ-at3443 c4)) ▸
       at 1 3 (CCZ134 ∷ []) (sym (wl0312 (lit c4))) ▸ done


-- SWbc-box @3443: 11 steps
lem-SWbc-box-at3443 : Ws → ⟪ (Sw24 ∷ Bx0-1243 ∷ Sw24 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1243 ∷ []) ⟫ʷ
lem-SWbc-box-at3443 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw24 ∷ Bx0-1243 ∷ Sw24 ∷ []) (CX24 ∷ Bx0-1243 ∷ CX24 ∷ CCZ123 ∷ CCZ134 ∷ CCZ123 ∷ CCZ134 ∷ CCZ123 ∷ [])
  b0 = at 0 1 (CX24 ∷ CX42 ∷ CX24 ∷ []) (sym (wl0405 (lit c4))) ▸
       at 4 1 (CX24 ∷ CX42 ∷ CX24 ∷ []) (sym (wl0405 (lit c4))) ▸
       at 2 3 (Bx0-1243 ∷ CCZ123 ∷ []) (lem-CXbc-box-at3443 c4) ▸
       at 3 2 (CX42 ∷ CCZ134 ∷ CCZ123 ∷ []) (wl0319 (lit c4)) ▸
       at 1 3 (Bx0-1243 ∷ CCZ134 ∷ []) (lem-CXcb-box-at3443 c4) ▸
       at 4 2 (CX24 ∷ CCZ123 ∷ []) (wl0406 (lit c4)) ▸
       at 3 2 (CX24 ∷ CCZ123 ∷ CCZ134 ∷ []) (wl0317 (lit c4)) ▸
       at 2 2 (CX24 ∷ CCZ123 ∷ CCZ134 ∷ []) (wl0317 (lit c4)) ▸ done

  b1 : Chain (CX24 ∷ Bx0-1243 ∷ CX24 ∷ CCZ123 ∷ CCZ134 ∷ CCZ123 ∷ CCZ134 ∷ CCZ123 ∷ []) (Bx0-1243 ∷ [])
  b1 = at 3 5 (CCZ123 ∷ []) (wl0407 (lit c4)) ▸
       at 0 3 (Bx0-1243 ∷ CCZ123 ∷ []) (lem-CXbc-box-at3443 c4) ▸
       at 1 2 [] (wl0181 (lit c4)) ▸ done


-- nat-SWbc @3443: 23 steps
lem-nat-SWbc-at3443 : Ws → ⟪ (Sw24 ∷ Bx0-1243 ∷ Sw24 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ []) ⟫ʷ
lem-nat-SWbc-at3443 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw24 ∷ Bx0-1243 ∷ Sw24 ∷ []) (CCZ014 ∷ Toff014 ∷ CCZ012 ∷ Toff102 ∷ Bx0-13 ∷ Toff102 ∷ Sw24 ∷ CCZ014 ∷ Bx0-13 ∷ Toff012 ∷ CCZ012 ∷ Bx1-043 ∷ Sw24 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff012 ∷ Bx1-043 ∷ Toff012 ∷ CCZ012 ∷ Bx1-043 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw24 ∷ []) (sym (wp0584 c4)) ▸
       at 1 2 (Toff014 ∷ Sw24 ∷ []) (wp1116 c4) ▸
       at 3 1 (CCZ014 ∷ Toff104 ∷ Bx0-13 ∷ Toff104 ∷ CCZ014 ∷ Bx0-13 ∷ []) (refl) ▸
       at 2 2 (CCZ012 ∷ Sw24 ∷ []) (sym (wp0582 c4)) ▸
       at 3 2 (Toff102 ∷ Sw24 ∷ []) (wp1117 c4) ▸
       at 4 2 (Bx0-13 ∷ Sw24 ∷ []) (lem-comm-SWAP24-BOX⟨0·13⟩ (lit c4)) ▸
       at 5 2 (Toff102 ∷ Sw24 ∷ []) (wp1117 c4) ▸ done

  b1 : Chain (CCZ014 ∷ Toff014 ∷ CCZ012 ∷ Toff102 ∷ Bx0-13 ∷ Toff102 ∷ Sw24 ∷ CCZ014 ∷ Bx0-13 ∷ Toff012 ∷ CCZ012 ∷ Bx1-043 ∷ Sw24 ∷ []) (CCZ014 ∷ Toff014 ∷ CCZ012 ∷ Toff102 ∷ Bx0-13 ∷ Toff102 ∷ CCZ012 ∷ Bx0-13 ∷ Toff014 ∷ CCZ014 ∷ CCZ012 ∷ Toff102 ∷ Bx0-13 ∷ Sw24 ∷ Toff104 ∷ CCZ014 ∷ Bx0-13 ∷ Sw24 ∷ [])
  b1 = at 6 2 (CCZ012 ∷ Sw24 ∷ []) (sym (wp0582 c4)) ▸
       at 7 2 (Bx0-13 ∷ Sw24 ∷ []) (lem-comm-SWAP24-BOX⟨0·13⟩ (lit c4)) ▸
       at 8 2 (Toff014 ∷ Sw24 ∷ []) (wp1116 c4) ▸
       at 9 2 (CCZ014 ∷ Sw24 ∷ []) (sym (wp0584 c4)) ▸
       at 11 1 (CCZ014 ∷ Toff104 ∷ Bx0-13 ∷ Toff104 ∷ CCZ014 ∷ Bx0-13 ∷ []) (refl) ▸
       at 10 2 (CCZ012 ∷ Sw24 ∷ []) (sym (wp0582 c4)) ▸
       at 11 2 (Toff102 ∷ Sw24 ∷ []) (wp1117 c4) ▸
       at 12 2 (Bx0-13 ∷ Sw24 ∷ []) (lem-comm-SWAP24-BOX⟨0·13⟩ (lit c4)) ▸ done

  b2 : Chain (CCZ014 ∷ Toff014 ∷ CCZ012 ∷ Toff102 ∷ Bx0-13 ∷ Toff102 ∷ CCZ012 ∷ Bx0-13 ∷ Toff014 ∷ CCZ014 ∷ CCZ012 ∷ Toff102 ∷ Bx0-13 ∷ Sw24 ∷ Toff104 ∷ CCZ014 ∷ Bx0-13 ∷ Sw24 ∷ []) (Bx0-1423 ∷ [])
  b2 = at 13 2 (Toff102 ∷ Sw24 ∷ []) (wp1117 c4) ▸
       at 14 2 (CCZ012 ∷ Sw24 ∷ []) (sym (wp0582 c4)) ▸
       at 15 2 (Bx0-13 ∷ Sw24 ∷ []) (lem-comm-SWAP24-BOX⟨0·13⟩ (lit c4)) ▸
       at 16 2 [] (wl0322 (lit c4)) ▸
       at 2 6 (Bx1-023 ∷ []) (refl) ▸
       at 5 6 (Bx1-023 ∷ []) (refl) ▸
       at 0 6 (Bx0-1423 ∷ []) (refl) ▸ done


-- sym-bc @3443: 2 steps
lem-sym-bc-at3443 : Ws → ⟪ (Bx0-1243 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ []) ⟫ʷ
lem-sym-bc-at3443 c4 = run b0
  where
  b0 : Chain (Bx0-1243 ∷ []) (Bx0-1423 ∷ [])
  b0 = at 0 1 (Sw24 ∷ Bx0-1243 ∷ Sw24 ∷ []) (sym (lem-SWbc-box-at3443 c4)) ▸
       at 0 3 (Bx0-1423 ∷ []) (lem-nat-SWbc-at3443 c4) ▸ done


-- box-perm-1324 @3443: 1 steps
lem-box-perm-1324-at3443 : Ws → ⟪ (Bx0-1243 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ []) ⟫ʷ
lem-box-perm-1324-at3443 c4 = run b0
  where
  b0 : Chain (Bx0-1243 ∷ []) (Bx0-1423 ∷ [])
  b0 = at 0 1 (Bx0-1423 ∷ []) (lem-sym-bc-at3443 c4) ▸ done


-- CKc-box @3443: 61 steps
lem-CKc-box-at3443 : Ws → ⟪ (Bx0-1243 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CK43 ∷ CCZ123 ∷ Bx0-1243 ∷ []) ⟫ʷ
lem-CKc-box-at3443 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (run b7)))))))
  where
  b0 : Chain (Bx0-1243 ∷ CK43 ∷ []) (X4 ∷ Bx0-1243 ∷ CCZ123 ∷ K3 ∷ CK43 ∷ S4 ∷ CCZ123 ∷ X4 ∷ CCZ123 ∷ [])
  b0 = at 1 0 (CCZ123 ∷ CCZ123 ∷ []) (sym (wl0181 (lit c4))) ▸
       at 0 1 (Bx0-1423 ∷ []) (lem-box-perm-1324-at3443 c4) ▸
       at 0 2 (X4 ∷ Bx0-1423 ∷ X4 ∷ []) (sym (lem-Xb-box-at243243 c4)) ▸
       at 3 2 (CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ123 ∷ []) (sym (wl1172 (lit c4))) ▸
       at 2 2 (CCZ123 ∷ X4 ∷ []) (sym (c₄ (CCZ ↑) (X))) ▸
       at 3 2 (K3 ∷ CK43 ∷ S4 ∷ X4 ∷ []) (sym (wl0729 (lit c4))) ▸
       at 6 2 (CCZ123 ∷ X4 ∷ []) (sym (c₄ (CCZ ↑) (X))) ▸
       at 1 1 (Bx0-1243 ∷ []) (lem-box-perm-1324-at243243 c4) ▸ done

  b1 : Chain (X4 ∷ Bx0-1243 ∷ CCZ123 ∷ K3 ∷ CK43 ∷ S4 ∷ CCZ123 ∷ X4 ∷ CCZ123 ∷ []) (X4 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ123 ∷ CCZ034 ∷ K3 ∷ CK43 ∷ S4 ∷ CCZ123 ∷ X4 ∷ CCZ123 ∷ [])
  b1 = at 1 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-box-tQ-at3443 c4) ▸
       at 5 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0207 (lit c4)) ▸
       at 4 2 (CS23 ∷ CCZ034 ∷ []) (wp0314 c4) ▸
       at 5 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 6 2 (CS23⁻ ∷ CCZ034 ∷ []) (wp0313 c4) ▸
       at 7 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 8 2 (CS13 ∷ CCZ034 ∷ []) (wp0312 c4) ▸
       at 4 5 (CCZ123 ∷ []) (sym (wl0207 (lit c4))) ▸ done

  b2 : Chain (X4 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ123 ∷ CCZ034 ∷ K3 ∷ CK43 ∷ S4 ∷ CCZ123 ∷ X4 ∷ CCZ123 ∷ []) (X4 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ123 ∷ K3 ∷ Toff304 ∷ CCZ034 ∷ CZ03 ∷ CK43 ∷ CZ03 ∷ S4 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CCZ034 ∷ CS13 ∷ X4 ∷ CCZ123 ∷ [])
  b2 = at 5 2 (K3 ∷ Toff304 ∷ CCZ034 ∷ CCZ034 ∷ []) (wp0979 c4) ▸
       at 8 2 (CZ03 ∷ CK43 ∷ CZ03 ∷ CCZ034 ∷ []) (wp0980 c4) ▸
       at 11 2 (S4 ∷ CCZ034 ∷ []) (wp0981 c4) ▸
       at 13 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0207 (lit c4)) ▸
       at 12 2 (CS23 ∷ CCZ034 ∷ []) (wp0314 c4) ▸
       at 13 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 14 2 (CS23⁻ ∷ CCZ034 ∷ []) (wp0313 c4) ▸
       at 15 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸ done

  b3 : Chain (X4 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ123 ∷ K3 ∷ Toff304 ∷ CCZ034 ∷ CZ03 ∷ CK43 ∷ CZ03 ∷ S4 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CCZ034 ∷ CS13 ∷ X4 ∷ CCZ123 ∷ []) (X4 ∷ Toff012 ∷ CCZ034 ∷ CCZ123 ∷ K3 ∷ CK43 ∷ S4 ∷ CCZ123 ∷ Toff012 ∷ CCZ034 ∷ X4 ∷ CCZ123 ∷ [])
  b3 = at 16 2 (CS13 ∷ CCZ034 ∷ []) (wp0312 c4) ▸
       at 12 5 (CCZ123 ∷ []) (sym (wl0207 (lit c4))) ▸
       at 5 7 (K3 ∷ CK43 ∷ S4 ∷ []) (sym (wp0982 c4)) ▸
       at 3 2 (CCZ123 ∷ Toff012 ∷ []) (sym (wl0464 (lit c4))) ▸
       at 4 2 (K3 ∷ Toff012 ∷ []) (c₃ (Toff) (K)) ▸
       at 5 2 (CK43 ∷ Toff012 ∷ []) (c₃ (Toff) (CK₁₀)) ▸
       at 6 2 (S4 ∷ Toff012 ∷ []) (c₃ (Toff) (S ↑)) ▸
       at 7 2 (CCZ123 ∷ Toff012 ∷ []) (sym (wl0464 (lit c4))) ▸ done

  b4 : Chain (X4 ∷ Toff012 ∷ CCZ034 ∷ CCZ123 ∷ K3 ∷ CK43 ∷ S4 ∷ CCZ123 ∷ Toff012 ∷ CCZ034 ∷ X4 ∷ CCZ123 ∷ []) (X4 ∷ Toff012 ∷ CCZ123 ∷ K3 ∷ Toff304 ∷ CCZ034 ∷ CCZ034 ∷ CK43 ∷ S4 ∷ CCZ123 ∷ Toff012 ∷ CCZ034 ∷ X4 ∷ CCZ123 ∷ [])
  b4 = at 3 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0207 (lit c4)) ▸
       at 2 2 (CS23 ∷ CCZ034 ∷ []) (wp0314 c4) ▸
       at 3 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 4 2 (CS23⁻ ∷ CCZ034 ∷ []) (wp0313 c4) ▸
       at 5 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 6 2 (CS13 ∷ CCZ034 ∷ []) (wp0312 c4) ▸
       at 2 5 (CCZ123 ∷ []) (sym (wl0207 (lit c4))) ▸
       at 3 2 (K3 ∷ Toff304 ∷ CCZ034 ∷ CCZ034 ∷ []) (wp0979 c4) ▸ done

  b5 : Chain (X4 ∷ Toff012 ∷ CCZ123 ∷ K3 ∷ Toff304 ∷ CCZ034 ∷ CCZ034 ∷ CK43 ∷ S4 ∷ CCZ123 ∷ Toff012 ∷ CCZ034 ∷ X4 ∷ CCZ123 ∷ []) (X4 ∷ Toff012 ∷ CCZ123 ∷ K3 ∷ Toff304 ∷ CCZ034 ∷ CZ03 ∷ CK43 ∷ CZ03 ∷ S4 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ X4 ∷ CCZ123 ∷ [])
  b5 = at 6 2 (CZ03 ∷ CK43 ∷ CZ03 ∷ CCZ034 ∷ []) (wp0980 c4) ▸
       at 9 2 (S4 ∷ CCZ034 ∷ []) (wp0981 c4) ▸
       at 11 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0207 (lit c4)) ▸
       at 10 2 (CS23 ∷ CCZ034 ∷ []) (wp0314 c4) ▸
       at 11 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 12 2 (CS23⁻ ∷ CCZ034 ∷ []) (wp0313 c4) ▸
       at 13 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 14 2 (CS13 ∷ CCZ034 ∷ []) (wp0312 c4) ▸ done

  b6 : Chain (X4 ∷ Toff012 ∷ CCZ123 ∷ K3 ∷ Toff304 ∷ CCZ034 ∷ CZ03 ∷ CK43 ∷ CZ03 ∷ S4 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ X4 ∷ CCZ123 ∷ []) (X4 ∷ CCZ123 ∷ K3 ∷ CK43 ∷ S4 ∷ CCZ123 ∷ Bx0-1243 ∷ X4 ∷ CCZ123 ∷ [])
  b6 = at 10 5 (CCZ123 ∷ []) (sym (wl0207 (lit c4))) ▸
       at 3 7 (K3 ∷ CK43 ∷ S4 ∷ []) (sym (wp0982 c4)) ▸
       at 1 2 (CCZ123 ∷ Toff012 ∷ []) (sym (wl0464 (lit c4))) ▸
       at 2 2 (K3 ∷ Toff012 ∷ []) (c₃ (Toff) (K)) ▸
       at 3 2 (CK43 ∷ Toff012 ∷ []) (c₃ (Toff) (CK₁₀)) ▸
       at 4 2 (S4 ∷ Toff012 ∷ []) (c₃ (Toff) (S ↑)) ▸
       at 5 2 (CCZ123 ∷ Toff012 ∷ []) (sym (wl0464 (lit c4))) ▸
       at 6 4 (Bx0-1243 ∷ []) (sym (lem-box-tQ-at3443 c4)) ▸ done

  b7 : Chain (X4 ∷ CCZ123 ∷ K3 ∷ CK43 ∷ S4 ∷ CCZ123 ∷ Bx0-1243 ∷ X4 ∷ CCZ123 ∷ []) (CCZ123 ∷ CK43 ∷ CCZ123 ∷ Bx0-1243 ∷ [])
  b7 = at 6 1 (Bx0-1423 ∷ []) (sym (lem-box-perm-1324-at243243 c4)) ▸
       at 0 6 (CCZ123 ∷ CK43 ∷ CCZ123 ∷ X4 ∷ []) (sym (wl1173 (lit c4))) ▸
       at 3 3 (Bx0-1423 ∷ CCZ123 ∷ []) (lem-Xb-box-at243243 c4) ▸
       at 4 2 [] (wl0181 (lit c4)) ▸
       at 3 1 (Bx0-1243 ∷ []) (lem-box-perm-1324-at243243 c4) ▸ done


-- nf-rel-266@1: 154 steps
lem-nf-rel-266at1 : Ws → ⟪ (CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ Toff234 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ CCZ123 ∷ S4 ∷ Bx0-1423 ∷ []) ⟫ʷ
lem-nf-rel-266at1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (run b19)))))))))))))))))))
  where
  b0 : Chain (CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ []) (Toff324 ∷ Toff234 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ [])
  b0 = at 1 2 (CCZ234 ∷ []) (lem-S2-SBOX⟨0·2·43·1⟩ c4) ▸
       at 5 2 (CCZ234 ∷ []) (lem-S2-SBOX⟨0·2·43·1⟩ c4) ▸
       at 10 2 (CCZ234 ∷ []) (lem-S2-SBOX⟨0·2·43·1⟩ c4) ▸
       at 14 2 (CCZ234 ∷ []) (lem-S2-SBOX⟨0·2·43·1⟩ c4) ▸
       at 8 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 10 1 (CS13 ∷ []) (refl) ▸
       at 12 1 (CS13⁻ ∷ []) (refl) ▸
       at 0 8 (Toff324 ∷ Toff234 ∷ []) (wl1285 (lit c4)) ▸ done

  b1 : Chain (Toff324 ∷ Toff234 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ []) (Toff324 ∷ Toff234 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CCZ014 ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ [])
  b1 = at 2 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 5 2 (Toff024 ∷ Toff324 ∷ Toff023 ∷ []) (wp0805 c4) ▸
       at 4 2 (Toff024 ∷ CCZ124 ∷ CCZ014 ∷ []) (wp0806 c4) ▸
       at 7 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 6 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸
       at 7 2 (CS34 ∷ CCZ014 ∷ []) (wp0064 c4) ▸
       at 8 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 9 2 (CS34⁻ ∷ CCZ014 ∷ []) (wp0063 c4) ▸ done

  b2 : Chain (Toff324 ∷ Toff234 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CCZ014 ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ []) (Toff324 ∷ Toff234 ∷ CCZ014 ∷ Toff024 ∷ CS24 ∷ CX14 ∷ Toff023 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ [])
  b2 = at 10 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 11 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸
       at 12 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸
       at 6 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 3 2 (Toff024 ∷ Toff023 ∷ []) (wp0072 c4) ▸
       at 5 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 4 2 (CS24 ∷ Toff023 ∷ []) (sym (wp0070 c4)) ▸
       at 5 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸ done

  b3 : Chain (Toff324 ∷ Toff234 ∷ CCZ014 ∷ Toff024 ∷ CS24 ∷ CX14 ∷ Toff023 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ []) (Toff324 ∷ Toff234 ∷ CCZ124 ∷ CCZ014 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ [])
  b3 = at 6 2 (CS24⁻ ∷ Toff023 ∷ []) (sym (wp0069 c4)) ▸
       at 7 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 8 2 (CS12 ∷ Toff023 ∷ []) (sym (wl0221 (lit c4))) ▸
       at 4 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 5 2 (Toff024 ∷ Toff324 ∷ Toff023 ∷ []) (wp0805 c4) ▸
       at 3 3 (CCZ124 ∷ []) (sym (wp0074 c4)) ▸
       at 2 2 (CCZ124 ∷ CCZ014 ∷ []) (wp0066 c4) ▸
       at 4 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸ done

  b4 : Chain (Toff324 ∷ Toff234 ∷ CCZ124 ∷ CCZ014 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ []) (Toff324 ∷ Toff234 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ [])
  b4 = at 3 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸
       at 4 2 (CS34 ∷ CCZ014 ∷ []) (wp0064 c4) ▸
       at 5 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 6 2 (CS34⁻ ∷ CCZ014 ∷ []) (wp0063 c4) ▸
       at 7 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 8 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸
       at 9 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸
       at 3 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸ done

  b5 : Chain (Toff324 ∷ Toff234 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ []) (Toff324 ∷ Toff234 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ [])
  b5 = at 4 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 4 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 7 2 (CS13 ∷ Toff023 ∷ []) (sym (wl0222 (lit c4))) ▸
       at 6 2 (CS13 ∷ CCZ014 ∷ []) (wp0053 c4) ▸
       at 5 2 (CS13 ∷ Toff023 ∷ []) (sym (wl0222 (lit c4))) ▸
       at 4 2 (CS13 ∷ CCZ014 ∷ []) (wp0053 c4) ▸
       at 5 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 5 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸ done

  b6 : Chain (Toff324 ∷ Toff234 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ []) (Toff324 ∷ Toff234 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CCZ014 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ [])
  b6 = at 8 2 (Toff024 ∷ Toff324 ∷ Toff023 ∷ []) (wp0805 c4) ▸
       at 7 2 (Toff024 ∷ CCZ124 ∷ CCZ014 ∷ []) (wp0806 c4) ▸
       at 10 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 9 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸
       at 10 2 (CS34 ∷ CCZ014 ∷ []) (wp0064 c4) ▸
       at 11 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 12 2 (CS34⁻ ∷ CCZ014 ∷ []) (wp0063 c4) ▸
       at 13 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸ done

  b7 : Chain (Toff324 ∷ Toff234 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CCZ014 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ []) (Toff324 ∷ Toff234 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff024 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ Toff023 ∷ CX14 ∷ CS12 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ [])
  b7 = at 14 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸
       at 15 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸
       at 9 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 6 2 (Toff024 ∷ Toff023 ∷ []) (wp0072 c4) ▸
       at 8 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 7 2 (CS24 ∷ Toff023 ∷ []) (sym (wp0070 c4)) ▸
       at 8 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 9 2 (CS24⁻ ∷ Toff023 ∷ []) (sym (wp0069 c4)) ▸ done

  b8 : Chain (Toff324 ∷ Toff234 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff024 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ Toff023 ∷ CX14 ∷ CS12 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ []) (Toff324 ∷ Toff234 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ K3 ∷ CCZ014 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ [])
  b8 = at 10 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 11 2 (CS12 ∷ Toff023 ∷ []) (sym (wl0221 (lit c4))) ▸
       at 7 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 8 2 (Toff024 ∷ Toff324 ∷ Toff023 ∷ []) (wp0805 c4) ▸
       at 6 3 (CCZ124 ∷ []) (sym (wp0074 c4)) ▸
       at 5 2 (CCZ124 ∷ CCZ014 ∷ []) (wp0066 c4) ▸
       at 7 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 6 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸ done

  b9 : Chain (Toff324 ∷ Toff234 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ K3 ∷ CCZ014 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ []) (Toff324 ∷ Toff234 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ Bx0-1423 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ [])
  b9 = at 7 2 (CS34 ∷ CCZ014 ∷ []) (wp0064 c4) ▸
       at 8 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 9 2 (CS34⁻ ∷ CCZ014 ∷ []) (wp0063 c4) ▸
       at 10 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 11 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸
       at 12 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸
       at 6 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 7 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸ done

  b10 : Chain (Toff324 ∷ Toff234 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ Bx0-1423 ∷ CS13⁻ ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ []) (Toff324 ∷ Toff234 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ Bx0-1342 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ [])
  b10 = at 7 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 10 2 (CS13⁻ ∷ Toff023 ∷ []) (sym (wl0219 (lit c4))) ▸
       at 9 2 (CS13⁻ ∷ CCZ014 ∷ []) (wp0060 c4) ▸
       at 8 2 (CS13⁻ ∷ Toff023 ∷ []) (sym (wl0219 (lit c4))) ▸
       at 7 2 (CS13⁻ ∷ CCZ014 ∷ []) (wp0060 c4) ▸
       at 8 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 8 1 (Bx0-1342 ∷ []) (lem-box-perm-1423-at243243 c4) ▸
       at 8 2 (CCZ123 ∷ CK42 ∷ CCZ123 ∷ Bx0-1342 ∷ []) (lem-CKc-box-at233442 c4) ▸ done

  b11 : Chain (Toff324 ∷ Toff234 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ Bx0-1342 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ []) (Toff324 ∷ Toff234 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ014 ∷ Toff023 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CCZ014 ∷ CS24 ∷ Toff023 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ [])
  b11 = at 11 1 (Bx0-1423 ∷ []) (lem-box-perm-1342-at233442 c4) ▸
       at 11 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 14 2 (CCZ234 ∷ Toff023 ∷ []) (sym (wp0278 c4)) ▸
       at 14 1 (CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ []) (wl0274 (lit c4)) ▸
       at 13 2 (CS34 ∷ CCZ014 ∷ []) (wp0064 c4) ▸
       at 14 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 15 2 (CS34⁻ ∷ CCZ014 ∷ []) (wp0063 c4) ▸
       at 16 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸ done

  b12 : Chain (Toff324 ∷ Toff234 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ014 ∷ Toff023 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CCZ014 ∷ CS24 ∷ Toff023 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ []) (Toff324 ∷ Toff234 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CCZ014 ∷ CS24 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ [])
  b12 = at 17 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸
       at 13 5 (CCZ234 ∷ []) (sym (wl0274 (lit c4))) ▸
       at 12 2 (CCZ234 ∷ Toff023 ∷ []) (sym (wp0278 c4)) ▸
       at 12 1 (CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ []) (wl0274 (lit c4)) ▸
       at 11 2 (CS34 ∷ CCZ014 ∷ []) (wp0064 c4) ▸
       at 12 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 13 2 (CS34⁻ ∷ CCZ014 ∷ []) (wp0063 c4) ▸
       at 14 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸ done

  b13 : Chain (Toff324 ∷ Toff234 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CCZ014 ∷ CS24 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ []) (Toff324 ∷ Toff234 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ S4 ∷ Toff023 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ [])
  b13 = at 15 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸
       at 11 5 (CCZ234 ∷ []) (sym (wl0274 (lit c4))) ▸
       at 12 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 12 1 (Bx0-1342 ∷ []) (lem-box-perm-1423-at243243 c4) ▸
       at 12 2 (CCZ123 ∷ CK42 ∷ CCZ123 ∷ Bx0-1342 ∷ []) (lem-CKc-box-at233442 c4) ▸
       at 15 1 (Bx0-1423 ∷ []) (lem-box-perm-1342-at233442 c4) ▸
       at 15 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 18 2 (S4 ∷ Toff023 ∷ []) (sym (wp0632 c4)) ▸ done

  b14 : Chain (Toff324 ∷ Toff234 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ S4 ∷ Toff023 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ []) (Toff324 ∷ Toff234 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ [])
  b14 = at 17 2 (S4 ∷ CCZ014 ∷ []) (wp0633 c4) ▸
       at 16 2 (S4 ∷ Toff023 ∷ []) (sym (wp0632 c4)) ▸
       at 15 2 (S4 ∷ CCZ014 ∷ []) (wp0633 c4) ▸
       at 16 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 16 1 (Bx0-1243 ∷ []) (lem-box-perm-1324-at243243 c4) ▸
       at 16 2 (CCZ123 ∷ CK43 ∷ CCZ123 ∷ Bx0-1243 ∷ []) (lem-CKc-box-at3443 c4) ▸
       at 19 1 (Bx0-1423 ∷ []) (lem-box-perm-1324-at3443 c4) ▸
       at 19 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸ done

  b15 : Chain (Toff324 ∷ Toff234 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ234 ∷ CK43 ∷ S4 ∷ []) (Toff324 ∷ Toff234 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ014 ∷ Toff023 ∷ CCZ234 ∷ CCZ014 ∷ Toff023 ∷ CK43 ∷ S4 ∷ [])
  b15 = at 22 2 (CCZ234 ∷ Toff023 ∷ []) (sym (wp0278 c4)) ▸
       at 22 1 (CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ []) (wl0274 (lit c4)) ▸
       at 21 2 (CS34 ∷ CCZ014 ∷ []) (wp0064 c4) ▸
       at 22 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 23 2 (CS34⁻ ∷ CCZ014 ∷ []) (wp0063 c4) ▸
       at 24 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 25 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸
       at 21 5 (CCZ234 ∷ []) (sym (wl0274 (lit c4))) ▸ done

  b16 : Chain (Toff324 ∷ Toff234 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ014 ∷ Toff023 ∷ CCZ234 ∷ CCZ014 ∷ Toff023 ∷ CK43 ∷ S4 ∷ []) (Toff324 ∷ Toff234 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ234 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CK43 ∷ S4 ∷ [])
  b16 = at 20 2 (CCZ234 ∷ Toff023 ∷ []) (sym (wp0278 c4)) ▸
       at 20 1 (CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ []) (wl0274 (lit c4)) ▸
       at 19 2 (CS34 ∷ CCZ014 ∷ []) (wp0064 c4) ▸
       at 20 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 21 2 (CS34⁻ ∷ CCZ014 ∷ []) (wp0063 c4) ▸
       at 22 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 23 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸
       at 19 5 (CCZ234 ∷ []) (sym (wl0274 (lit c4))) ▸ done

  b17 : Chain (Toff324 ∷ Toff234 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ234 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CK43 ∷ S4 ∷ []) (Toff324 ∷ Toff234 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ014 ∷ S4 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ [])
  b17 = at 20 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 20 1 (Bx0-1243 ∷ []) (lem-box-perm-1324-at243243 c4) ▸
       at 20 2 (CCZ123 ∷ CK43 ∷ CCZ123 ∷ Bx0-1243 ∷ []) (lem-CKc-box-at3443 c4) ▸
       at 23 1 (Bx0-1423 ∷ []) (lem-box-perm-1324-at3443 c4) ▸
       at 23 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 26 2 (S4 ∷ Toff023 ∷ []) (sym (wp0632 c4)) ▸
       at 25 2 (S4 ∷ CCZ014 ∷ []) (wp0633 c4) ▸
       at 24 2 (S4 ∷ Toff023 ∷ []) (sym (wp0632 c4)) ▸ done

  b18 : Chain (Toff324 ∷ Toff234 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ014 ∷ S4 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (Toff324 ∷ Toff234 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ S4 ∷ Bx0-1423 ∷ [])
  b18 = at 23 2 (S4 ∷ CCZ014 ∷ []) (wp0633 c4) ▸
       at 24 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 2 3 (Toff324 ∷ CS13 ∷ CCZ124 ∷ []) (wl1000 (lit c4)) ▸
       at 4 2 [] (wl0263 (lit c4)) ▸
       at 8 2 (CCZ234 ∷ CCZ123 ∷ []) (wl0508 (lit c4)) ▸
       at 9 2 [] (wl0181 (lit c4)) ▸
       at 10 2 (S4 ∷ CCZ123 ∷ []) (wl1286 (lit c4)) ▸
       at 11 2 [] (wl0181 (lit c4)) ▸ done

  b19 : Chain (Toff324 ∷ Toff234 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ S4 ∷ Bx0-1423 ∷ []) (Toff324 ∷ Toff234 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ CCZ123 ∷ S4 ∷ Bx0-1423 ∷ [])
  b19 = at 12 2 (CCZ234 ∷ CCZ123 ∷ []) (wl0508 (lit c4)) ▸
       at 13 2 [] (wl0181 (lit c4)) ▸ done


-- F1-rel-266@1: 157 steps
lem-F1-rel-266at1 : Ws → ⟪ (CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ []) ⟫ʷ
lem-F1-rel-266at1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (run b19)))))))))))))))))))
  where
  b0 : Chain (CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ []) (Toff124 ∷ Toff214 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ [])
  b0 = at 1 2 (CCZ124 ∷ []) (lem-S2-SBOX⟨0·1·42·3⟩ c4) ▸
       at 5 2 (CCZ124 ∷ []) (lem-S2-SBOX⟨0·1·42·3⟩ c4) ▸
       at 10 2 (CCZ124 ∷ []) (lem-S2-SBOX⟨0·1·42·3⟩ c4) ▸
       at 14 2 (CCZ124 ∷ []) (lem-S2-SBOX⟨0·1·42·3⟩ c4) ▸
       at 8 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 10 1 (CS12 ∷ []) (refl) ▸
       at 12 1 (CS12⁻ ∷ []) (refl) ▸
       at 0 8 (Toff124 ∷ Toff214 ∷ []) (wl1287 (lit c4)) ▸ done

  b1 : Chain (Toff124 ∷ Toff214 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ []) (Toff124 ∷ Toff214 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CCZ024 ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ [])
  b1 = at 2 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 5 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp0843 c4) ▸
       at 4 2 (Toff034 ∷ CCZ234 ∷ CCZ024 ∷ []) (wp0845 c4) ▸
       at 7 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 6 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸
       at 7 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 8 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 9 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸ done

  b2 : Chain (Toff124 ∷ Toff214 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CCZ024 ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ []) (Toff124 ∷ Toff214 ∷ CCZ024 ∷ Toff034 ∷ CS34 ∷ CX24 ∷ Toff013 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ [])
  b2 = at 10 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 11 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 12 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 6 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 3 2 (Toff034 ∷ Toff013 ∷ []) (wp0097 c4) ▸
       at 5 1 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (wl0245 (lit c4)) ▸
       at 4 2 (CS34 ∷ Toff013 ∷ []) (sym (wp0095 c4)) ▸
       at 5 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸ done

  b3 : Chain (Toff124 ∷ Toff214 ∷ CCZ024 ∷ Toff034 ∷ CS34 ∷ CX24 ∷ Toff013 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ []) (Toff124 ∷ Toff214 ∷ CCZ234 ∷ CCZ024 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ [])
  b3 = at 6 2 (CS34⁻ ∷ Toff013 ∷ []) (sym (wp0094 c4)) ▸
       at 7 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 8 2 (CS23 ∷ Toff013 ∷ []) (sym (wl0246 (lit c4))) ▸
       at 4 5 (CCZ234 ∷ []) (sym (wl0245 (lit c4))) ▸
       at 5 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp0843 c4) ▸
       at 3 3 (CCZ234 ∷ []) (sym (wp0842 c4)) ▸
       at 2 2 (CCZ234 ∷ CCZ024 ∷ []) (wp0090 c4) ▸
       at 4 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸ done

  b4 : Chain (Toff124 ∷ Toff214 ∷ CCZ234 ∷ CCZ024 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ []) (Toff124 ∷ Toff214 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ [])
  b4 = at 3 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸
       at 4 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 5 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 6 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 7 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 8 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 9 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 3 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸ done

  b5 : Chain (Toff124 ∷ Toff214 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ []) (Toff124 ∷ Toff214 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12⁻ ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ [])
  b5 = at 4 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 4 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 7 2 (CS12 ∷ Toff013 ∷ []) (sym (wl0247 (lit c4))) ▸
       at 6 2 (CS12 ∷ CCZ024 ∷ []) (wp0081 c4) ▸
       at 5 2 (CS12 ∷ Toff013 ∷ []) (sym (wl0247 (lit c4))) ▸
       at 4 2 (CS12 ∷ CCZ024 ∷ []) (wp0081 c4) ▸
       at 5 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 5 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸ done

  b6 : Chain (Toff124 ∷ Toff214 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12⁻ ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ []) (Toff124 ∷ Toff214 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CS12⁻ ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ [])
  b6 = at 8 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp0843 c4) ▸
       at 7 2 (Toff034 ∷ CCZ234 ∷ CCZ024 ∷ []) (wp0845 c4) ▸
       at 10 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 9 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸
       at 10 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 11 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 12 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 13 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸ done

  b7 : Chain (Toff124 ∷ Toff214 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CS12⁻ ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ []) (Toff124 ∷ Toff214 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff034 ∷ CS34 ∷ CX24 ∷ CS34⁻ ∷ Toff013 ∷ CX24 ∷ CS23 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ [])
  b7 = at 14 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 15 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 9 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 6 2 (Toff034 ∷ Toff013 ∷ []) (wp0097 c4) ▸
       at 8 1 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (wl0245 (lit c4)) ▸
       at 7 2 (CS34 ∷ Toff013 ∷ []) (sym (wp0095 c4)) ▸
       at 8 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 9 2 (CS34⁻ ∷ Toff013 ∷ []) (sym (wp0094 c4)) ▸ done

  b8 : Chain (Toff124 ∷ Toff214 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff034 ∷ CS34 ∷ CX24 ∷ CS34⁻ ∷ Toff013 ∷ CX24 ∷ CS23 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ []) (Toff124 ∷ Toff214 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ K1 ∷ CCZ024 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ [])
  b8 = at 10 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 11 2 (CS23 ∷ Toff013 ∷ []) (sym (wl0246 (lit c4))) ▸
       at 7 5 (CCZ234 ∷ []) (sym (wl0245 (lit c4))) ▸
       at 8 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp0843 c4) ▸
       at 6 3 (CCZ234 ∷ []) (sym (wp0842 c4)) ▸
       at 5 2 (CCZ234 ∷ CCZ024 ∷ []) (wp0090 c4) ▸
       at 7 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 6 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸ done

  b9 : Chain (Toff124 ∷ Toff214 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ K1 ∷ CCZ024 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ []) (Toff124 ∷ Toff214 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ Bx0-2431 ∷ CS12⁻ ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ [])
  b9 = at 7 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 8 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 9 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 10 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 11 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 12 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 6 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 7 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸ done

  b10 : Chain (Toff124 ∷ Toff214 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ Bx0-2431 ∷ CS12⁻ ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ []) (Toff124 ∷ Toff214 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ Bx0-3142 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ [])
  b10 = at 7 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 10 2 (CS12⁻ ∷ Toff013 ∷ []) (sym (wl0244 (lit c4))) ▸
       at 9 2 (CS12⁻ ∷ CCZ024 ∷ []) (wp0087 c4) ▸
       at 8 2 (CS12⁻ ∷ Toff013 ∷ []) (sym (wl0244 (lit c4))) ▸
       at 7 2 (CS12⁻ ∷ CCZ024 ∷ []) (wp0087 c4) ▸
       at 8 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 8 1 (Bx0-3142 ∷ []) (lem-box-perm-3421-at122441 c4) ▸
       at 8 2 (CCZ123 ∷ CK42 ∷ CCZ123 ∷ Bx0-3142 ∷ []) (lem-CKc-box-at13213442 c4) ▸ done

  b11 : Chain (Toff124 ∷ Toff214 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ Bx0-3142 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ []) (Toff124 ∷ Toff214 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ Toff013 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ [])
  b11 = at 11 1 (Bx0-2431 ∷ []) (lem-box-perm-4312-at13213442 c4) ▸
       at 11 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 15 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 14 2 (CS24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CS24 (lit c4)) ▸
       at 15 2 (CX12 ∷ Toff013 ∷ []) (sym (wl0872 (lit c4))) ▸
       at 16 2 (CS24⁻ ∷ Toff013 ∷ []) (lem-comm-TOFF013-CSd24 (lit c4)) ▸
       at 17 2 (CX12 ∷ Toff013 ∷ []) (sym (wl0872 (lit c4))) ▸
       at 18 2 (CS14 ∷ Toff013 ∷ []) (sym (wp0785 c4)) ▸ done

  b12 : Chain (Toff124 ∷ Toff214 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ Toff013 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ []) (Toff124 ∷ Toff214 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ024 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ [])
  b12 = at 14 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 13 2 (CCZ124 ∷ CCZ024 ∷ []) (wp0827 c4) ▸
       at 13 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 12 2 (CS24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CS24 (lit c4)) ▸
       at 13 2 (CX12 ∷ Toff013 ∷ []) (sym (wl0872 (lit c4))) ▸
       at 14 2 (CS24⁻ ∷ Toff013 ∷ []) (lem-comm-TOFF013-CSd24 (lit c4)) ▸
       at 15 2 (CX12 ∷ Toff013 ∷ []) (sym (wl0872 (lit c4))) ▸
       at 16 2 (CS14 ∷ Toff013 ∷ []) (sym (wp0785 c4)) ▸ done

  b13 : Chain (Toff124 ∷ Toff214 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ024 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ []) (Toff124 ∷ Toff214 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ124 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ S4 ∷ Toff013 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ [])
  b13 = at 12 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 11 2 (CCZ124 ∷ CCZ024 ∷ []) (wp0827 c4) ▸
       at 12 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 12 1 (Bx0-3142 ∷ []) (lem-box-perm-3421-at122441 c4) ▸
       at 12 2 (CCZ123 ∷ CK42 ∷ CCZ123 ∷ Bx0-3142 ∷ []) (lem-CKc-box-at13213442 c4) ▸
       at 15 1 (Bx0-2431 ∷ []) (lem-box-perm-4312-at13213442 c4) ▸
       at 15 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 18 2 (S4 ∷ Toff013 ∷ []) (sym (wp0647 c4)) ▸ done

  b14 : Chain (Toff124 ∷ Toff214 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ124 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ S4 ∷ Toff013 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ []) (Toff124 ∷ Toff214 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ124 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ123 ∷ CK41 ∷ CCZ123 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ [])
  b14 = at 17 2 (S4 ∷ CCZ024 ∷ []) (wp0617 c4) ▸
       at 16 2 (S4 ∷ Toff013 ∷ []) (sym (wp0647 c4)) ▸
       at 15 2 (S4 ∷ CCZ024 ∷ []) (wp0617 c4) ▸
       at 16 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 16 1 (Bx0-2341 ∷ []) (lem-box-perm-1324-at122441 c4) ▸
       at 16 2 (CCZ123 ∷ CK41 ∷ CCZ123 ∷ Bx0-2341 ∷ []) (lem-CKc-box-at12233441 c4) ▸
       at 19 1 (Bx0-2431 ∷ []) (lem-box-perm-1324-at12233441 c4) ▸
       at 19 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸ done

  b15 : Chain (Toff124 ∷ Toff214 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ124 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ123 ∷ CK41 ∷ CCZ123 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ []) (Toff124 ∷ Toff214 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ124 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ123 ∷ CK41 ∷ CCZ123 ∷ CCZ024 ∷ Toff013 ∷ CCZ124 ∷ CCZ024 ∷ Toff013 ∷ CK41 ∷ S4 ∷ [])
  b15 = at 23 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 22 2 (CS24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CS24 (lit c4)) ▸
       at 23 2 (CX12 ∷ Toff013 ∷ []) (sym (wl0872 (lit c4))) ▸
       at 24 2 (CS24⁻ ∷ Toff013 ∷ []) (lem-comm-TOFF013-CSd24 (lit c4)) ▸
       at 25 2 (CX12 ∷ Toff013 ∷ []) (sym (wl0872 (lit c4))) ▸
       at 26 2 (CS14 ∷ Toff013 ∷ []) (sym (wp0785 c4)) ▸
       at 22 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 21 2 (CCZ124 ∷ CCZ024 ∷ []) (wp0827 c4) ▸ done

  b16 : Chain (Toff124 ∷ Toff214 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ124 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ123 ∷ CK41 ∷ CCZ123 ∷ CCZ024 ∷ Toff013 ∷ CCZ124 ∷ CCZ024 ∷ Toff013 ∷ CK41 ∷ S4 ∷ []) (Toff124 ∷ Toff214 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ124 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ123 ∷ CK41 ∷ CCZ123 ∷ CCZ124 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CK41 ∷ S4 ∷ [])
  b16 = at 21 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 20 2 (CS24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CS24 (lit c4)) ▸
       at 21 2 (CX12 ∷ Toff013 ∷ []) (sym (wl0872 (lit c4))) ▸
       at 22 2 (CS24⁻ ∷ Toff013 ∷ []) (lem-comm-TOFF013-CSd24 (lit c4)) ▸
       at 23 2 (CX12 ∷ Toff013 ∷ []) (sym (wl0872 (lit c4))) ▸
       at 24 2 (CS14 ∷ Toff013 ∷ []) (sym (wp0785 c4)) ▸
       at 20 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 19 2 (CCZ124 ∷ CCZ024 ∷ []) (wp0827 c4) ▸ done

  b17 : Chain (Toff124 ∷ Toff214 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ124 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ123 ∷ CK41 ∷ CCZ123 ∷ CCZ124 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CK41 ∷ S4 ∷ []) (Toff124 ∷ Toff214 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ124 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ123 ∷ CK41 ∷ CCZ123 ∷ CCZ124 ∷ CCZ123 ∷ CK41 ∷ CCZ123 ∷ CCZ024 ∷ S4 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ [])
  b17 = at 20 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 20 1 (Bx0-2341 ∷ []) (lem-box-perm-1324-at122441 c4) ▸
       at 20 2 (CCZ123 ∷ CK41 ∷ CCZ123 ∷ Bx0-2341 ∷ []) (lem-CKc-box-at12233441 c4) ▸
       at 23 1 (Bx0-2431 ∷ []) (lem-box-perm-1324-at12233441 c4) ▸
       at 23 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 26 2 (S4 ∷ Toff013 ∷ []) (sym (wp0647 c4)) ▸
       at 25 2 (S4 ∷ CCZ024 ∷ []) (wp0617 c4) ▸
       at 24 2 (S4 ∷ Toff013 ∷ []) (sym (wp0647 c4)) ▸ done

  b18 : Chain (Toff124 ∷ Toff214 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ124 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CCZ123 ∷ CK41 ∷ CCZ123 ∷ CCZ124 ∷ CCZ123 ∷ CK41 ∷ CCZ123 ∷ CCZ024 ∷ S4 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (Toff124 ∷ Toff214 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ123 ∷ CCZ124 ∷ CCZ123 ∷ CK41 ∷ CCZ123 ∷ S4 ∷ Bx0-2431 ∷ [])
  b18 = at 23 2 (S4 ∷ CCZ024 ∷ []) (wp0617 c4) ▸
       at 24 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 2 3 (Toff134 ∷ CS12 ∷ CCZ234 ∷ []) (wl1037 (lit c4)) ▸
       at 4 2 [] (wl0305 (lit c4)) ▸
       at 8 2 (CCZ124 ∷ CCZ123 ∷ []) (wl0770 (lit c4)) ▸
       at 9 2 [] (wl0181 (lit c4)) ▸
       at 10 2 (S4 ∷ CCZ123 ∷ []) (wl1286 (lit c4)) ▸
       at 11 2 [] (wl0181 (lit c4)) ▸ done

  b19 : Chain (Toff124 ∷ Toff214 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ123 ∷ CCZ124 ∷ CCZ123 ∷ CK41 ∷ CCZ123 ∷ S4 ∷ Bx0-2431 ∷ []) (CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ [])
  b19 = at 12 2 (CCZ124 ∷ CCZ123 ∷ []) (wl0770 (lit c4)) ▸
       at 13 2 [] (wl0181 (lit c4)) ▸
       at 16 1 (Bx0-1423 ∷ []) (lem-box-perm-4213-at122441 c4) ▸
       at 0 16 (Toff324 ∷ Toff234 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CK43 ∷ CCZ234 ∷ CK43 ∷ CCZ123 ∷ S4 ∷ []) (wl1288 (lit c4)) ▸
       at 0 17 (CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ []) (sym (lem-nf-rel-266at1 c4)) ▸ done


-- nf-rel-267@0: 13 steps
lem-nf-rel-267at0 : Ws → ⟪ (CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ []) ⟫ʷ
lem-nf-rel-267at0 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ []) (CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ [])
  b0 = at 1 1 (Sb3-0-41-2 ∷ []) (lem-F0-at14213243 c4) ▸
       at 2 1 (Sb3-0-41-2 ∷ []) (lem-F0-at14213243 c4) ▸
       at 5 1 (Sb3-1-42-0 ∷ []) (lem-F0-at01143043 c4) ▸
       at 6 1 (Sb3-1-42-0 ∷ []) (lem-F0-at01143043 c4) ▸
       at 8 1 (Sb3-0-41-2 ∷ []) (lem-F0-at14213243 c4) ▸
       at 9 1 (Sb3-0-41-2 ∷ []) (lem-F0-at14213243 c4) ▸
       at 12 1 (Sb3-1-42-0 ∷ []) (lem-F0-at01143043 c4) ▸
       at 13 1 (Sb3-1-42-0 ∷ []) (lem-F0-at01143043 c4) ▸ done

  b1 : Chain (CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ []) (CCZ024 ∷ [])
  b1 = at 1 2 (CCZ014 ∷ []) (lem-S2-SBOX⟨3·0·41·2⟩ c4) ▸
       at 4 2 (CCZ124 ∷ []) (lem-S2-SBOX⟨3·1·42·0⟩ c4) ▸
       at 6 2 (CCZ014 ∷ []) (lem-S2-SBOX⟨3·0·41·2⟩ c4) ▸
       at 9 2 (CCZ124 ∷ []) (lem-S2-SBOX⟨3·1·42·0⟩ c4) ▸
       at 0 10 (CCZ024 ∷ []) (sym (wp1118 c4)) ▸ done


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


-- nf-rel-267@1: 5 steps
lem-nf-rel-267at1 : Ws → ⟪ (CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ []) ⟫ʷ
lem-nf-rel-267at1 c4 = run b0
  where
  b0 : Chain (CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ []) (CCZ134 ∷ [])
  b0 = at 1 2 (CCZ124 ∷ []) (lem-S2-SBOX⟨0·1·42·3⟩ c4) ▸
       at 4 2 (CCZ234 ∷ []) (lem-S2-SBOX⟨0·2·43·1⟩ c4) ▸
       at 6 2 (CCZ124 ∷ []) (lem-S2-SBOX⟨0·1·42·3⟩ c4) ▸
       at 9 2 (CCZ234 ∷ []) (lem-S2-SBOX⟨0·2·43·1⟩ c4) ▸
       at 0 10 (CCZ134 ∷ []) (sym (wl1289 (lit c4))) ▸ done


-- F1-rel-267@1: 8 steps
lem-F1-rel-267at1 : Ws → ⟪ (CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-F1-rel-267at1 c4 = run b0
  where
  b0 : Chain (CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ []) (CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ [])
  b0 = at 1 2 (CCZ124 ∷ []) (lem-S2-SBOX⟨0·1·42·3⟩ c4) ▸
       at 5 2 (CCZ124 ∷ []) (lem-S2-SBOX⟨0·1·42·3⟩ c4) ▸
       at 8 2 (CCZ234 ∷ []) (lem-S2-SBOX⟨0·2·43·1⟩ c4) ▸
       at 10 2 (CCZ124 ∷ []) (lem-S2-SBOX⟨0·1·42·3⟩ c4) ▸
       at 14 2 (CCZ124 ∷ []) (lem-S2-SBOX⟨0·1·42·3⟩ c4) ▸
       at 0 17 (CCZ134 ∷ []) (sym (wl1290 (lit c4))) ▸
       at 0 1 (CCZ134 ∷ []) (wl1291 (lit c4)) ▸
       at 0 1 (CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ []) (sym (lem-nf-rel-267at1 c4)) ▸ done

