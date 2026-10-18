{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D022 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0171 ; wl0172 ; wl0173 ; wl0181 ; wl0184 ; wl0217 ; wl0219 ; wl0220 ; wl0221 ; wl0222 ; wl0241 ; wl0244 ; wl0245 ; wl0246 ; wl0247 ; wl0256 ; wl0263 ; wl0298 ; wl0300 ; wl0302 ; wl0305 ; wl0306 ; wl0316 ; wl0318 ; wl0321 ; wl0322 ; wl0341 ; wl0348 ; wl0391 ; wl0392 ; wl0393 ; wl0405 ; wl0406 ; wl0414 ; wl0415 ; wl0424 ; wl0432 ; wl0433 ; wl0436 ; wl0441 ; wl0450 ; wl0458 ; wl0487 ; wl0488 ; wl0489 ; wl0490 ; wl0491 ; wl0492 ; wl0503 ; wl0508 ; wl0512 ; wl0519 ; wl0520 ; wl0618 ; wl0621 ; wl0694 ; wl0695 ; wl0720 ; wl0763 ; wl0764 ; wl0765 ; wl0774 ; wl0781 ; wl0782 ; wl0783 ; wl0784 ; wl0785 ; wl0786 ; wl0787 ; wl0788 ; wl0790 ; wl0872 ; wl0907 ; wl0910 ; wl1037 ; wl1155 ; wl1189 ; wl1190 ; wl1220 ; wl1221 ; wl1223 ; wl1224 ; wl1234 ; wl1235 ; wl1236 ; wl1237 ; wl1238 ; wl1239 ; wl1240 ; wl1241 ; wl1242 ; wl1243 ; wl1244 ; wl1245 ; wl1246 ; wl1247 ; wl1248 ; wl1249 ; wl1250 ; wl1251 ; wl1252 ; wl1253 ; wl1254 ; wl1255 ; wl1256 ; wl1257 ; wl1258 ; wl1259 ; wl1260 ; wp0001 ; wp0013 ; wp0034 ; wp0035 ; wp0036 ; wp0041 ; wp0053 ; wp0060 ; wp0061 ; wp0062 ; wp0063 ; wp0064 ; wp0065 ; wp0066 ; wp0069 ; wp0070 ; wp0072 ; wp0074 ; wp0081 ; wp0087 ; wp0088 ; wp0089 ; wp0090 ; wp0094 ; wp0095 ; wp0097 ; wp0135 ; wp0149 ; wp0151 ; wp0161 ; wp0170 ; wp0175 ; wp0176 ; wp0177 ; wp0178 ; wp0261 ; wp0269 ; wp0272 ; wp0273 ; wp0274 ; wp0279 ; wp0285 ; wp0288 ; wp0289 ; wp0294 ; wp0333 ; wp0343 ; wp0347 ; wp0348 ; wp0349 ; wp0350 ; wp0351 ; wp0352 ; wp0353 ; wp0354 ; wp0513 ; wp0546 ; wp0669 ; wp0688 ; wp0692 ; wp0703 ; wp0706 ; wp0727 ; wp0728 ; wp0729 ; wp0730 ; wp0731 ; wp0785 ; wp0796 ; wp0797 ; wp0798 ; wp0805 ; wp0806 ; wp0816 ; wp0817 ; wp0818 ; wp0819 ; wp0820 ; wp0821 ; wp0827 ; wp0839 ; wp0842 ; wp0843 ; wp0845 ; wp1003 ; wp1004 ; wp1005 ; wp1006 ; wp1007 ; wp1008 ; wp1019 ; wp1021 ; wp1022 ; wp1023 ; wp1024 ; wp1026 ; wp1027 ; wp1032 ; wp1042 ; wp1046 ; wp1047 ; wp1048 ; wp1049 ; wp1050 ; wp1051 ; wp1052 ; wp1053 ; wp1054 ; wp1055 ; wp1056 ; wp1057 ; wp1058 ; wp1059 ; wp1060 ; wp1061 ; wp1062 ; wp1063 ; wp1064 ; wp1065 ; wp1066 ; wp1067 ; wp1068 ; wp1069 ; wp1070 ; wp1071 ; wp1072 ; wp1073)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-box-cP-at122441 ; lem-box-cP-at243243 ; lem-box2-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-box-tQ-at0310243142 ; lem-sym-ab-at0310243142)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-sym-ab-at0314203142)
open import Examples.Groups.Clifford+CS.Five.D.D006 using (lem-box-cP-at12233441 ; lem-box-perm-1324-at122441)
open import Examples.Groups.Clifford+CS.Five.D.D008 using (lem-box-tQ-at0314213042 ; lem-sym-bc-at0314203142 ; lem-sym-bc-at0314213042 ; lem-tP-at0314213042)
open import Examples.Groups.Clifford+CS.Five.D.D009 using (lem-box-cP-at0314213042)
open import Examples.Groups.Clifford+CS.Five.D.D012 using (lem-box-perm-4213-at122441)
open import Examples.Groups.Clifford+CS.Five.D.D020 using (lem-box-cP-at03243240 ; lem-box2-at03243240)
open import Examples.Groups.Clifford+CS.Five.D.D021 using (lem-nf-comm-CSu-CSat1)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CX04-CCZ123 ; lem-comm-CZ04-CCZ123)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-TOFF013-CSd24)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-CS12-CCZ034 ; lem-comm-CS24-TOFF301 ; lem-comm-CSd04-TOFF312 ; lem-comm-CSd12-CCZ034 ; lem-comm-CSd12-TOFF304 ; lem-comm-CSd24-TOFF301 ; lem-comm-CX02-CCZ134 ; lem-comm-TOFF304-CSd12)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-comm-CCZ024-CX13 ; lem-comm-CS12-TOFF304 ; lem-comm-CSd02-TOFF314 ; lem-comm-CSd14-TOFF302 ; lem-comm-CZ02-TOFF314 ; lem-comm-CZ14-TOFF302)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-comm-CCZ014-CX23 ; lem-comm-CCZ023-CX14 ; lem-comm-CCZ024-CS13 ; lem-comm-CCZ024-CSd13 ; lem-comm-CCZ134-CX02 ; lem-comm-CS14-TOFF302 ; lem-comm-CX14-TOFF302 ; lem-comm-CZ02-CCZ134 ; lem-comm-SWAP14-BOX⟨3·02⟩ ; lem-comm-TOFF013-CS24 ; lem-comm-TOFF013-CX24 ; lem-comm-TOFF014-CX23 ; lem-comm-TOFF023-CX14 ; lem-comm-TOFF302-CK41 ; lem-comm-TOFF302-CSd14)
-- F1-comm-CSu-CS@1: 288 steps
lem-F1-comm-CSu-CSat1 : Ws → ⟪ (Sb0-2-43-1 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-F1-comm-CSu-CSat1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (run b35)))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (Sb0-2-43-1 ∷ Sb0-1-42-3 ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff024 ∷ Toff324 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b0 = at 0 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 2 1 (CS12 ∷ []) (refl) ▸
       at 4 1 (CS12⁻ ∷ []) (refl) ▸
       at 5 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 7 1 (CS13 ∷ []) (refl) ▸
       at 9 1 (CS13⁻ ∷ []) (refl) ▸
       at 5 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 8 2 (Toff024 ∷ Toff324 ∷ Toff023 ∷ []) (wp0805 c4) ▸ done

  b1 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff024 ∷ Toff324 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ CCZ014 ∷ K3⁻ ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b1 = at 7 2 (Toff024 ∷ CCZ124 ∷ CCZ014 ∷ []) (wp0806 c4) ▸
       at 10 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 9 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸
       at 10 2 (CS34 ∷ CCZ014 ∷ []) (wp0064 c4) ▸
       at 11 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 12 2 (CS34⁻ ∷ CCZ014 ∷ []) (wp0063 c4) ▸
       at 13 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 14 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸ done

  b2 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ CCZ014 ∷ K3⁻ ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CCZ014 ∷ Toff024 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ Toff023 ∷ CS12 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b2 = at 15 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸
       at 9 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 6 2 (Toff024 ∷ Toff023 ∷ []) (wp0072 c4) ▸
       at 8 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 7 2 (CS24 ∷ Toff023 ∷ []) (sym (wp0070 c4)) ▸
       at 8 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 9 2 (CS24⁻ ∷ Toff023 ∷ []) (sym (wp0069 c4)) ▸
       at 10 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸ done

  b3 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CCZ014 ∷ Toff024 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ Toff023 ∷ CS12 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CCZ014 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b3 = at 11 2 (CS12 ∷ Toff023 ∷ []) (sym (wl0221 (lit c4))) ▸
       at 7 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 8 2 (Toff024 ∷ Toff324 ∷ Toff023 ∷ []) (wp0805 c4) ▸
       at 6 3 (CCZ124 ∷ []) (sym (wp0074 c4)) ▸
       at 5 2 (CCZ124 ∷ CCZ014 ∷ []) (wp0066 c4) ▸
       at 7 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 6 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸
       at 7 2 (CS34 ∷ CCZ014 ∷ []) (wp0064 c4) ▸ done

  b4 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CCZ014 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b4 = at 8 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 9 2 (CS34⁻ ∷ CCZ014 ∷ []) (wp0063 c4) ▸
       at 10 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 11 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸
       at 12 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸
       at 6 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 7 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 7 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸ done

  b5 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ124 ∷ CCZ014 ∷ Toff324 ∷ Toff023 ∷ CS13⁻ ∷ [])
  b5 = at 10 2 (CS13 ∷ Toff023 ∷ []) (sym (wl0222 (lit c4))) ▸
       at 9 2 (CS13 ∷ CCZ014 ∷ []) (wp0053 c4) ▸
       at 8 2 (CS13 ∷ Toff023 ∷ []) (sym (wl0222 (lit c4))) ▸
       at 7 2 (CS13 ∷ CCZ014 ∷ []) (wp0053 c4) ▸
       at 8 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 8 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 11 2 (Toff024 ∷ Toff324 ∷ Toff023 ∷ []) (wp0805 c4) ▸
       at 10 2 (Toff024 ∷ CCZ124 ∷ CCZ014 ∷ []) (wp0806 c4) ▸ done

  b6 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ124 ∷ CCZ014 ∷ Toff324 ∷ Toff023 ∷ CS13⁻ ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ [])
  b6 = at 13 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 12 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸
       at 13 2 (CS34 ∷ CCZ014 ∷ []) (wp0064 c4) ▸
       at 14 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 15 2 (CS34⁻ ∷ CCZ014 ∷ []) (wp0063 c4) ▸
       at 16 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 17 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸
       at 18 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸ done

  b7 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff024 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ Toff023 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ [])
  b7 = at 12 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 9 2 (Toff024 ∷ Toff023 ∷ []) (wp0072 c4) ▸
       at 11 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 10 2 (CS24 ∷ Toff023 ∷ []) (sym (wp0070 c4)) ▸
       at 11 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 12 2 (CS24⁻ ∷ Toff023 ∷ []) (sym (wp0069 c4)) ▸
       at 13 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 14 2 (CS12 ∷ Toff023 ∷ []) (sym (wl0221 (lit c4))) ▸ done

  b8 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff024 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ Toff023 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CX23 ∷ CCZ014 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ [])
  b8 = at 10 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 11 2 (Toff024 ∷ Toff324 ∷ Toff023 ∷ []) (wp0805 c4) ▸
       at 9 3 (CCZ124 ∷ []) (sym (wp0074 c4)) ▸
       at 8 2 (CCZ124 ∷ CCZ014 ∷ []) (wp0066 c4) ▸
       at 10 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 9 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸
       at 10 2 (CS34 ∷ CCZ014 ∷ []) (wp0064 c4) ▸
       at 11 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸ done

  b9 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CX23 ∷ CCZ014 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ CS13⁻ ∷ Toff023 ∷ [])
  b9 = at 12 2 (CS34⁻ ∷ CCZ014 ∷ []) (wp0063 c4) ▸
       at 13 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 14 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸
       at 15 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸
       at 9 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 10 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 10 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 13 2 (CS13⁻ ∷ Toff023 ∷ []) (sym (wl0219 (lit c4))) ▸ done

  b10 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ CS13⁻ ∷ Toff023 ∷ []) (CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ CCZ024 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ Bx0-1423 ∷ [])
  b10 = at 12 2 (CS13⁻ ∷ CCZ014 ∷ []) (wp0060 c4) ▸
       at 11 2 (CS13⁻ ∷ Toff023 ∷ []) (sym (wl0219 (lit c4))) ▸
       at 10 2 (CS13⁻ ∷ CCZ014 ∷ []) (wp0060 c4) ▸
       at 11 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 0 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 3 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp0843 c4) ▸
       at 2 2 (Toff034 ∷ CCZ234 ∷ CCZ024 ∷ []) (wp0845 c4) ▸
       at 5 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸ done

  b11 : Chain (CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ CCZ024 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ Bx0-1423 ∷ []) (CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ Bx0-1423 ∷ [])
  b11 = at 4 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸
       at 5 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 6 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 7 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 8 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 9 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 10 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 4 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸ done

  b12 : Chain (CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ Bx0-1423 ∷ []) (CCZ024 ∷ Toff034 ∷ CCZ234 ∷ Toff013 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ Bx0-1423 ∷ [])
  b12 = at 1 2 (Toff034 ∷ Toff013 ∷ []) (wp0097 c4) ▸
       at 3 1 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (wl0245 (lit c4)) ▸
       at 2 2 (CS34 ∷ Toff013 ∷ []) (sym (wp0095 c4)) ▸
       at 3 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 4 2 (CS34⁻ ∷ Toff013 ∷ []) (sym (wp0094 c4)) ▸
       at 5 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 6 2 (CS23 ∷ Toff013 ∷ []) (sym (wl0246 (lit c4))) ▸
       at 2 5 (CCZ234 ∷ []) (sym (wl0245 (lit c4))) ▸ done

  b13 : Chain (CCZ024 ∷ Toff034 ∷ CCZ234 ∷ Toff013 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ Bx0-1423 ∷ []) (CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CCZ024 ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ Bx0-1423 ∷ [])
  b13 = at 3 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp0843 c4) ▸
       at 1 3 (CCZ234 ∷ []) (sym (wp0842 c4)) ▸
       at 0 2 (CCZ234 ∷ CCZ024 ∷ []) (wp0090 c4) ▸
       at 2 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 1 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸
       at 2 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 3 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 4 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸ done

  b14 : Chain (CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CCZ024 ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ Bx0-1423 ∷ []) (CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12⁻ ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ Bx0-1423 ∷ [])
  b14 = at 5 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 6 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 7 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 1 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 2 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 2 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 5 2 (CS12 ∷ Toff013 ∷ []) (sym (wl0247 (lit c4))) ▸
       at 4 2 (CS12 ∷ CCZ024 ∷ []) (wp0081 c4) ▸ done

  b15 : Chain (CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12⁻ ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ Bx0-1423 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ K1 ∷ CCZ024 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CS12⁻ ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ Bx0-1423 ∷ [])
  b15 = at 3 2 (CS12 ∷ Toff013 ∷ []) (sym (wl0247 (lit c4))) ▸
       at 2 2 (CS12 ∷ CCZ024 ∷ []) (wp0081 c4) ▸
       at 3 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 3 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 6 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp0843 c4) ▸
       at 5 2 (Toff034 ∷ CCZ234 ∷ CCZ024 ∷ []) (wp0845 c4) ▸
       at 8 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 7 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸ done

  b16 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ K1 ∷ CCZ024 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CS12⁻ ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ Bx0-1423 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff034 ∷ Toff013 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ Bx0-1423 ∷ [])
  b16 = at 8 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 9 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 10 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 11 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 12 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 13 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 7 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 4 2 (Toff034 ∷ Toff013 ∷ []) (wp0097 c4) ▸ done

  b17 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff034 ∷ Toff013 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ Bx0-1423 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff034 ∷ CCZ234 ∷ Toff034 ∷ Toff134 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ Bx0-1423 ∷ [])
  b17 = at 6 1 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (wl0245 (lit c4)) ▸
       at 5 2 (CS34 ∷ Toff013 ∷ []) (sym (wp0095 c4)) ▸
       at 6 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 7 2 (CS34⁻ ∷ Toff013 ∷ []) (sym (wp0094 c4)) ▸
       at 8 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 9 2 (CS23 ∷ Toff013 ∷ []) (sym (wl0246 (lit c4))) ▸
       at 5 5 (CCZ234 ∷ []) (sym (wl0245 (lit c4))) ▸
       at 6 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp0843 c4) ▸ done

  b18 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff034 ∷ CCZ234 ∷ Toff034 ∷ Toff134 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ Bx0-1423 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ Bx0-1423 ∷ [])
  b18 = at 4 3 (CCZ234 ∷ []) (sym (wp0842 c4)) ▸
       at 3 2 (CCZ234 ∷ CCZ024 ∷ []) (wp0090 c4) ▸
       at 5 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 4 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸
       at 5 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 6 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 7 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 8 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸ done

  b19 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ Bx0-1423 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ CS12⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ Bx0-1423 ∷ [])
  b19 = at 9 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 10 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 4 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 5 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 5 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 8 2 (CS12⁻ ∷ Toff013 ∷ []) (sym (wl0244 (lit c4))) ▸
       at 7 2 (CS12⁻ ∷ CCZ024 ∷ []) (wp0087 c4) ▸
       at 6 2 (CS12⁻ ∷ Toff013 ∷ []) (sym (wl0244 (lit c4))) ▸ done

  b20 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ CS12⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ Bx0-1423 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ Toff013 ∷ CS14 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ Bx0-1423 ∷ [])
  b20 = at 5 2 (CS12⁻ ∷ CCZ024 ∷ []) (wp0087 c4) ▸
       at 6 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 6 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 10 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 9 2 (CS24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CS24 (lit c4)) ▸
       at 10 2 (CX12 ∷ Toff013 ∷ []) (sym (wl0872 (lit c4))) ▸
       at 11 2 (CS24⁻ ∷ Toff013 ∷ []) (lem-comm-TOFF013-CSd24 (lit c4)) ▸
       at 12 2 (CX12 ∷ Toff013 ∷ []) (sym (wl0872 (lit c4))) ▸ done

  b21 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ Toff013 ∷ CS14 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ Bx0-1423 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ024 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ Toff013 ∷ CS14 ∷ CCZ024 ∷ Toff013 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ Bx0-1423 ∷ [])
  b21 = at 13 2 (CS14 ∷ Toff013 ∷ []) (sym (wp0785 c4)) ▸
       at 9 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 8 2 (CCZ124 ∷ CCZ024 ∷ []) (wp0827 c4) ▸
       at 8 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 7 2 (CS24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CS24 (lit c4)) ▸
       at 8 2 (CX12 ∷ Toff013 ∷ []) (sym (wl0872 (lit c4))) ▸
       at 9 2 (CS24⁻ ∷ Toff013 ∷ []) (lem-comm-TOFF013-CSd24 (lit c4)) ▸
       at 10 2 (CX12 ∷ Toff013 ∷ []) (sym (wl0872 (lit c4))) ▸ done

  b22 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ024 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ Toff013 ∷ CS14 ∷ CCZ024 ∷ Toff013 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ Bx0-1423 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ124 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ K3 ∷ Toff014 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ Bx0-1423 ∷ [])
  b22 = at 11 2 (CS14 ∷ Toff013 ∷ []) (sym (wp0785 c4)) ▸
       at 7 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 6 2 (CCZ124 ∷ CCZ024 ∷ []) (wp0827 c4) ▸
       at 7 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 7 1 (Bx0-2341 ∷ []) (lem-box-perm-1324-at122441 c4) ▸
       at 7 1 (CCZ023 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ []) (lem-box-cP-at12233441 c4) ▸
       at 11 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 10 2 (K3 ∷ Toff014 ∷ []) (sym (wp0819 c4)) ▸ done

  b23 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ124 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ K3 ∷ Toff014 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ Bx0-1423 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ124 ∷ CCZ023 ∷ Toff014 ∷ Toff324 ∷ CCZ024 ∷ CCZ023 ∷ Toff014 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ Bx0-1423 ∷ [])
  b23 = at 11 2 (CS34 ∷ Toff014 ∷ []) (sym (wp0546 c4)) ▸
       at 12 2 (CX23 ∷ Toff014 ∷ []) (lem-comm-TOFF014-CX23 (lit c4)) ▸
       at 13 2 (CS34⁻ ∷ Toff014 ∷ []) (sym (wp0818 c4)) ▸
       at 14 2 (CX23 ∷ Toff014 ∷ []) (lem-comm-TOFF014-CX23 (lit c4)) ▸
       at 15 2 (CS24 ∷ Toff014 ∷ []) (sym (wp0817 c4)) ▸
       at 16 2 (K3⁻ ∷ Toff014 ∷ []) (sym (wp0816 c4)) ▸
       at 10 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 9 2 (Toff324 ∷ CCZ024 ∷ CCZ023 ∷ []) (wp1046 c4) ▸ done

  b24 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ124 ∷ CCZ023 ∷ Toff014 ∷ Toff324 ∷ CCZ024 ∷ CCZ023 ∷ Toff014 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ Bx0-1423 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ124 ∷ CCZ023 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff014 ∷ CCZ024 ∷ CCZ023 ∷ Toff014 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ Bx0-1423 ∷ [])
  b24 = at 9 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 8 2 (K3 ∷ Toff014 ∷ []) (sym (wp0819 c4)) ▸
       at 9 2 (CS34 ∷ Toff014 ∷ []) (sym (wp0546 c4)) ▸
       at 10 2 (CX23 ∷ Toff014 ∷ []) (lem-comm-TOFF014-CX23 (lit c4)) ▸
       at 11 2 (CS34⁻ ∷ Toff014 ∷ []) (sym (wp0818 c4)) ▸
       at 12 2 (CX23 ∷ Toff014 ∷ []) (lem-comm-TOFF014-CX23 (lit c4)) ▸
       at 13 2 (CS24 ∷ Toff014 ∷ []) (sym (wp0817 c4)) ▸
       at 14 2 (K3⁻ ∷ Toff014 ∷ []) (sym (wp0816 c4)) ▸ done

  b25 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ124 ∷ CCZ023 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff014 ∷ CCZ024 ∷ CCZ023 ∷ Toff014 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ Bx0-1423 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ024 ∷ CCZ024 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CCZ023 ∷ CX14 ∷ CS12 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ Bx0-1423 ∷ [])
  b25 = at 8 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 9 2 (CCZ024 ∷ CCZ124 ∷ Toff014 ∷ []) (sym (wp0839 c4)) ▸
       at 7 2 (Toff324 ∷ CCZ024 ∷ CCZ023 ∷ []) (wp1046 c4) ▸
       at 9 2 (CCZ024 ∷ CCZ023 ∷ []) (wp0669 c4) ▸
       at 11 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 10 2 (CS24 ∷ CCZ023 ∷ []) (wp0513 c4) ▸
       at 11 2 (CX14 ∷ CCZ023 ∷ []) (lem-comm-CCZ023-CX14 (lit c4)) ▸
       at 12 2 (CS24⁻ ∷ CCZ023 ∷ []) (wp0820 c4) ▸ done

  b26 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ024 ∷ CCZ024 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CCZ023 ∷ CX14 ∷ CS12 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ Bx0-1423 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ CS13 ∷ Toff013 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ Bx0-1423 ∷ [])
  b26 = at 13 2 (CX14 ∷ CCZ023 ∷ []) (lem-comm-CCZ023-CX14 (lit c4)) ▸
       at 14 2 (CS12 ∷ CCZ023 ∷ []) (wl0621 (lit c4)) ▸
       at 10 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 7 3 (Toff324 ∷ []) (wp0821 c4) ▸
       at 9 4 (Bx0-2341 ∷ []) (sym (lem-box-cP-at12233441 c4)) ▸
       at 9 1 (Bx0-2431 ∷ []) (sym (lem-box-perm-1324-at122441 c4)) ▸
       at 9 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 12 2 (CS13 ∷ Toff013 ∷ []) (sym (wl0910 (lit c4))) ▸ done

  b27 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ CS13 ∷ Toff013 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ Bx0-1423 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ CS24 ∷ CX12 ∷ Toff013 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ Toff324 ∷ CS13⁻ ∷ Bx0-1423 ∷ [])
  b27 = at 11 2 (CS13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CS13 (lit c4)) ▸
       at 10 2 (CS13 ∷ Toff013 ∷ []) (sym (wl0910 (lit c4))) ▸
       at 9 2 (CS13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CS13 (lit c4)) ▸
       at 10 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 10 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 14 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 13 2 (CS24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CS24 (lit c4)) ▸
       at 14 2 (CX12 ∷ Toff013 ∷ []) (sym (wl0872 (lit c4))) ▸ done

  b28 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ CS24 ∷ CX12 ∷ Toff013 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ Toff324 ∷ CS13⁻ ∷ Bx0-1423 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ CCZ024 ∷ CS24 ∷ CX12 ∷ Toff013 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ CCZ024 ∷ Toff013 ∷ Toff324 ∷ CS13⁻ ∷ Bx0-1423 ∷ [])
  b28 = at 15 2 (CS24⁻ ∷ Toff013 ∷ []) (lem-comm-TOFF013-CSd24 (lit c4)) ▸
       at 16 2 (CX12 ∷ Toff013 ∷ []) (sym (wl0872 (lit c4))) ▸
       at 17 2 (CS14 ∷ Toff013 ∷ []) (sym (wp0785 c4)) ▸
       at 13 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 12 2 (CCZ124 ∷ CCZ024 ∷ []) (wp0827 c4) ▸
       at 12 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 11 2 (CS24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CS24 (lit c4)) ▸
       at 12 2 (CX12 ∷ Toff013 ∷ []) (sym (wl0872 (lit c4))) ▸ done

  b29 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ CCZ024 ∷ CS24 ∷ CX12 ∷ Toff013 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ CCZ024 ∷ Toff013 ∷ Toff324 ∷ CS13⁻ ∷ Bx0-1423 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ Toff324 ∷ CS13⁻ ∷ Bx0-1423 ∷ [])
  b29 = at 13 2 (CS24⁻ ∷ Toff013 ∷ []) (lem-comm-TOFF013-CSd24 (lit c4)) ▸
       at 14 2 (CX12 ∷ Toff013 ∷ []) (sym (wl0872 (lit c4))) ▸
       at 15 2 (CS14 ∷ Toff013 ∷ []) (sym (wp0785 c4)) ▸
       at 11 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 10 2 (CCZ124 ∷ CCZ024 ∷ []) (wp0827 c4) ▸
       at 11 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 11 1 (Bx0-2341 ∷ []) (lem-box-perm-1324-at122441 c4) ▸
       at 11 1 (CCZ023 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ []) (lem-box-cP-at12233441 c4) ▸ done

  b30 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ Toff324 ∷ CS13⁻ ∷ Bx0-1423 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff014 ∷ CS13⁻ ∷ Bx0-1423 ∷ [])
  b30 = at 15 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 14 2 (K3 ∷ Toff014 ∷ []) (sym (wp0819 c4)) ▸
       at 15 2 (CS34 ∷ Toff014 ∷ []) (sym (wp0546 c4)) ▸
       at 16 2 (CX23 ∷ Toff014 ∷ []) (lem-comm-TOFF014-CX23 (lit c4)) ▸
       at 17 2 (CS34⁻ ∷ Toff014 ∷ []) (sym (wp0818 c4)) ▸
       at 18 2 (CX23 ∷ Toff014 ∷ []) (lem-comm-TOFF014-CX23 (lit c4)) ▸
       at 19 2 (CS24 ∷ Toff014 ∷ []) (sym (wp0817 c4)) ▸
       at 20 2 (K3⁻ ∷ Toff014 ∷ []) (sym (wp0816 c4)) ▸ done

  b31 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff014 ∷ CS13⁻ ∷ Bx0-1423 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ CCZ023 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ Toff014 ∷ CS24 ∷ K3⁻ ∷ CCZ024 ∷ CCZ023 ∷ Toff014 ∷ CS13⁻ ∷ Bx0-1423 ∷ [])
  b31 = at 14 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 13 2 (Toff324 ∷ CCZ024 ∷ CCZ023 ∷ []) (wp1046 c4) ▸
       at 13 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 12 2 (K3 ∷ Toff014 ∷ []) (sym (wp0819 c4)) ▸
       at 13 2 (CS34 ∷ Toff014 ∷ []) (sym (wp0546 c4)) ▸
       at 14 2 (CX23 ∷ Toff014 ∷ []) (lem-comm-TOFF014-CX23 (lit c4)) ▸
       at 15 2 (CS34⁻ ∷ Toff014 ∷ []) (sym (wp0818 c4)) ▸
       at 16 2 (CX23 ∷ Toff014 ∷ []) (lem-comm-TOFF014-CX23 (lit c4)) ▸ done

  b32 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ CCZ023 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ Toff014 ∷ CS24 ∷ K3⁻ ∷ CCZ024 ∷ CCZ023 ∷ Toff014 ∷ CS13⁻ ∷ Bx0-1423 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ024 ∷ CCZ024 ∷ CS24 ∷ CCZ023 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CS13⁻ ∷ Bx0-1423 ∷ [])
  b32 = at 17 2 (CS24 ∷ Toff014 ∷ []) (sym (wp0817 c4)) ▸
       at 18 2 (K3⁻ ∷ Toff014 ∷ []) (sym (wp0816 c4)) ▸
       at 12 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 13 2 (CCZ024 ∷ CCZ124 ∷ Toff014 ∷ []) (sym (wp0839 c4)) ▸
       at 11 2 (Toff324 ∷ CCZ024 ∷ CCZ023 ∷ []) (wp1046 c4) ▸
       at 13 2 (CCZ024 ∷ CCZ023 ∷ []) (wp0669 c4) ▸
       at 15 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 14 2 (CS24 ∷ CCZ023 ∷ []) (wp0513 c4) ▸ done

  b33 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ024 ∷ CCZ024 ∷ CS24 ∷ CCZ023 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CS13⁻ ∷ Bx0-1423 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ Bx0-2431 ∷ CS13⁻ ∷ Bx0-1423 ∷ [])
  b33 = at 15 2 (CX14 ∷ CCZ023 ∷ []) (lem-comm-CCZ023-CX14 (lit c4)) ▸
       at 16 2 (CS24⁻ ∷ CCZ023 ∷ []) (wp0820 c4) ▸
       at 17 2 (CX14 ∷ CCZ023 ∷ []) (lem-comm-CCZ023-CX14 (lit c4)) ▸
       at 18 2 (CS12 ∷ CCZ023 ∷ []) (wl0621 (lit c4)) ▸
       at 14 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 11 3 (Toff324 ∷ []) (wp0821 c4) ▸
       at 13 4 (Bx0-2341 ∷ []) (sym (lem-box-cP-at12233441 c4)) ▸
       at 13 1 (Bx0-2431 ∷ []) (sym (lem-box-perm-1324-at122441 c4)) ▸ done

  b34 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ Bx0-2431 ∷ CS13⁻ ∷ Bx0-1423 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ [])
  b34 = at 13 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 16 2 (CS13⁻ ∷ Toff013 ∷ []) (sym (wl0907 (lit c4))) ▸
       at 15 2 (CS13⁻ ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CSd13 (lit c4)) ▸
       at 14 2 (CS13⁻ ∷ Toff013 ∷ []) (sym (wl0907 (lit c4))) ▸
       at 13 2 (CS13⁻ ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CSd13 (lit c4)) ▸
       at 14 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 14 1 (Bx0-1423 ∷ []) (lem-box-perm-4213-at122441 c4) ▸
       at 14 2 [] (lem-box2-at243243 c4) ▸ done

  b35 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ []) (Sb0-1-42-3 ∷ Sb0-2-43-1 ∷ [])
  b35 = at 0 3 (Toff134 ∷ CS12 ∷ CCZ234 ∷ []) (wl1037 (lit c4)) ▸
       at 2 2 [] (wl0305 (lit c4)) ▸
       at 4 2 (Toff324 ∷ CCZ124 ∷ []) (wl0450 (lit c4)) ▸
       at 5 2 [] (wl0263 (lit c4)) ▸
       at 6 2 (Toff324 ∷ CCZ124 ∷ []) (wl0450 (lit c4)) ▸
       at 7 2 [] (wl0263 (lit c4)) ▸
       at 0 8 (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (wl1234 (lit c4)) ▸
       at 0 8 (Sb0-1-42-3 ∷ Sb0-2-43-1 ∷ []) (sym (lem-nf-comm-CSu-CSat1 c4)) ▸ done


-- S2-SBOX(3;1;42;0): 86 steps
lem-S2-SBOX⟨3·1·42·0⟩ : Ws → ⟪ (Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ []) ⟫ʷ
lem-S2-SBOX⟨3·1·42·0⟩ c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (run b10))))))))))
  where
  b0 : Chain (Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CCZ134 ∷ CS01⁻ ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ [])
  b0 = at 1 1 (Bx3-1420 ∷ Toff024 ∷ Sb3-1-0-2 ∷ Toff024 ∷ Sb⁻3-1-0-2 ∷ []) (refl) ▸
       at 3 1 (CS01 ∷ []) (refl) ▸
       at 5 1 (CS01⁻ ∷ []) (refl) ▸
       at 0 1 (Bx3-1420 ∷ Toff024 ∷ Sb3-1-0-2 ∷ Toff024 ∷ Sb⁻3-1-0-2 ∷ []) (refl) ▸
       at 2 1 (CS01 ∷ []) (refl) ▸
       at 4 1 (CS01⁻ ∷ []) (refl) ▸
       at 5 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at03243240 c4) ▸
       at 4 2 (CCZ134 ∷ CS01⁻ ∷ []) (sym (wp1027 c4)) ▸ done

  b1 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CCZ134 ∷ CS01⁻ ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CCZ134 ∷ CS04 ∷ K0⁻ ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CS01⁻ ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ [])
  b1 = at 5 2 (Toff302 ∷ CS01⁻ ∷ []) (wl1224 (lit c4)) ▸
       at 6 2 (CCZ134 ∷ CS01⁻ ∷ []) (sym (wp1027 c4)) ▸
       at 7 2 (Toff302 ∷ CS01⁻ ∷ []) (wl1224 (lit c4)) ▸
       at 4 4 (Bx3-1420 ∷ []) (sym (lem-box-cP-at03243240 c4)) ▸
       at 4 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at03243240 c4) ▸
       at 3 1 (K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ []) (sym (wp1026 c4)) ▸
       at 9 2 (CCZ134 ∷ K0⁻ ∷ []) (c₁ (K • iI) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑)) ▸
       at 8 2 (CCZ134 ∷ CS04 ∷ []) (sym (wp1003 c4)) ▸ done

  b2 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CCZ134 ∷ CS04 ∷ K0⁻ ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CS01⁻ ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ CCZ134 ∷ Toff302 ∷ Toff024 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff302 ∷ CS01⁻ ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ [])
  b2 = at 7 2 (CCZ134 ∷ CX02 ∷ []) (lem-comm-CX02-CCZ134 (lit c4)) ▸
       at 6 2 (CCZ134 ∷ CS24⁻ ∷ []) (sym (wl1221 (lit c4))) ▸
       at 5 2 (CCZ134 ∷ CX02 ∷ []) (lem-comm-CX02-CCZ134 (lit c4)) ▸
       at 4 2 (CCZ134 ∷ CS24 ∷ []) (sym (wl1220 (lit c4))) ▸
       at 3 2 (CCZ134 ∷ K0 ∷ []) (c₁ (K) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑)) ▸
       at 4 7 (Toff024 ∷ []) (wp1026 c4) ▸
       at 4 2 (Toff302 ∷ Toff024 ∷ Toff324 ∷ []) (wp1004 c4) ▸
       at 6 2 (CCZ134 ∷ Toff324 ∷ CCZ124 ∷ []) (sym (wl1189 (lit c4))) ▸ done

  b3 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ CCZ134 ∷ Toff302 ∷ Toff024 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff302 ∷ CS01⁻ ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ Toff324 ∷ CCZ124 ∷ Toff302 ∷ CS01⁻ ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ [])
  b3 = at 5 1 (K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ []) (sym (wp1026 c4)) ▸
       at 11 2 (CCZ134 ∷ K0⁻ ∷ []) (c₁ (K • iI) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑)) ▸
       at 10 2 (CCZ134 ∷ CS04 ∷ []) (sym (wp1003 c4)) ▸
       at 9 2 (CCZ134 ∷ CX02 ∷ []) (lem-comm-CX02-CCZ134 (lit c4)) ▸
       at 8 2 (CCZ134 ∷ CS24⁻ ∷ []) (sym (wl1221 (lit c4))) ▸
       at 7 2 (CCZ134 ∷ CX02 ∷ []) (lem-comm-CX02-CCZ134 (lit c4)) ▸
       at 6 2 (CCZ134 ∷ CS24 ∷ []) (sym (wl1220 (lit c4))) ▸
       at 5 2 (CCZ134 ∷ K0 ∷ []) (c₁ (K) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑)) ▸ done

  b4 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ Toff324 ∷ CCZ124 ∷ Toff302 ∷ CS01⁻ ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff024 ∷ Toff324 ∷ Toff302 ∷ CCZ124 ∷ CS01⁻ ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ [])
  b4 = at 6 7 (Toff024 ∷ []) (wp1026 c4) ▸
       at 8 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 12 2 (Toff302 ∷ CS12 ∷ []) (wl1190 (lit c4)) ▸
       at 11 2 (Toff302 ∷ CX14 ∷ []) (lem-comm-CX14-TOFF302 (lit c4)) ▸
       at 10 2 (Toff302 ∷ CS24⁻ ∷ []) (wp1005 c4) ▸
       at 9 2 (Toff302 ∷ CX14 ∷ []) (lem-comm-CX14-TOFF302 (lit c4)) ▸
       at 8 2 (Toff302 ∷ CS24 ∷ []) (wp1006 c4) ▸
       at 9 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸ done

  b5 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff024 ∷ Toff324 ∷ Toff302 ∷ CCZ124 ∷ CS01⁻ ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ []) (Bx3-1420 ∷ Toff024 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ CS01 ∷ Toff302 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ [])
  b5 = at 7 2 (Toff302 ∷ Toff324 ∷ []) (sym (wp1007 c4)) ▸
       at 6 2 (Toff302 ∷ Toff024 ∷ Toff324 ∷ []) (wp1004 c4) ▸
       at 7 3 (Toff024 ∷ []) (wp1008 c4) ▸
       at 3 4 (Bx3-1420 ∷ []) (sym (lem-box-cP-at03243240 c4)) ▸
       at 3 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at03243240 c4) ▸
       at 2 2 (CCZ134 ∷ CS01 ∷ []) (sym (wp0261 c4)) ▸
       at 3 2 (Toff302 ∷ CS01 ∷ []) (wl1223 (lit c4)) ▸
       at 4 2 (CCZ134 ∷ CS01 ∷ []) (sym (wp0261 c4)) ▸ done

  b6 : Chain (Bx3-1420 ∷ Toff024 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ CS01 ∷ Toff302 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ []) (Bx3-1420 ∷ K0 ∷ CS24 ∷ CX02 ∷ CCZ134 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ [])
  b6 = at 5 2 (Toff302 ∷ CS01 ∷ []) (wl1223 (lit c4)) ▸
       at 2 4 (Bx3-1420 ∷ []) (sym (lem-box-cP-at03243240 c4)) ▸
       at 2 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at03243240 c4) ▸
       at 1 1 (K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ []) (sym (wp1026 c4)) ▸
       at 7 2 (CCZ134 ∷ K0⁻ ∷ []) (c₁ (K • iI) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑)) ▸
       at 6 2 (CCZ134 ∷ CS04 ∷ []) (sym (wp1003 c4)) ▸
       at 5 2 (CCZ134 ∷ CX02 ∷ []) (lem-comm-CX02-CCZ134 (lit c4)) ▸
       at 4 2 (CCZ134 ∷ CS24⁻ ∷ []) (sym (wl1221 (lit c4))) ▸ done

  b7 : Chain (Bx3-1420 ∷ K0 ∷ CS24 ∷ CX02 ∷ CCZ134 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ []) (Bx3-1420 ∷ CCZ134 ∷ Toff302 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ CCZ134 ∷ K0⁻ ∷ Toff324 ∷ CCZ124 ∷ Toff302 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ [])
  b7 = at 3 2 (CCZ134 ∷ CX02 ∷ []) (lem-comm-CX02-CCZ134 (lit c4)) ▸
       at 2 2 (CCZ134 ∷ CS24 ∷ []) (sym (wl1220 (lit c4))) ▸
       at 1 2 (CCZ134 ∷ K0 ∷ []) (c₁ (K) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑)) ▸
       at 2 7 (Toff024 ∷ []) (wp1026 c4) ▸
       at 2 2 (Toff302 ∷ Toff024 ∷ Toff324 ∷ []) (wp1004 c4) ▸
       at 4 2 (CCZ134 ∷ Toff324 ∷ CCZ124 ∷ []) (sym (wl1189 (lit c4))) ▸
       at 3 1 (K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ []) (sym (wp1026 c4)) ▸
       at 9 2 (CCZ134 ∷ K0⁻ ∷ []) (c₁ (K • iI) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑)) ▸ done

  b8 : Chain (Bx3-1420 ∷ CCZ134 ∷ Toff302 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ CCZ134 ∷ K0⁻ ∷ Toff324 ∷ CCZ124 ∷ Toff302 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ []) (Bx3-1420 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff024 ∷ Toff324 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ Toff302 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ [])
  b8 = at 8 2 (CCZ134 ∷ CS04 ∷ []) (sym (wp1003 c4)) ▸
       at 7 2 (CCZ134 ∷ CX02 ∷ []) (lem-comm-CX02-CCZ134 (lit c4)) ▸
       at 6 2 (CCZ134 ∷ CS24⁻ ∷ []) (sym (wl1221 (lit c4))) ▸
       at 5 2 (CCZ134 ∷ CX02 ∷ []) (lem-comm-CX02-CCZ134 (lit c4)) ▸
       at 4 2 (CCZ134 ∷ CS24 ∷ []) (sym (wl1220 (lit c4))) ▸
       at 3 2 (CCZ134 ∷ K0 ∷ []) (c₁ (K) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑)) ▸
       at 4 7 (Toff024 ∷ []) (wp1026 c4) ▸
       at 6 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸ done

  b9 : Chain (Bx3-1420 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff024 ∷ Toff324 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ Toff302 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ []) (Bx3-1420 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ Toff024 ∷ Toff324 ∷ Toff324 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ [])
  b9 = at 10 2 (Toff302 ∷ CS12 ∷ []) (wl1190 (lit c4)) ▸
       at 9 2 (Toff302 ∷ CX14 ∷ []) (lem-comm-CX14-TOFF302 (lit c4)) ▸
       at 8 2 (Toff302 ∷ CS24⁻ ∷ []) (wp1005 c4) ▸
       at 7 2 (Toff302 ∷ CX14 ∷ []) (lem-comm-CX14-TOFF302 (lit c4)) ▸
       at 6 2 (Toff302 ∷ CS24 ∷ []) (wp1006 c4) ▸
       at 7 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 5 2 (Toff302 ∷ Toff324 ∷ []) (sym (wp1007 c4)) ▸
       at 4 2 (Toff302 ∷ Toff024 ∷ Toff324 ∷ []) (wp1004 c4) ▸ done

  b10 : Chain (Bx3-1420 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ Toff024 ∷ Toff324 ∷ Toff324 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ []) (CCZ124 ∷ [])
  b10 = at 5 3 (Toff024 ∷ []) (wp1008 c4) ▸
       at 1 4 (Bx3-1420 ∷ []) (sym (lem-box-cP-at03243240 c4)) ▸
       at 0 2 [] (lem-box2-at03243240 c4) ▸
       at 1 3 (CS01 ∷ Toff024 ∷ CCZ124 ∷ []) (wp1042 c4) ▸
       at 3 2 [] (wl0263 (lit c4)) ▸
       at 0 8 (CCZ124 ∷ []) (sym (wp1047 c4)) ▸ done


-- P-box @0314213042: 8 steps
lem-P-box-at0314213042 : Ws → ⟪ (Toff302 ∷ Bx3-4102 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4102 ∷ []) ⟫ʷ
lem-P-box-at0314213042 c4 = run b0
  where
  b0 : Chain (Toff302 ∷ Bx3-4102 ∷ Toff302 ∷ []) (Bx3-4102 ∷ [])
  b0 = at 1 1 (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ []) (lem-box-tQ-at0314213042 c4) ▸
       at 0 2 (Toff314 ∷ Toff302 ∷ []) (sym (lem-tP-at0314213042 c4)) ▸
       at 1 2 (CCZ023 ∷ CZ02 ∷ Toff302 ∷ []) (sym (wl1235 (lit c4))) ▸
       at 3 2 (Toff314 ∷ Toff302 ∷ []) (sym (lem-tP-at0314213042 c4)) ▸
       at 4 3 (CCZ023 ∷ CZ02 ∷ []) (sym (wl1236 (lit c4))) ▸
       at 2 2 (Toff314 ∷ CZ02 ∷ []) (lem-comm-CZ02-TOFF314 (lit c4)) ▸
       at 3 3 (CCZ023 ∷ []) (sym (wl0774 (lit c4))) ▸
       at 0 4 (Bx3-4102 ∷ []) (sym (lem-box-tQ-at0314213042 c4)) ▸ done


-- cQ @03103441: 7 steps
lem-cQ-at03103441 : Ws → ⟪ (CCZ023 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ CCZ023 ∷ []) ⟫ʷ
lem-cQ-at03103441 c4 = run b0
  where
  b0 : Chain (CCZ023 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ023 ∷ [])
  b0 = at 0 1 (CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ []) (wl0458 (lit c4)) ▸
       at 4 2 (CCZ134 ∷ CS03 ∷ []) (sym (wp0706 c4)) ▸
       at 3 2 (CCZ134 ∷ CX02 ∷ []) (lem-comm-CX02-CCZ134 (lit c4)) ▸
       at 2 2 (CCZ134 ∷ CS23⁻ ∷ []) (sym (wl1237 (lit c4))) ▸
       at 1 2 (CCZ134 ∷ CX02 ∷ []) (lem-comm-CX02-CCZ134 (lit c4)) ▸
       at 0 2 (CCZ134 ∷ CS23 ∷ []) (sym (wl0790 (lit c4))) ▸
       at 1 5 (CCZ023 ∷ []) (sym (wl0458 (lit c4))) ▸ done


-- box-tQ @03103441: 13 steps
lem-box-tQ-at03103441 : Ws → ⟪ (Bx3-0241 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ []) ⟫ʷ
lem-box-tQ-at03103441 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-0241 ∷ []) (CCZ023 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ023 ∷ CCZ034 ∷ Toff034 ∷ CZ01 ∷ Toff034 ∷ CCZ034 ∷ CZ01 ∷ [])
  b0 = at 0 1 (CCZ023 ∷ Toff302 ∷ Bx0-341 ∷ Toff302 ∷ CCZ023 ∷ Bx0-341 ∷ []) (refl) ▸
       at 2 1 (CCZ034 ∷ Toff034 ∷ Bx3-01 ∷ Toff034 ∷ CCZ034 ∷ Bx3-01 ∷ []) (refl) ▸
       at 4 1 (CZ01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 2 6 (CCZ134 ∷ []) (wp1048 c4) ▸
       at 5 1 (CCZ034 ∷ Toff034 ∷ Bx3-01 ∷ Toff034 ∷ CCZ034 ∷ Bx3-01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 10 1 (CZ01 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ023 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ023 ∷ CCZ034 ∷ Toff034 ∷ CZ01 ∷ Toff034 ∷ CCZ034 ∷ CZ01 ∷ []) (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ [])
  b1 = at 5 6 (CCZ134 ∷ []) (wp1048 c4) ▸
       at 0 2 (Toff302 ∷ CCZ023 ∷ CZ02 ∷ []) (wl1238 (lit c4)) ▸
       at 2 2 (CCZ134 ∷ CZ02 ∷ []) (lem-comm-CZ02-CCZ134 (lit c4)) ▸
       at 1 2 (CCZ134 ∷ CCZ023 ∷ []) (lem-cQ-at03103441 c4) ▸
       at 2 4 (Toff302 ∷ []) (wl1239 (lit c4)) ▸ done


-- pairs @0314213042: 4 steps
lem-pairs-at0314213042 : Ws → ⟪ (Bx3-4102 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0241 ∷ []) ⟫ʷ
lem-pairs-at0314213042 c4 = run b0
  where
  b0 : Chain (Bx3-4102 ∷ []) (Bx3-0241 ∷ [])
  b0 = at 0 1 (Toff302 ∷ Bx3-4102 ∷ Toff302 ∷ []) (sym (lem-P-box-at0314213042 c4)) ▸
       at 1 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at0314213042 c4) ▸
       at 4 2 [] (wl0787 (lit c4)) ▸
       at 0 4 (Bx3-0241 ∷ []) (sym (lem-box-tQ-at03103441 c4)) ▸ done


-- box-perm-1423 @0310243142: 3 steps
lem-box-perm-1423-at0310243142 : Ws → ⟪ (Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0241 ∷ []) ⟫ʷ
lem-box-perm-1423-at0310243142 c4 = run b0
  where
  b0 : Chain (Bx3-0412 ∷ []) (Bx3-0241 ∷ [])
  b0 = at 0 1 (Bx3-4012 ∷ []) (lem-sym-ab-at0310243142 c4) ▸
       at 0 1 (Bx3-4102 ∷ []) (lem-sym-bc-at0314203142 c4) ▸
       at 0 1 (Bx3-0241 ∷ []) (lem-pairs-at0314213042 c4) ▸ done


-- CXbc-box @03103441: 17 steps
lem-CXbc-box-at03103441 : Ws → ⟪ (CX24 ∷ Bx3-0241 ∷ CX24 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0241 ∷ CCZ012 ∷ []) ⟫ʷ
lem-CXbc-box-at03103441 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX24 ∷ Bx3-0241 ∷ CX24 ∷ []) (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CX24 ∷ CCZ123 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CCZ134 ∷ CX02 ∷ CS01 ∷ CX24 ∷ [])
  b0 = at 1 1 (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ []) (lem-box-tQ-at03103441 c4) ▸
       at 0 2 (Toff302 ∷ CX24 ∷ []) (wp1049 c4) ▸
       at 1 2 (CCZ134 ∷ CX24 ∷ CCZ123 ∷ []) (sym (wl1240 (lit c4))) ▸
       at 3 2 (Toff302 ∷ CCZ123 ∷ CCZ012 ∷ []) (wl1241 (lit c4)) ▸
       at 2 2 (Toff302 ∷ CX24 ∷ []) (wp1049 c4) ▸
       at 5 1 (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ []) (wl0391 (lit c4)) ▸
       at 9 2 (CCZ134 ∷ CS01 ∷ []) (sym (wp0261 c4)) ▸
       at 8 2 (CCZ134 ∷ CX02 ∷ []) (lem-comm-CX02-CCZ134 (lit c4)) ▸ done

  b1 : Chain (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CX24 ∷ CCZ123 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CCZ134 ∷ CX02 ∷ CS01 ∷ CX24 ∷ []) (Bx3-0241 ∷ CX24 ∷ CCZ012 ∷ CX24 ∷ [])
  b1 = at 7 2 (CCZ134 ∷ CS12⁻ ∷ []) (sym (wl0392 (lit c4))) ▸
       at 6 2 (CCZ134 ∷ CX02 ∷ []) (lem-comm-CX02-CCZ134 (lit c4)) ▸
       at 5 2 (CCZ134 ∷ CS12 ∷ []) (sym (wl0393 (lit c4))) ▸
       at 6 5 (CCZ012 ∷ []) (sym (wl0391 (lit c4))) ▸
       at 4 2 (CCZ134 ∷ CCZ123 ∷ []) (wl0618 (lit c4)) ▸
       at 3 2 (CCZ134 ∷ CX24 ∷ CCZ123 ∷ []) (sym (wl1240 (lit c4))) ▸
       at 4 3 (CX24 ∷ []) (wl1242 (lit c4)) ▸
       at 0 4 (Bx3-0241 ∷ []) (sym (lem-box-tQ-at03103441 c4)) ▸ done

  b2 : Chain (Bx3-0241 ∷ CX24 ∷ CCZ012 ∷ CX24 ∷ []) (Bx3-0241 ∷ CCZ012 ∷ [])
  b2 = at 1 3 (CCZ012 ∷ []) (sym (wp1019 c4)) ▸ done


-- CXcb-box @03103441: 18 steps
lem-CXcb-box-at03103441 : Ws → ⟪ (CX42 ∷ Bx3-0241 ∷ CX42 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0241 ∷ CCZ014 ∷ []) ⟫ʷ
lem-CXcb-box-at03103441 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX42 ∷ Bx3-0241 ∷ CX42 ∷ []) (Toff302 ∷ CCZ134 ∷ CX42 ∷ Toff304 ∷ CS14 ∷ CX04 ∷ Toff302 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ CCZ134 ∷ CX42 ∷ [])
  b0 = at 1 1 (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ []) (lem-box-tQ-at03103441 c4) ▸
       at 0 2 (Toff302 ∷ CX42 ∷ Toff304 ∷ []) (wp1050 c4) ▸
       at 2 2 (CCZ134 ∷ Toff304 ∷ CCZ014 ∷ []) (sym (wp1051 c4)) ▸
       at 1 2 (CCZ134 ∷ CX42 ∷ []) (sym (wl0318 (lit c4))) ▸
       at 4 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4) ▸
       at 8 2 (Toff302 ∷ CS01 ∷ []) (wl1223 (lit c4)) ▸
       at 7 2 (Toff302 ∷ CX04 ∷ []) (wp1052 c4) ▸
       at 6 2 (Toff302 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-TOFF302 (lit c4)) ▸ done

  b1 : Chain (Toff302 ∷ CCZ134 ∷ CX42 ∷ Toff304 ∷ CS14 ∷ CX04 ∷ Toff302 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ CCZ134 ∷ CX42 ∷ []) (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ CX42 ∷ CCZ014 ∷ CX42 ∷ [])
  b1 = at 5 2 (Toff302 ∷ CX04 ∷ []) (wp1052 c4) ▸
       at 4 2 (Toff302 ∷ CS14 ∷ []) (lem-comm-CS14-TOFF302 (lit c4)) ▸
       at 5 5 (CCZ014 ∷ []) (sym (wp0041 c4)) ▸
       at 3 2 (Toff302 ∷ Toff304 ∷ []) (sym (wp1053 c4)) ▸
       at 2 2 (Toff302 ∷ CX42 ∷ Toff304 ∷ []) (wp1050 c4) ▸
       at 3 3 (CX42 ∷ []) (wp1054 c4) ▸
       at 4 2 (CCZ134 ∷ CCZ014 ∷ []) (wp0272 c4) ▸
       at 3 2 (CCZ134 ∷ CX42 ∷ []) (sym (wl0318 (lit c4))) ▸ done

  b2 : Chain (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ CX42 ∷ CCZ014 ∷ CX42 ∷ []) (Bx3-0241 ∷ CCZ014 ∷ [])
  b2 = at 0 4 (Bx3-0241 ∷ []) (sym (lem-box-tQ-at03103441 c4)) ▸
       at 1 3 (CCZ014 ∷ []) (sym (wp1021 c4)) ▸ done


-- SWbc-box @03103441: 11 steps
lem-SWbc-box-at03103441 : Ws → ⟪ (Sw24 ∷ Bx3-0241 ∷ Sw24 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0241 ∷ []) ⟫ʷ
lem-SWbc-box-at03103441 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw24 ∷ Bx3-0241 ∷ Sw24 ∷ []) (CX24 ∷ Bx3-0241 ∷ CX24 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ [])
  b0 = at 0 1 (CX24 ∷ CX42 ∷ CX24 ∷ []) (sym (wl0405 (lit c4))) ▸
       at 4 1 (CX24 ∷ CX42 ∷ CX24 ∷ []) (sym (wl0405 (lit c4))) ▸
       at 2 3 (Bx3-0241 ∷ CCZ012 ∷ []) (lem-CXbc-box-at03103441 c4) ▸
       at 3 2 (CX42 ∷ CCZ014 ∷ CCZ012 ∷ []) (wp1022 c4) ▸
       at 1 3 (Bx3-0241 ∷ CCZ014 ∷ []) (lem-CXcb-box-at03103441 c4) ▸
       at 4 2 (CX24 ∷ CCZ012 ∷ []) (wp0170 c4) ▸
       at 3 2 (CX24 ∷ CCZ012 ∷ CCZ014 ∷ []) (wp1023 c4) ▸
       at 2 2 (CX24 ∷ CCZ012 ∷ CCZ014 ∷ []) (wp1023 c4) ▸ done

  b1 : Chain (CX24 ∷ Bx3-0241 ∷ CX24 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ []) (Bx3-0241 ∷ [])
  b1 = at 3 5 (CCZ012 ∷ []) (wp1024 c4) ▸
       at 0 3 (Bx3-0241 ∷ CCZ012 ∷ []) (lem-CXbc-box-at03103441 c4) ▸
       at 1 2 [] (wl0341 (lit c4)) ▸ done


-- nat-SWbc @03103441: 23 steps
lem-nat-SWbc-at03103441 : Ws → ⟪ (Sw24 ∷ Bx3-0241 ∷ Sw24 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0421 ∷ []) ⟫ʷ
lem-nat-SWbc-at03103441 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw24 ∷ Bx3-0241 ∷ Sw24 ∷ []) (CCZ034 ∷ Toff304 ∷ CCZ023 ∷ Toff023 ∷ Bx3-01 ∷ Toff023 ∷ Sw24 ∷ CCZ034 ∷ Bx3-01 ∷ Toff302 ∷ CCZ023 ∷ Bx0-341 ∷ Sw24 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff302 ∷ Bx0-341 ∷ Toff302 ∷ CCZ023 ∷ Bx0-341 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw24 ∷ []) (sym (wp0177 c4)) ▸
       at 1 2 (Toff304 ∷ Sw24 ∷ []) (wp0178 c4) ▸
       at 3 1 (CCZ034 ∷ Toff034 ∷ Bx3-01 ∷ Toff034 ∷ CCZ034 ∷ Bx3-01 ∷ []) (refl) ▸
       at 2 2 (CCZ023 ∷ Sw24 ∷ []) (sym (wp0175 c4)) ▸
       at 3 2 (Toff023 ∷ Sw24 ∷ []) (wp0176 c4) ▸
       at 4 2 (Bx3-01 ∷ Sw24 ∷ []) (sym (c₂ (CZ) (Swap ↑ • Swap • Swap ↑))) ▸
       at 5 2 (Toff023 ∷ Sw24 ∷ []) (wp0176 c4) ▸ done

  b1 : Chain (CCZ034 ∷ Toff304 ∷ CCZ023 ∷ Toff023 ∷ Bx3-01 ∷ Toff023 ∷ Sw24 ∷ CCZ034 ∷ Bx3-01 ∷ Toff302 ∷ CCZ023 ∷ Bx0-341 ∷ Sw24 ∷ []) (CCZ034 ∷ Toff304 ∷ CCZ023 ∷ Toff023 ∷ Bx3-01 ∷ Toff023 ∷ CCZ023 ∷ Bx3-01 ∷ Toff304 ∷ CCZ034 ∷ CCZ023 ∷ Toff023 ∷ Bx3-01 ∷ Sw24 ∷ Toff034 ∷ CCZ034 ∷ Bx3-01 ∷ Sw24 ∷ [])
  b1 = at 6 2 (CCZ023 ∷ Sw24 ∷ []) (sym (wp0175 c4)) ▸
       at 7 2 (Bx3-01 ∷ Sw24 ∷ []) (sym (c₂ (CZ) (Swap ↑ • Swap • Swap ↑))) ▸
       at 8 2 (Toff304 ∷ Sw24 ∷ []) (wp0178 c4) ▸
       at 9 2 (CCZ034 ∷ Sw24 ∷ []) (sym (wp0177 c4)) ▸
       at 11 1 (CCZ034 ∷ Toff034 ∷ Bx3-01 ∷ Toff034 ∷ CCZ034 ∷ Bx3-01 ∷ []) (refl) ▸
       at 10 2 (CCZ023 ∷ Sw24 ∷ []) (sym (wp0175 c4)) ▸
       at 11 2 (Toff023 ∷ Sw24 ∷ []) (wp0176 c4) ▸
       at 12 2 (Bx3-01 ∷ Sw24 ∷ []) (sym (c₂ (CZ) (Swap ↑ • Swap • Swap ↑))) ▸ done

  b2 : Chain (CCZ034 ∷ Toff304 ∷ CCZ023 ∷ Toff023 ∷ Bx3-01 ∷ Toff023 ∷ CCZ023 ∷ Bx3-01 ∷ Toff304 ∷ CCZ034 ∷ CCZ023 ∷ Toff023 ∷ Bx3-01 ∷ Sw24 ∷ Toff034 ∷ CCZ034 ∷ Bx3-01 ∷ Sw24 ∷ []) (Bx3-0421 ∷ [])
  b2 = at 13 2 (Toff023 ∷ Sw24 ∷ []) (wp0176 c4) ▸
       at 14 2 (CCZ023 ∷ Sw24 ∷ []) (sym (wp0175 c4)) ▸
       at 15 2 (Bx3-01 ∷ Sw24 ∷ []) (sym (c₂ (CZ) (Swap ↑ • Swap • Swap ↑))) ▸
       at 16 2 [] (wl0322 (lit c4)) ▸
       at 2 6 (Bx0-321 ∷ []) (refl) ▸
       at 5 6 (Bx0-321 ∷ []) (refl) ▸
       at 0 6 (Bx3-0421 ∷ []) (refl) ▸ done


-- sym-bc @03103441: 2 steps
lem-sym-bc-at03103441 : Ws → ⟪ (Bx3-0241 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0421 ∷ []) ⟫ʷ
lem-sym-bc-at03103441 c4 = run b0
  where
  b0 : Chain (Bx3-0241 ∷ []) (Bx3-0421 ∷ [])
  b0 = at 0 1 (Sw24 ∷ Bx3-0241 ∷ Sw24 ∷ []) (sym (lem-SWbc-box-at03103441 c4)) ▸
       at 0 3 (Bx3-0421 ∷ []) (lem-nat-SWbc-at03103441 c4) ▸ done


-- box-perm-1324 @03103441: 1 steps
lem-box-perm-1324-at03103441 : Ws → ⟪ (Bx3-0241 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0421 ∷ []) ⟫ʷ
lem-box-perm-1324-at03103441 c4 = run b0
  where
  b0 : Chain (Bx3-0241 ∷ []) (Bx3-0421 ∷ [])
  b0 = at 0 1 (Bx3-0421 ∷ []) (lem-sym-bc-at03103441 c4) ▸ done


-- cQ @0310243241: 7 steps
lem-cQ-at0310243241 : Ws → ⟪ (CCZ034 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CCZ034 ∷ []) ⟫ʷ
lem-cQ-at0310243241 c4 = run b0
  where
  b0 : Chain (CCZ034 ∷ CCZ123 ∷ []) (CCZ123 ∷ CCZ034 ∷ [])
  b0 = at 0 1 (CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ []) (wp0352 c4) ▸
       at 4 2 (CCZ123 ∷ CS03 ∷ []) (sym (wl0490 (lit c4))) ▸
       at 3 2 (CCZ123 ∷ CX04 ∷ []) (lem-comm-CX04-CCZ123 (lit c4)) ▸
       at 2 2 (CCZ123 ∷ CS34⁻ ∷ []) (sym (wl0491 (lit c4))) ▸
       at 1 2 (CCZ123 ∷ CX04 ∷ []) (lem-comm-CX04-CCZ123 (lit c4)) ▸
       at 0 2 (CCZ123 ∷ CS34 ∷ []) (sym (wl0492 (lit c4))) ▸
       at 1 5 (CCZ034 ∷ []) (sym (wp0352 c4)) ▸ done


-- tP @0310243241: 7 steps
lem-tP-at0310243241 : Ws → ⟪ (Toff304 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ Toff304 ∷ []) ⟫ʷ
lem-tP-at0310243241 c4 = run b0
  where
  b0 : Chain (Toff304 ∷ Toff312 ∷ []) (Toff312 ∷ Toff304 ∷ [])
  b0 = at 0 1 (K3 ∷ CCZ034 ∷ K3⁻ ∷ []) (sym (wp0343 c4)) ▸
       at 3 1 (K3 ∷ CCZ123 ∷ K3⁻ ∷ []) (sym (wl0487 (lit c4))) ▸
       at 2 2 [] (wl0436 (lit c4)) ▸
       at 1 2 (CCZ123 ∷ CCZ034 ∷ []) (lem-cQ-at0310243241 c4) ▸
       at 2 0 (K3⁻ ∷ K3 ∷ []) (sym (wl0436 (lit c4))) ▸
       at 0 3 (Toff312 ∷ []) (wl0487 (lit c4)) ▸
       at 1 3 (Toff304 ∷ []) (wp0343 c4) ▸ done


-- VPQ @0310243241: 14 steps
lem-VPQ-at0310243241 : Ws → ⟪ (Toff304 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CCZ123 ∷ Toff304 ∷ CCZ034 ∷ []) ⟫ʷ
lem-VPQ-at0310243241 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff304 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ []) (CS12⁻ ∷ CS04⁻ ∷ S3 ∷ Toff312 ∷ Toff304 ∷ S3⁻ ∷ [])
  b0 = at 0 2 (CS04⁻ ∷ S3 ∷ Toff304 ∷ S3⁻ ∷ []) (sym (wp0347 c4)) ▸
       at 4 2 (CS12⁻ ∷ S3 ∷ Toff312 ∷ S3⁻ ∷ []) (sym (wl0488 (lit c4))) ▸
       at 3 2 (CS12⁻ ∷ S3⁻ ∷ []) (sym (c₃ ((CS • CS • CS) ↑) (S • S • S))) ▸
       at 2 2 (CS12⁻ ∷ Toff304 ∷ []) (lem-comm-TOFF304-CSd12 (lit c4)) ▸
       at 1 2 (CS12⁻ ∷ S3 ∷ []) (sym (c₃ ((CS • CS • CS) ↑) (S))) ▸
       at 0 2 (CS12⁻ ∷ CS04⁻ ∷ []) (wp0350 c4) ▸
       at 4 2 [] (wl0441 (lit c4)) ▸
       at 3 2 (Toff312 ∷ Toff304 ∷ []) (lem-tP-at0310243241 c4) ▸ done

  b1 : Chain (CS12⁻ ∷ CS04⁻ ∷ S3 ∷ Toff312 ∷ Toff304 ∷ S3⁻ ∷ []) (Toff312 ∷ CCZ123 ∷ Toff304 ∷ CCZ034 ∷ [])
  b1 = at 4 0 (S3⁻ ∷ S3 ∷ []) (sym (wl0441 (lit c4))) ▸
       at 1 2 (S3 ∷ CS04⁻ ∷ []) (wp0349 c4) ▸
       at 2 2 (Toff312 ∷ CS04⁻ ∷ []) (lem-comm-CSd04-TOFF312 (lit c4)) ▸
       at 3 2 (S3⁻ ∷ CS04⁻ ∷ []) (wp0348 c4) ▸
       at 0 4 (Toff312 ∷ CCZ123 ∷ []) (wl0488 (lit c4)) ▸
       at 2 4 (Toff304 ∷ CCZ034 ∷ []) (wp0347 c4) ▸ done


-- QVQ @0310243241: 3 steps
lem-QVQ-at0310243241 : Ws → ⟪ (CCZ123 ∷ Toff304 ∷ CCZ034 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ Toff304 ∷ CCZ034 ∷ Toff312 ∷ []) ⟫ʷ
lem-QVQ-at0310243241 c4 = run b0
  where
  b0 : Chain (CCZ123 ∷ Toff304 ∷ CCZ034 ∷ CCZ123 ∷ []) (Toff312 ∷ Toff304 ∷ CCZ034 ∷ Toff312 ∷ [])
  b0 = at 0 0 (Toff312 ∷ Toff312 ∷ []) (sym (wl0489 (lit c4))) ▸
       at 1 4 (Toff304 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ []) (sym (lem-VPQ-at0310243241 c4)) ▸
       at 4 2 [] (wl0181 (lit c4)) ▸ done


-- box-cP @0310243241: 12 steps
lem-box-cP-at0310243241 : Ws → ⟪ (Bx3-0421 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) ⟫ʷ
lem-box-cP-at0310243241 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-0421 ∷ []) (CCZ034 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ034 ∷ CCZ023 ∷ Toff023 ∷ CZ01 ∷ Toff023 ∷ CCZ023 ∷ CZ01 ∷ [])
  b0 = at 0 1 (CCZ034 ∷ Toff304 ∷ Bx0-321 ∷ Toff304 ∷ CCZ034 ∷ Bx0-321 ∷ []) (refl) ▸
       at 2 1 (CCZ023 ∷ Toff023 ∷ Bx3-01 ∷ Toff023 ∷ CCZ023 ∷ Bx3-01 ∷ []) (refl) ▸
       at 4 1 (CZ01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 2 6 (CCZ123 ∷ []) (wl1155 (lit c4)) ▸
       at 5 1 (CCZ023 ∷ Toff023 ∷ Bx3-01 ∷ Toff023 ∷ CCZ023 ∷ Bx3-01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 10 1 (CZ01 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ034 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ034 ∷ CCZ023 ∷ Toff023 ∷ CZ01 ∷ Toff023 ∷ CCZ023 ∷ CZ01 ∷ []) (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ [])
  b1 = at 5 6 (CCZ123 ∷ []) (wl1155 (lit c4)) ▸
       at 2 4 (Toff312 ∷ Toff304 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-QVQ-at0310243241 c4) ▸
       at 1 2 (Toff312 ∷ Toff304 ∷ []) (lem-tP-at0310243241 c4) ▸
       at 2 2 [] (wp0351 c4) ▸ done


-- Xb-box @0310243241: 18 steps
lem-Xb-box-at0310243241 : Ws → ⟪ (X4 ∷ Bx3-0421 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0421 ∷ CCZ012 ∷ []) ⟫ʷ
lem-Xb-box-at0310243241 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ Bx3-0421 ∷ X4 ∷ []) (CCZ034 ∷ Toff312 ∷ X4 ∷ CZ03 ∷ CS12 ∷ CX02 ∷ CCZ034 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ Toff312 ∷ X4 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243241 c4) ▸
       at 0 2 (CCZ034 ∷ X4 ∷ CZ03 ∷ []) (sym (wp0796 c4)) ▸
       at 2 2 (Toff312 ∷ CZ03 ∷ CCZ012 ∷ []) (wl0512 (lit c4)) ▸
       at 1 2 (Toff312 ∷ X4 ∷ []) (sym (c₄ (Toffᵗ ↑) (X))) ▸
       at 4 1 (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ []) (wl0391 (lit c4)) ▸
       at 8 2 (CCZ034 ∷ CS01 ∷ []) (sym (wp0001 c4)) ▸
       at 7 2 (CCZ034 ∷ CX02 ∷ []) (sym (wp0333 c4)) ▸
       at 6 2 (CCZ034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-CCZ034 (lit c4)) ▸ done

  b1 : Chain (CCZ034 ∷ Toff312 ∷ X4 ∷ CZ03 ∷ CS12 ∷ CX02 ∷ CCZ034 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ Toff312 ∷ X4 ∷ []) (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ X4 ∷ CCZ012 ∷ X4 ∷ [])
  b1 = at 5 2 (CCZ034 ∷ CX02 ∷ []) (sym (wp0333 c4)) ▸
       at 4 2 (CCZ034 ∷ CS12 ∷ []) (lem-comm-CS12-CCZ034 (lit c4)) ▸
       at 5 5 (CCZ012 ∷ []) (sym (wl0391 (lit c4))) ▸
       at 3 2 (CCZ034 ∷ CZ03 ∷ []) (sym (wp0797 c4)) ▸
       at 2 2 (CCZ034 ∷ X4 ∷ CZ03 ∷ []) (sym (wp0796 c4)) ▸
       at 3 3 (X4 ∷ []) (wp0798 c4) ▸
       at 4 2 (Toff312 ∷ CCZ012 ∷ []) (wl0503 (lit c4)) ▸
       at 3 2 (Toff312 ∷ X4 ∷ []) (sym (c₄ (Toffᵗ ↑) (X))) ▸ done

  b2 : Chain (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ X4 ∷ CCZ012 ∷ X4 ∷ []) (Bx3-0421 ∷ CCZ012 ∷ [])
  b2 = at 0 4 (Bx3-0421 ∷ []) (sym (lem-box-cP-at0310243241 c4)) ▸
       at 1 3 (CCZ012 ∷ []) (sym (wl1243 (lit c4))) ▸ done


-- box-tQ @0310243241: 13 steps
lem-box-tQ-at0310243241 : Ws → ⟪ (Bx3-0421 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) ⟫ʷ
lem-box-tQ-at0310243241 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-0421 ∷ []) (CCZ034 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ034 ∷ CCZ023 ∷ Toff023 ∷ CZ01 ∷ Toff023 ∷ CCZ023 ∷ CZ01 ∷ [])
  b0 = at 0 1 (CCZ034 ∷ Toff304 ∷ Bx0-321 ∷ Toff304 ∷ CCZ034 ∷ Bx0-321 ∷ []) (refl) ▸
       at 2 1 (CCZ023 ∷ Toff023 ∷ Bx3-01 ∷ Toff023 ∷ CCZ023 ∷ Bx3-01 ∷ []) (refl) ▸
       at 4 1 (CZ01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 2 6 (CCZ123 ∷ []) (wl1155 (lit c4)) ▸
       at 5 1 (CCZ023 ∷ Toff023 ∷ Bx3-01 ∷ Toff023 ∷ CCZ023 ∷ Bx3-01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 10 1 (CZ01 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ034 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ034 ∷ CCZ023 ∷ Toff023 ∷ CZ01 ∷ Toff023 ∷ CCZ023 ∷ CZ01 ∷ []) (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ [])
  b1 = at 5 6 (CCZ123 ∷ []) (wl1155 (lit c4)) ▸
       at 0 2 (Toff304 ∷ CCZ034 ∷ CZ04 ∷ []) (wp0353 c4) ▸
       at 2 2 (CCZ123 ∷ CZ04 ∷ []) (lem-comm-CZ04-CCZ123 (lit c4)) ▸
       at 1 2 (CCZ123 ∷ CCZ034 ∷ []) (lem-cQ-at0310243241 c4) ▸
       at 2 4 (Toff304 ∷ []) (wp0354 c4) ▸ done


-- CXbc-box @0310243241: 17 steps
lem-CXbc-box-at0310243241 : Ws → ⟪ (CX42 ∷ Bx3-0421 ∷ CX42 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0421 ∷ CCZ014 ∷ []) ⟫ʷ
lem-CXbc-box-at0310243241 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX42 ∷ Bx3-0421 ∷ CX42 ∷ []) (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CX42 ∷ CCZ134 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CCZ123 ∷ CX04 ∷ CS01 ∷ CX42 ∷ [])
  b0 = at 1 1 (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) (lem-box-tQ-at0310243241 c4) ▸
       at 0 2 (Toff304 ∷ CX42 ∷ []) (wp1055 c4) ▸
       at 1 2 (CCZ123 ∷ CX42 ∷ CCZ134 ∷ []) (sym (wl1244 (lit c4))) ▸
       at 3 2 (Toff304 ∷ CCZ134 ∷ CCZ014 ∷ []) (wp1056 c4) ▸
       at 2 2 (Toff304 ∷ CX42 ∷ []) (wp1055 c4) ▸
       at 5 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4) ▸
       at 9 2 (CCZ123 ∷ CS01 ∷ []) (sym (wl0763 (lit c4))) ▸
       at 8 2 (CCZ123 ∷ CX04 ∷ []) (lem-comm-CX04-CCZ123 (lit c4)) ▸ done

  b1 : Chain (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CX42 ∷ CCZ134 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CCZ123 ∷ CX04 ∷ CS01 ∷ CX42 ∷ []) (Bx3-0421 ∷ CX42 ∷ CCZ014 ∷ CX42 ∷ [])
  b1 = at 7 2 (CCZ123 ∷ CS14⁻ ∷ []) (sym (wl0764 (lit c4))) ▸
       at 6 2 (CCZ123 ∷ CX04 ∷ []) (lem-comm-CX04-CCZ123 (lit c4)) ▸
       at 5 2 (CCZ123 ∷ CS14 ∷ []) (sym (wl0765 (lit c4))) ▸
       at 6 5 (CCZ014 ∷ []) (sym (wp0041 c4)) ▸
       at 4 2 (CCZ123 ∷ CCZ134 ∷ []) (sym (wl0618 (lit c4))) ▸
       at 3 2 (CCZ123 ∷ CX42 ∷ CCZ134 ∷ []) (sym (wl1244 (lit c4))) ▸
       at 4 3 (CX42 ∷ []) (wl1245 (lit c4)) ▸
       at 0 4 (Bx3-0421 ∷ []) (sym (lem-box-tQ-at0310243241 c4)) ▸ done

  b2 : Chain (Bx3-0421 ∷ CX42 ∷ CCZ014 ∷ CX42 ∷ []) (Bx3-0421 ∷ CCZ014 ∷ [])
  b2 = at 1 3 (CCZ014 ∷ []) (sym (wp1021 c4)) ▸ done


-- CXcb-box @0310243241: 18 steps
lem-CXcb-box-at0310243241 : Ws → ⟪ (CX24 ∷ Bx3-0421 ∷ CX24 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0421 ∷ CCZ012 ∷ []) ⟫ʷ
lem-CXcb-box-at0310243241 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX24 ∷ Bx3-0421 ∷ CX24 ∷ []) (Toff304 ∷ CCZ123 ∷ CX24 ∷ Toff302 ∷ CS12 ∷ CX02 ∷ Toff304 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ CCZ123 ∷ CX24 ∷ [])
  b0 = at 1 1 (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) (lem-box-tQ-at0310243241 c4) ▸
       at 0 2 (Toff304 ∷ CX24 ∷ Toff302 ∷ []) (wp1057 c4) ▸
       at 2 2 (CCZ123 ∷ Toff302 ∷ CCZ012 ∷ []) (sym (wl1246 (lit c4))) ▸
       at 1 2 (CCZ123 ∷ CX24 ∷ []) (sym (wl0406 (lit c4))) ▸
       at 4 1 (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ []) (wl0391 (lit c4)) ▸
       at 8 2 (Toff304 ∷ CS01 ∷ []) (wp1058 c4) ▸
       at 7 2 (Toff304 ∷ CX02 ∷ []) (wp1059 c4) ▸
       at 6 2 (Toff304 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-TOFF304 (lit c4)) ▸ done

  b1 : Chain (Toff304 ∷ CCZ123 ∷ CX24 ∷ Toff302 ∷ CS12 ∷ CX02 ∷ Toff304 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ CCZ123 ∷ CX24 ∷ []) (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ CX24 ∷ CCZ012 ∷ CX24 ∷ [])
  b1 = at 5 2 (Toff304 ∷ CX02 ∷ []) (wp1059 c4) ▸
       at 4 2 (Toff304 ∷ CS12 ∷ []) (lem-comm-CS12-TOFF304 (lit c4)) ▸
       at 5 5 (CCZ012 ∷ []) (sym (wl0391 (lit c4))) ▸
       at 3 2 (Toff304 ∷ Toff302 ∷ []) (wp1053 c4) ▸
       at 2 2 (Toff304 ∷ CX24 ∷ Toff302 ∷ []) (wp1057 c4) ▸
       at 3 3 (CX24 ∷ []) (wp1060 c4) ▸
       at 4 2 (CCZ123 ∷ CCZ012 ∷ []) (wl0298 (lit c4)) ▸
       at 3 2 (CCZ123 ∷ CX24 ∷ []) (sym (wl0406 (lit c4))) ▸ done

  b2 : Chain (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ CX24 ∷ CCZ012 ∷ CX24 ∷ []) (Bx3-0421 ∷ CCZ012 ∷ [])
  b2 = at 0 4 (Bx3-0421 ∷ []) (sym (lem-box-tQ-at0310243241 c4)) ▸
       at 1 3 (CCZ012 ∷ []) (sym (wp1019 c4)) ▸ done


-- SWbc-box @0310243241: 11 steps
lem-SWbc-box-at0310243241 : Ws → ⟪ (Sw24 ∷ Bx3-0421 ∷ Sw24 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0421 ∷ []) ⟫ʷ
lem-SWbc-box-at0310243241 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw24 ∷ Bx3-0421 ∷ Sw24 ∷ []) (CX42 ∷ Bx3-0421 ∷ CX42 ∷ CCZ014 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CCZ014 ∷ [])
  b0 = at 0 1 (CX42 ∷ CX24 ∷ CX42 ∷ []) (sym (wl0316 (lit c4))) ▸
       at 4 1 (CX42 ∷ CX24 ∷ CX42 ∷ []) (sym (wl0316 (lit c4))) ▸
       at 2 3 (Bx3-0421 ∷ CCZ014 ∷ []) (lem-CXbc-box-at0310243241 c4) ▸
       at 3 2 (CX24 ∷ CCZ012 ∷ CCZ014 ∷ []) (wp1023 c4) ▸
       at 1 3 (Bx3-0421 ∷ CCZ012 ∷ []) (lem-CXcb-box-at0310243241 c4) ▸
       at 4 2 (CX42 ∷ CCZ014 ∷ []) (wp0269 c4) ▸
       at 3 2 (CX42 ∷ CCZ014 ∷ CCZ012 ∷ []) (wp1022 c4) ▸
       at 2 2 (CX42 ∷ CCZ014 ∷ CCZ012 ∷ []) (wp1022 c4) ▸ done

  b1 : Chain (CX42 ∷ Bx3-0421 ∷ CX42 ∷ CCZ014 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CCZ014 ∷ []) (Bx3-0421 ∷ [])
  b1 = at 3 5 (CCZ014 ∷ []) (wp1032 c4) ▸
       at 0 3 (Bx3-0421 ∷ CCZ014 ∷ []) (lem-CXbc-box-at0310243241 c4) ▸
       at 1 2 [] (wp0161 c4) ▸ done


-- nat-SWbc @0310243241: 23 steps
lem-nat-SWbc-at0310243241 : Ws → ⟪ (Sw24 ∷ Bx3-0421 ∷ Sw24 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0241 ∷ []) ⟫ʷ
lem-nat-SWbc-at0310243241 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw24 ∷ Bx3-0421 ∷ Sw24 ∷ []) (CCZ023 ∷ Toff302 ∷ CCZ034 ∷ Toff034 ∷ Bx3-01 ∷ Toff034 ∷ Sw24 ∷ CCZ023 ∷ Bx3-01 ∷ Toff304 ∷ CCZ034 ∷ Bx0-321 ∷ Sw24 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff304 ∷ Bx0-321 ∷ Toff304 ∷ CCZ034 ∷ Bx0-321 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw24 ∷ []) (sym (wp0175 c4)) ▸
       at 1 2 (Toff302 ∷ Sw24 ∷ []) (wp0274 c4) ▸
       at 3 1 (CCZ023 ∷ Toff023 ∷ Bx3-01 ∷ Toff023 ∷ CCZ023 ∷ Bx3-01 ∷ []) (refl) ▸
       at 2 2 (CCZ034 ∷ Sw24 ∷ []) (sym (wp0177 c4)) ▸
       at 3 2 (Toff034 ∷ Sw24 ∷ []) (wp0273 c4) ▸
       at 4 2 (Bx3-01 ∷ Sw24 ∷ []) (sym (c₂ (CZ) (Swap ↑ • Swap • Swap ↑))) ▸
       at 5 2 (Toff034 ∷ Sw24 ∷ []) (wp0273 c4) ▸ done

  b1 : Chain (CCZ023 ∷ Toff302 ∷ CCZ034 ∷ Toff034 ∷ Bx3-01 ∷ Toff034 ∷ Sw24 ∷ CCZ023 ∷ Bx3-01 ∷ Toff304 ∷ CCZ034 ∷ Bx0-321 ∷ Sw24 ∷ []) (CCZ023 ∷ Toff302 ∷ CCZ034 ∷ Toff034 ∷ Bx3-01 ∷ Toff034 ∷ CCZ034 ∷ Bx3-01 ∷ Toff302 ∷ CCZ023 ∷ CCZ034 ∷ Toff034 ∷ Bx3-01 ∷ Sw24 ∷ Toff023 ∷ CCZ023 ∷ Bx3-01 ∷ Sw24 ∷ [])
  b1 = at 6 2 (CCZ034 ∷ Sw24 ∷ []) (sym (wp0177 c4)) ▸
       at 7 2 (Bx3-01 ∷ Sw24 ∷ []) (sym (c₂ (CZ) (Swap ↑ • Swap • Swap ↑))) ▸
       at 8 2 (Toff302 ∷ Sw24 ∷ []) (wp0274 c4) ▸
       at 9 2 (CCZ023 ∷ Sw24 ∷ []) (sym (wp0175 c4)) ▸
       at 11 1 (CCZ023 ∷ Toff023 ∷ Bx3-01 ∷ Toff023 ∷ CCZ023 ∷ Bx3-01 ∷ []) (refl) ▸
       at 10 2 (CCZ034 ∷ Sw24 ∷ []) (sym (wp0177 c4)) ▸
       at 11 2 (Toff034 ∷ Sw24 ∷ []) (wp0273 c4) ▸
       at 12 2 (Bx3-01 ∷ Sw24 ∷ []) (sym (c₂ (CZ) (Swap ↑ • Swap • Swap ↑))) ▸ done

  b2 : Chain (CCZ023 ∷ Toff302 ∷ CCZ034 ∷ Toff034 ∷ Bx3-01 ∷ Toff034 ∷ CCZ034 ∷ Bx3-01 ∷ Toff302 ∷ CCZ023 ∷ CCZ034 ∷ Toff034 ∷ Bx3-01 ∷ Sw24 ∷ Toff023 ∷ CCZ023 ∷ Bx3-01 ∷ Sw24 ∷ []) (Bx3-0241 ∷ [])
  b2 = at 13 2 (Toff034 ∷ Sw24 ∷ []) (wp0273 c4) ▸
       at 14 2 (CCZ034 ∷ Sw24 ∷ []) (sym (wp0177 c4)) ▸
       at 15 2 (Bx3-01 ∷ Sw24 ∷ []) (sym (c₂ (CZ) (Swap ↑ • Swap • Swap ↑))) ▸
       at 16 2 [] (wl0322 (lit c4)) ▸
       at 2 6 (Bx0-341 ∷ []) (refl) ▸
       at 5 6 (Bx0-341 ∷ []) (refl) ▸
       at 0 6 (Bx3-0241 ∷ []) (refl) ▸ done


-- sym-bc @0310243241: 2 steps
lem-sym-bc-at0310243241 : Ws → ⟪ (Bx3-0421 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0241 ∷ []) ⟫ʷ
lem-sym-bc-at0310243241 c4 = run b0
  where
  b0 : Chain (Bx3-0421 ∷ []) (Bx3-0241 ∷ [])
  b0 = at 0 1 (Sw24 ∷ Bx3-0421 ∷ Sw24 ∷ []) (sym (lem-SWbc-box-at0310243241 c4)) ▸
       at 0 3 (Bx3-0241 ∷ []) (lem-nat-SWbc-at0310243241 c4) ▸ done


-- box-perm-1324 @0310243241: 1 steps
lem-box-perm-1324-at0310243241 : Ws → ⟪ (Bx3-0421 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0241 ∷ []) ⟫ʷ
lem-box-perm-1324-at0310243241 c4 = run b0
  where
  b0 : Chain (Bx3-0421 ∷ []) (Bx3-0241 ∷ [])
  b0 = at 0 1 (Bx3-0241 ∷ []) (lem-sym-bc-at0310243241 c4) ▸ done


-- CKc-box @03103441: 61 steps
lem-CKc-box-at03103441 : Ws → ⟪ (Bx3-0241 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ CK41 ∷ CCZ012 ∷ Bx3-0241 ∷ []) ⟫ʷ
lem-CKc-box-at03103441 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (run b7)))))))
  where
  b0 : Chain (Bx3-0241 ∷ CK41 ∷ []) (X4 ∷ Bx3-0241 ∷ CCZ012 ∷ K1 ∷ CK41 ∷ S4 ∷ CCZ012 ∷ X4 ∷ CCZ012 ∷ [])
  b0 = at 1 0 (CCZ012 ∷ CCZ012 ∷ []) (sym (wl0341 (lit c4))) ▸
       at 0 1 (Bx3-0421 ∷ []) (lem-box-perm-1324-at03103441 c4) ▸
       at 0 2 (X4 ∷ Bx3-0421 ∷ X4 ∷ []) (sym (lem-Xb-box-at0310243241 c4)) ▸
       at 3 2 (CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ012 ∷ []) (sym (wp1061 c4)) ▸
       at 2 2 (CCZ012 ∷ X4 ∷ []) (sym (c₃ (CCZ) (X ↑))) ▸
       at 3 2 (K1 ∷ CK41 ∷ S4 ∷ X4 ∷ []) (sym (wl0720 (lit c4))) ▸
       at 6 2 (CCZ012 ∷ X4 ∷ []) (sym (c₃ (CCZ) (X ↑))) ▸
       at 1 1 (Bx3-0241 ∷ []) (lem-box-perm-1324-at0310243241 c4) ▸ done

  b1 : Chain (X4 ∷ Bx3-0241 ∷ CCZ012 ∷ K1 ∷ CK41 ∷ S4 ∷ CCZ012 ∷ X4 ∷ CCZ012 ∷ []) (X4 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ012 ∷ CCZ134 ∷ K1 ∷ CK41 ∷ S4 ∷ CCZ012 ∷ X4 ∷ CCZ012 ∷ [])
  b1 = at 1 1 (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ []) (lem-box-tQ-at03103441 c4) ▸
       at 5 1 (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ []) (wl0391 (lit c4)) ▸
       at 4 2 (CS12 ∷ CCZ134 ∷ []) (wl0393 (lit c4)) ▸
       at 5 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸
       at 6 2 (CS12⁻ ∷ CCZ134 ∷ []) (wl0392 (lit c4)) ▸
       at 7 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸
       at 8 2 (CS01 ∷ CCZ134 ∷ []) (wp0261 c4) ▸
       at 4 5 (CCZ012 ∷ []) (sym (wl0391 (lit c4))) ▸ done

  b2 : Chain (X4 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ012 ∷ CCZ134 ∷ K1 ∷ CK41 ∷ S4 ∷ CCZ012 ∷ X4 ∷ CCZ012 ∷ []) (X4 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ012 ∷ K1 ∷ Toff134 ∷ CCZ134 ∷ CZ13 ∷ CK41 ∷ CZ13 ∷ S4 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CCZ134 ∷ CS01 ∷ X4 ∷ CCZ012 ∷ [])
  b2 = at 5 2 (K1 ∷ Toff134 ∷ CCZ134 ∷ CCZ134 ∷ []) (wl1247 (lit c4)) ▸
       at 8 2 (CZ13 ∷ CK41 ∷ CZ13 ∷ CCZ134 ∷ []) (wl1248 (lit c4)) ▸
       at 11 2 (S4 ∷ CCZ134 ∷ []) (wl1249 (lit c4)) ▸
       at 13 1 (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ []) (wl0391 (lit c4)) ▸
       at 12 2 (CS12 ∷ CCZ134 ∷ []) (wl0393 (lit c4)) ▸
       at 13 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸
       at 14 2 (CS12⁻ ∷ CCZ134 ∷ []) (wl0392 (lit c4)) ▸
       at 15 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸ done

  b3 : Chain (X4 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ012 ∷ K1 ∷ Toff134 ∷ CCZ134 ∷ CZ13 ∷ CK41 ∷ CZ13 ∷ S4 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CCZ134 ∷ CS01 ∷ X4 ∷ CCZ012 ∷ []) (X4 ∷ Toff302 ∷ CCZ134 ∷ CCZ012 ∷ K1 ∷ CK41 ∷ S4 ∷ CCZ012 ∷ Toff302 ∷ CCZ134 ∷ X4 ∷ CCZ012 ∷ [])
  b3 = at 16 2 (CS01 ∷ CCZ134 ∷ []) (wp0261 c4) ▸
       at 12 5 (CCZ012 ∷ []) (sym (wl0391 (lit c4))) ▸
       at 5 7 (K1 ∷ CK41 ∷ S4 ∷ []) (sym (wl1250 (lit c4))) ▸
       at 3 2 (CCZ012 ∷ Toff302 ∷ []) (sym (wl1251 (lit c4))) ▸
       at 4 2 (K1 ∷ Toff302 ∷ []) (sym (wl1252 (lit c4))) ▸
       at 5 2 (CK41 ∷ Toff302 ∷ []) (lem-comm-TOFF302-CK41 (lit c4)) ▸
       at 6 2 (S4 ∷ Toff302 ∷ []) (c₄ (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑) (S)) ▸
       at 7 2 (CCZ012 ∷ Toff302 ∷ []) (sym (wl1251 (lit c4))) ▸ done

  b4 : Chain (X4 ∷ Toff302 ∷ CCZ134 ∷ CCZ012 ∷ K1 ∷ CK41 ∷ S4 ∷ CCZ012 ∷ Toff302 ∷ CCZ134 ∷ X4 ∷ CCZ012 ∷ []) (X4 ∷ Toff302 ∷ CCZ012 ∷ K1 ∷ Toff134 ∷ CCZ134 ∷ CCZ134 ∷ CK41 ∷ S4 ∷ CCZ012 ∷ Toff302 ∷ CCZ134 ∷ X4 ∷ CCZ012 ∷ [])
  b4 = at 3 1 (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ []) (wl0391 (lit c4)) ▸
       at 2 2 (CS12 ∷ CCZ134 ∷ []) (wl0393 (lit c4)) ▸
       at 3 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸
       at 4 2 (CS12⁻ ∷ CCZ134 ∷ []) (wl0392 (lit c4)) ▸
       at 5 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸
       at 6 2 (CS01 ∷ CCZ134 ∷ []) (wp0261 c4) ▸
       at 2 5 (CCZ012 ∷ []) (sym (wl0391 (lit c4))) ▸
       at 3 2 (K1 ∷ Toff134 ∷ CCZ134 ∷ CCZ134 ∷ []) (wl1247 (lit c4)) ▸ done

  b5 : Chain (X4 ∷ Toff302 ∷ CCZ012 ∷ K1 ∷ Toff134 ∷ CCZ134 ∷ CCZ134 ∷ CK41 ∷ S4 ∷ CCZ012 ∷ Toff302 ∷ CCZ134 ∷ X4 ∷ CCZ012 ∷ []) (X4 ∷ Toff302 ∷ CCZ012 ∷ K1 ∷ Toff134 ∷ CCZ134 ∷ CZ13 ∷ CK41 ∷ CZ13 ∷ S4 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ X4 ∷ CCZ012 ∷ [])
  b5 = at 6 2 (CZ13 ∷ CK41 ∷ CZ13 ∷ CCZ134 ∷ []) (wl1248 (lit c4)) ▸
       at 9 2 (S4 ∷ CCZ134 ∷ []) (wl1249 (lit c4)) ▸
       at 11 1 (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ []) (wl0391 (lit c4)) ▸
       at 10 2 (CS12 ∷ CCZ134 ∷ []) (wl0393 (lit c4)) ▸
       at 11 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸
       at 12 2 (CS12⁻ ∷ CCZ134 ∷ []) (wl0392 (lit c4)) ▸
       at 13 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸
       at 14 2 (CS01 ∷ CCZ134 ∷ []) (wp0261 c4) ▸ done

  b6 : Chain (X4 ∷ Toff302 ∷ CCZ012 ∷ K1 ∷ Toff134 ∷ CCZ134 ∷ CZ13 ∷ CK41 ∷ CZ13 ∷ S4 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ X4 ∷ CCZ012 ∷ []) (X4 ∷ CCZ012 ∷ K1 ∷ CK41 ∷ S4 ∷ CCZ012 ∷ Bx3-0241 ∷ X4 ∷ CCZ012 ∷ [])
  b6 = at 10 5 (CCZ012 ∷ []) (sym (wl0391 (lit c4))) ▸
       at 3 7 (K1 ∷ CK41 ∷ S4 ∷ []) (sym (wl1250 (lit c4))) ▸
       at 1 2 (CCZ012 ∷ Toff302 ∷ []) (sym (wl1251 (lit c4))) ▸
       at 2 2 (K1 ∷ Toff302 ∷ []) (sym (wl1252 (lit c4))) ▸
       at 3 2 (CK41 ∷ Toff302 ∷ []) (lem-comm-TOFF302-CK41 (lit c4)) ▸
       at 4 2 (S4 ∷ Toff302 ∷ []) (c₄ (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑) (S)) ▸
       at 5 2 (CCZ012 ∷ Toff302 ∷ []) (sym (wl1251 (lit c4))) ▸
       at 6 4 (Bx3-0241 ∷ []) (sym (lem-box-tQ-at03103441 c4)) ▸ done

  b7 : Chain (X4 ∷ CCZ012 ∷ K1 ∷ CK41 ∷ S4 ∷ CCZ012 ∷ Bx3-0241 ∷ X4 ∷ CCZ012 ∷ []) (CCZ012 ∷ CK41 ∷ CCZ012 ∷ Bx3-0241 ∷ [])
  b7 = at 6 1 (Bx3-0421 ∷ []) (sym (lem-box-perm-1324-at0310243241 c4)) ▸
       at 0 6 (CCZ012 ∷ CK41 ∷ CCZ012 ∷ X4 ∷ []) (sym (wp1062 c4)) ▸
       at 3 3 (Bx3-0421 ∷ CCZ012 ∷ []) (lem-Xb-box-at0310243241 c4) ▸
       at 4 2 [] (wl0341 (lit c4)) ▸
       at 3 1 (Bx3-0241 ∷ []) (lem-box-perm-1324-at0310243241 c4) ▸ done


-- tP @03103441: 7 steps
lem-tP-at03103441 : Ws → ⟪ (Toff302 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ Toff302 ∷ []) ⟫ʷ
lem-tP-at03103441 c4 = run b0
  where
  b0 : Chain (Toff302 ∷ Toff314 ∷ []) (Toff314 ∷ Toff302 ∷ [])
  b0 = at 0 1 (K3 ∷ CCZ023 ∷ K3⁻ ∷ []) (sym (wl0782 (lit c4))) ▸
       at 3 1 (K3 ∷ CCZ134 ∷ K3⁻ ∷ []) (sym (wl0781 (lit c4))) ▸
       at 2 2 [] (wl0436 (lit c4)) ▸
       at 1 2 (CCZ134 ∷ CCZ023 ∷ []) (lem-cQ-at03103441 c4) ▸
       at 2 0 (K3⁻ ∷ K3 ∷ []) (sym (wl0436 (lit c4))) ▸
       at 0 3 (Toff314 ∷ []) (wl0781 (lit c4)) ▸
       at 1 3 (Toff302 ∷ []) (wl0782 (lit c4)) ▸ done


-- P-box @03103441: 8 steps
lem-P-box-at03103441 : Ws → ⟪ (Toff314 ∷ Bx3-0241 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0241 ∷ []) ⟫ʷ
lem-P-box-at03103441 c4 = run b0
  where
  b0 : Chain (Toff314 ∷ Bx3-0241 ∷ Toff314 ∷ []) (Bx3-0241 ∷ [])
  b0 = at 1 1 (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ []) (lem-box-tQ-at03103441 c4) ▸
       at 0 2 (Toff302 ∷ Toff314 ∷ []) (sym (lem-tP-at03103441 c4)) ▸
       at 1 2 (CCZ134 ∷ CZ14 ∷ Toff314 ∷ []) (sym (wl1253 (lit c4))) ▸
       at 3 2 (Toff302 ∷ Toff314 ∷ []) (sym (lem-tP-at03103441 c4)) ▸
       at 4 3 (CCZ134 ∷ CZ14 ∷ []) (sym (wl1254 (lit c4))) ▸
       at 2 2 (Toff302 ∷ CZ14 ∷ []) (lem-comm-CZ14-TOFF302 (lit c4)) ▸
       at 3 3 (CCZ134 ∷ []) (sym (wl1255 (lit c4))) ▸
       at 0 4 (Bx3-0241 ∷ []) (sym (lem-box-tQ-at03103441 c4)) ▸ done


-- VPQ @03103441: 14 steps
lem-VPQ-at03103441 : Ws → ⟪ (Toff302 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CCZ134 ∷ Toff302 ∷ CCZ023 ∷ []) ⟫ʷ
lem-VPQ-at03103441 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff302 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ []) (CS14⁻ ∷ CS02⁻ ∷ S3 ∷ Toff314 ∷ Toff302 ∷ S3⁻ ∷ [])
  b0 = at 0 2 (CS02⁻ ∷ S3 ∷ Toff302 ∷ S3⁻ ∷ []) (sym (wl0784 (lit c4))) ▸
       at 4 2 (CS14⁻ ∷ S3 ∷ Toff314 ∷ S3⁻ ∷ []) (sym (wl0783 (lit c4))) ▸
       at 3 2 (CS14⁻ ∷ S3⁻ ∷ []) (sym (wl0786 (lit c4))) ▸
       at 2 2 (CS14⁻ ∷ Toff302 ∷ []) (lem-comm-TOFF302-CSd14 (lit c4)) ▸
       at 1 2 (CS14⁻ ∷ S3 ∷ []) (sym (wl0785 (lit c4))) ▸
       at 0 2 (CS14⁻ ∷ CS02⁻ ∷ []) (wp0703 c4) ▸
       at 4 2 [] (wl0441 (lit c4)) ▸
       at 3 2 (Toff314 ∷ Toff302 ∷ []) (lem-tP-at03103441 c4) ▸ done

  b1 : Chain (CS14⁻ ∷ CS02⁻ ∷ S3 ∷ Toff314 ∷ Toff302 ∷ S3⁻ ∷ []) (Toff314 ∷ CCZ134 ∷ Toff302 ∷ CCZ023 ∷ [])
  b1 = at 4 0 (S3⁻ ∷ S3 ∷ []) (sym (wl0441 (lit c4))) ▸
       at 1 2 (S3 ∷ CS02⁻ ∷ []) (c₃ (Swap ↑ • (CS • CS • CS) • Swap ↑) (S)) ▸
       at 2 2 (Toff314 ∷ CS02⁻ ∷ []) (lem-comm-CSd02-TOFF314 (lit c4)) ▸
       at 3 2 (S3⁻ ∷ CS02⁻ ∷ []) (c₃ (Swap ↑ • (CS • CS • CS) • Swap ↑) (S • S • S)) ▸
       at 0 4 (Toff314 ∷ CCZ134 ∷ []) (wl0783 (lit c4)) ▸
       at 2 4 (Toff302 ∷ CCZ023 ∷ []) (wl0784 (lit c4)) ▸ done


-- QVQ @03103441: 3 steps
lem-QVQ-at03103441 : Ws → ⟪ (CCZ134 ∷ Toff302 ∷ CCZ023 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ Toff302 ∷ CCZ023 ∷ Toff314 ∷ []) ⟫ʷ
lem-QVQ-at03103441 c4 = run b0
  where
  b0 : Chain (CCZ134 ∷ Toff302 ∷ CCZ023 ∷ CCZ134 ∷ []) (Toff314 ∷ Toff302 ∷ CCZ023 ∷ Toff314 ∷ [])
  b0 = at 0 0 (Toff314 ∷ Toff314 ∷ []) (sym (wl0788 (lit c4))) ▸
       at 1 4 (Toff302 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ []) (sym (lem-VPQ-at03103441 c4)) ▸
       at 4 2 [] (wl0321 (lit c4)) ▸ done


-- box-cP @03103441: 12 steps
lem-box-cP-at03103441 : Ws → ⟪ (Bx3-0241 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ []) ⟫ʷ
lem-box-cP-at03103441 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-0241 ∷ []) (CCZ023 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ023 ∷ CCZ034 ∷ Toff034 ∷ CZ01 ∷ Toff034 ∷ CCZ034 ∷ CZ01 ∷ [])
  b0 = at 0 1 (CCZ023 ∷ Toff302 ∷ Bx0-341 ∷ Toff302 ∷ CCZ023 ∷ Bx0-341 ∷ []) (refl) ▸
       at 2 1 (CCZ034 ∷ Toff034 ∷ Bx3-01 ∷ Toff034 ∷ CCZ034 ∷ Bx3-01 ∷ []) (refl) ▸
       at 4 1 (CZ01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 2 6 (CCZ134 ∷ []) (wp1048 c4) ▸
       at 5 1 (CCZ034 ∷ Toff034 ∷ Bx3-01 ∷ Toff034 ∷ CCZ034 ∷ Bx3-01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 10 1 (CZ01 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ023 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ023 ∷ CCZ034 ∷ Toff034 ∷ CZ01 ∷ Toff034 ∷ CCZ034 ∷ CZ01 ∷ []) (CCZ023 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ [])
  b1 = at 5 6 (CCZ134 ∷ []) (wp1048 c4) ▸
       at 2 4 (Toff314 ∷ Toff302 ∷ CCZ023 ∷ Toff314 ∷ []) (lem-QVQ-at03103441 c4) ▸
       at 1 2 (Toff314 ∷ Toff302 ∷ []) (lem-tP-at03103441 c4) ▸
       at 2 2 [] (wl0787 (lit c4)) ▸ done


-- pairs @03103441: 4 steps
lem-pairs-at03103441 : Ws → ⟪ (Bx3-0241 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4102 ∷ []) ⟫ʷ
lem-pairs-at03103441 c4 = run b0
  where
  b0 : Chain (Bx3-0241 ∷ []) (Bx3-4102 ∷ [])
  b0 = at 0 1 (Toff314 ∷ Bx3-0241 ∷ Toff314 ∷ []) (sym (lem-P-box-at03103441 c4)) ▸
       at 1 1 (CCZ023 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ []) (lem-box-cP-at03103441 c4) ▸
       at 4 2 [] (wl0788 (lit c4)) ▸
       at 0 4 (Bx3-4102 ∷ []) (sym (lem-box-tQ-at0314213042 c4)) ▸ done


-- box-perm-1342 @03103441: 3 steps
lem-box-perm-1342-at03103441 : Ws → ⟪ (Bx3-0241 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ []) ⟫ʷ
lem-box-perm-1342-at03103441 c4 = run b0
  where
  b0 : Chain (Bx3-0241 ∷ []) (Bx3-0412 ∷ [])
  b0 = at 0 1 (Bx3-4102 ∷ []) (lem-pairs-at03103441 c4) ▸
       at 0 1 (Bx3-4012 ∷ []) (lem-sym-bc-at0314213042 c4) ▸
       at 0 1 (Bx3-0412 ∷ []) (lem-sym-ab-at0314203142 c4) ▸ done


-- CXbc-box @0310243142: 17 steps
lem-CXbc-box-at0310243142 : Ws → ⟪ (CX41 ∷ Bx3-0412 ∷ CX41 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ CCZ024 ∷ []) ⟫ʷ
lem-CXbc-box-at0310243142 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX41 ∷ Bx3-0412 ∷ CX41 ∷ []) (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CX41 ∷ CCZ234 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ CCZ123 ∷ CX04 ∷ CS02 ∷ CX41 ∷ [])
  b0 = at 1 1 (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) (lem-box-tQ-at0310243142 c4) ▸
       at 0 2 (Toff304 ∷ CX41 ∷ []) (wp0692 c4) ▸
       at 1 2 (CCZ123 ∷ CX41 ∷ CCZ234 ∷ []) (sym (wl0694 (lit c4))) ▸
       at 3 2 (Toff304 ∷ CCZ234 ∷ CCZ024 ∷ []) (wp1063 c4) ▸
       at 2 2 (Toff304 ∷ CX41 ∷ []) (wp0692 c4) ▸
       at 5 1 (CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ []) (wp0013 c4) ▸
       at 9 2 (CCZ123 ∷ CS02 ∷ []) (sym (wl0171 (lit c4))) ▸
       at 8 2 (CCZ123 ∷ CX04 ∷ []) (lem-comm-CX04-CCZ123 (lit c4)) ▸ done

  b1 : Chain (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CX41 ∷ CCZ234 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ CCZ123 ∷ CX04 ∷ CS02 ∷ CX41 ∷ []) (Bx3-0412 ∷ CX41 ∷ CCZ024 ∷ CX41 ∷ [])
  b1 = at 7 2 (CCZ123 ∷ CS24⁻ ∷ []) (sym (wl0172 (lit c4))) ▸
       at 6 2 (CCZ123 ∷ CX04 ∷ []) (lem-comm-CX04-CCZ123 (lit c4)) ▸
       at 5 2 (CCZ123 ∷ CS24 ∷ []) (sym (wl0173 (lit c4))) ▸
       at 6 5 (CCZ024 ∷ []) (sym (wp0013 c4)) ▸
       at 4 2 (CCZ123 ∷ CCZ234 ∷ []) (sym (wl0508 (lit c4))) ▸
       at 3 2 (CCZ123 ∷ CX41 ∷ CCZ234 ∷ []) (sym (wl0694 (lit c4))) ▸
       at 4 3 (CX41 ∷ []) (wl0695 (lit c4)) ▸
       at 0 4 (Bx3-0412 ∷ []) (sym (lem-box-tQ-at0310243142 c4)) ▸ done

  b2 : Chain (Bx3-0412 ∷ CX41 ∷ CCZ024 ∷ CX41 ∷ []) (Bx3-0412 ∷ CCZ024 ∷ [])
  b2 = at 1 3 (CCZ024 ∷ []) (sym (wp0727 c4)) ▸ done


-- CXcb-box @0310243142: 18 steps
lem-CXcb-box-at0310243142 : Ws → ⟪ (CX14 ∷ Bx3-0412 ∷ CX14 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ CCZ012 ∷ []) ⟫ʷ
lem-CXcb-box-at0310243142 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX14 ∷ Bx3-0412 ∷ CX14 ∷ []) (Toff304 ∷ CCZ123 ∷ CX14 ∷ Toff301 ∷ CS12 ∷ CX01 ∷ Toff304 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ CCZ123 ∷ CX14 ∷ [])
  b0 = at 1 1 (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) (lem-box-tQ-at0310243142 c4) ▸
       at 0 2 (Toff304 ∷ CX14 ∷ Toff301 ∷ []) (wp1064 c4) ▸
       at 2 2 (CCZ123 ∷ Toff301 ∷ CCZ012 ∷ []) (sym (wl1256 (lit c4))) ▸
       at 1 2 (CCZ123 ∷ CX14 ∷ []) (sym (wl0424 (lit c4))) ▸
       at 4 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wl0348 (lit c4)) ▸
       at 8 2 (Toff304 ∷ CS02 ∷ []) (wp1065 c4) ▸
       at 7 2 (Toff304 ∷ CX01 ∷ []) (wp0688 c4) ▸
       at 6 2 (Toff304 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-TOFF304 (lit c4)) ▸ done

  b1 : Chain (Toff304 ∷ CCZ123 ∷ CX14 ∷ Toff301 ∷ CS12 ∷ CX01 ∷ Toff304 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ CCZ123 ∷ CX14 ∷ []) (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ CX14 ∷ CCZ012 ∷ CX14 ∷ [])
  b1 = at 5 2 (Toff304 ∷ CX01 ∷ []) (wp0688 c4) ▸
       at 4 2 (Toff304 ∷ CS12 ∷ []) (lem-comm-CS12-TOFF304 (lit c4)) ▸
       at 5 5 (CCZ012 ∷ []) (sym (wl0348 (lit c4))) ▸
       at 3 2 (Toff304 ∷ Toff301 ∷ []) (wp1066 c4) ▸
       at 2 2 (Toff304 ∷ CX14 ∷ Toff301 ∷ []) (wp1064 c4) ▸
       at 3 3 (CX14 ∷ []) (wp1067 c4) ▸
       at 4 2 (CCZ123 ∷ CCZ012 ∷ []) (wl0298 (lit c4)) ▸
       at 3 2 (CCZ123 ∷ CX14 ∷ []) (sym (wl0424 (lit c4))) ▸ done

  b2 : Chain (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ CX14 ∷ CCZ012 ∷ CX14 ∷ []) (Bx3-0412 ∷ CCZ012 ∷ [])
  b2 = at 0 4 (Bx3-0412 ∷ []) (sym (lem-box-tQ-at0310243142 c4)) ▸
       at 1 3 (CCZ012 ∷ []) (sym (wp0728 c4)) ▸ done


-- SWbc-box @0310243142: 11 steps
lem-SWbc-box-at0310243142 : Ws → ⟪ (Sw14 ∷ Bx3-0412 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ []) ⟫ʷ
lem-SWbc-box-at0310243142 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw14 ∷ Bx3-0412 ∷ Sw14 ∷ []) (CX41 ∷ Bx3-0412 ∷ CX41 ∷ CCZ024 ∷ CCZ012 ∷ CCZ024 ∷ CCZ012 ∷ CCZ024 ∷ [])
  b0 = at 0 1 (CX41 ∷ CX14 ∷ CX41 ∷ []) (sym (wl0300 (lit c4))) ▸
       at 4 1 (CX41 ∷ CX14 ∷ CX41 ∷ []) (sym (wl0300 (lit c4))) ▸
       at 2 3 (Bx3-0412 ∷ CCZ024 ∷ []) (lem-CXbc-box-at0310243142 c4) ▸
       at 3 2 (CX14 ∷ CCZ012 ∷ CCZ024 ∷ []) (wp0729 c4) ▸
       at 1 3 (Bx3-0412 ∷ CCZ012 ∷ []) (lem-CXcb-box-at0310243142 c4) ▸
       at 4 2 (CX41 ∷ CCZ024 ∷ []) (wp0285 c4) ▸
       at 3 2 (CX41 ∷ CCZ024 ∷ CCZ012 ∷ []) (wp0730 c4) ▸
       at 2 2 (CX41 ∷ CCZ024 ∷ CCZ012 ∷ []) (wp0730 c4) ▸ done

  b1 : Chain (CX41 ∷ Bx3-0412 ∷ CX41 ∷ CCZ024 ∷ CCZ012 ∷ CCZ024 ∷ CCZ012 ∷ CCZ024 ∷ []) (Bx3-0412 ∷ [])
  b1 = at 3 5 (CCZ024 ∷ []) (wp0731 c4) ▸
       at 0 3 (Bx3-0412 ∷ CCZ024 ∷ []) (lem-CXbc-box-at0310243142 c4) ▸
       at 1 2 [] (wp0135 c4) ▸ done


-- nat-SWbc @0310243142: 23 steps
lem-nat-SWbc-at0310243142 : Ws → ⟪ (Sw14 ∷ Bx3-0412 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0142 ∷ []) ⟫ʷ
lem-nat-SWbc-at0310243142 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw14 ∷ Bx3-0412 ∷ Sw14 ∷ []) (CCZ013 ∷ Toff301 ∷ CCZ034 ∷ Toff034 ∷ Bx3-02 ∷ Toff034 ∷ Sw14 ∷ CCZ013 ∷ Bx3-02 ∷ Toff304 ∷ CCZ034 ∷ Bx0-312 ∷ Sw14 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff304 ∷ Bx0-312 ∷ Toff304 ∷ CCZ034 ∷ Bx0-312 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw14 ∷ []) (sym (wp0149 c4)) ▸
       at 1 2 (Toff301 ∷ Sw14 ∷ []) (wp0289 c4) ▸
       at 3 1 (CCZ013 ∷ Toff013 ∷ Bx3-02 ∷ Toff013 ∷ CCZ013 ∷ Bx3-02 ∷ []) (refl) ▸
       at 2 2 (CCZ034 ∷ Sw14 ∷ []) (sym (wp0151 c4)) ▸
       at 3 2 (Toff034 ∷ Sw14 ∷ []) (wp0288 c4) ▸
       at 4 2 (Bx3-02 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨3·02⟩ (lit c4)) ▸
       at 5 2 (Toff034 ∷ Sw14 ∷ []) (wp0288 c4) ▸ done

  b1 : Chain (CCZ013 ∷ Toff301 ∷ CCZ034 ∷ Toff034 ∷ Bx3-02 ∷ Toff034 ∷ Sw14 ∷ CCZ013 ∷ Bx3-02 ∷ Toff304 ∷ CCZ034 ∷ Bx0-312 ∷ Sw14 ∷ []) (CCZ013 ∷ Toff301 ∷ CCZ034 ∷ Toff034 ∷ Bx3-02 ∷ Toff034 ∷ CCZ034 ∷ Bx3-02 ∷ Toff301 ∷ CCZ013 ∷ CCZ034 ∷ Toff034 ∷ Bx3-02 ∷ Sw14 ∷ Toff013 ∷ CCZ013 ∷ Bx3-02 ∷ Sw14 ∷ [])
  b1 = at 6 2 (CCZ034 ∷ Sw14 ∷ []) (sym (wp0151 c4)) ▸
       at 7 2 (Bx3-02 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨3·02⟩ (lit c4)) ▸
       at 8 2 (Toff301 ∷ Sw14 ∷ []) (wp0289 c4) ▸
       at 9 2 (CCZ013 ∷ Sw14 ∷ []) (sym (wp0149 c4)) ▸
       at 11 1 (CCZ013 ∷ Toff013 ∷ Bx3-02 ∷ Toff013 ∷ CCZ013 ∷ Bx3-02 ∷ []) (refl) ▸
       at 10 2 (CCZ034 ∷ Sw14 ∷ []) (sym (wp0151 c4)) ▸
       at 11 2 (Toff034 ∷ Sw14 ∷ []) (wp0288 c4) ▸
       at 12 2 (Bx3-02 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨3·02⟩ (lit c4)) ▸ done

  b2 : Chain (CCZ013 ∷ Toff301 ∷ CCZ034 ∷ Toff034 ∷ Bx3-02 ∷ Toff034 ∷ CCZ034 ∷ Bx3-02 ∷ Toff301 ∷ CCZ013 ∷ CCZ034 ∷ Toff034 ∷ Bx3-02 ∷ Sw14 ∷ Toff013 ∷ CCZ013 ∷ Bx3-02 ∷ Sw14 ∷ []) (Bx3-0142 ∷ [])
  b2 = at 13 2 (Toff034 ∷ Sw14 ∷ []) (wp0288 c4) ▸
       at 14 2 (CCZ034 ∷ Sw14 ∷ []) (sym (wp0151 c4)) ▸
       at 15 2 (Bx3-02 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨3·02⟩ (lit c4)) ▸
       at 16 2 [] (wl0306 (lit c4)) ▸
       at 2 6 (Bx0-342 ∷ []) (refl) ▸
       at 5 6 (Bx0-342 ∷ []) (refl) ▸
       at 0 6 (Bx3-0142 ∷ []) (refl) ▸ done


-- sym-bc @0310243142: 2 steps
lem-sym-bc-at0310243142 : Ws → ⟪ (Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0142 ∷ []) ⟫ʷ
lem-sym-bc-at0310243142 c4 = run b0
  where
  b0 : Chain (Bx3-0412 ∷ []) (Bx3-0142 ∷ [])
  b0 = at 0 1 (Sw14 ∷ Bx3-0412 ∷ Sw14 ∷ []) (sym (lem-SWbc-box-at0310243142 c4)) ▸
       at 0 3 (Bx3-0142 ∷ []) (lem-nat-SWbc-at0310243142 c4) ▸ done


-- box-perm-1324 @0310243142: 1 steps
lem-box-perm-1324-at0310243142 : Ws → ⟪ (Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0142 ∷ []) ⟫ʷ
lem-box-perm-1324-at0310243142 c4 = run b0
  where
  b0 : Chain (Bx3-0412 ∷ []) (Bx3-0142 ∷ [])
  b0 = at 0 1 (Bx3-0142 ∷ []) (lem-sym-bc-at0310243142 c4) ▸ done


-- cQ @0310213442: 7 steps
lem-cQ-at0310213442 : Ws → ⟪ (CCZ013 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ CCZ013 ∷ []) ⟫ʷ
lem-cQ-at0310213442 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ013 ∷ [])
  b0 = at 0 1 (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ []) (wl0184 (lit c4)) ▸
       at 4 2 (CCZ234 ∷ CS03 ∷ []) (sym (wp0294 c4)) ▸
       at 3 2 (CCZ234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (CCZ)) ▸
       at 2 2 (CCZ234 ∷ CS13⁻ ∷ []) (sym (wl0432 (lit c4))) ▸
       at 1 2 (CCZ234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (CCZ)) ▸
       at 0 2 (CCZ234 ∷ CS13 ∷ []) (sym (wl0433 (lit c4))) ▸
       at 1 5 (CCZ013 ∷ []) (sym (wl0184 (lit c4))) ▸ done


-- box-tQ @0310213442: 13 steps
lem-box-tQ-at0310213442 : Ws → ⟪ (Bx3-0142 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ []) ⟫ʷ
lem-box-tQ-at0310213442 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-0142 ∷ []) (CCZ013 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ013 ∷ CCZ034 ∷ Toff034 ∷ CZ02 ∷ Toff034 ∷ CCZ034 ∷ CZ02 ∷ [])
  b0 = at 0 1 (CCZ013 ∷ Toff301 ∷ Bx0-342 ∷ Toff301 ∷ CCZ013 ∷ Bx0-342 ∷ []) (refl) ▸
       at 2 1 (CCZ034 ∷ Toff034 ∷ Bx3-02 ∷ Toff034 ∷ CCZ034 ∷ Bx3-02 ∷ []) (refl) ▸
       at 4 1 (CZ02 ∷ []) (refl) ▸
       at 7 1 (CZ02 ∷ []) (refl) ▸
       at 2 6 (CCZ234 ∷ []) (wp1068 c4) ▸
       at 5 1 (CCZ034 ∷ Toff034 ∷ Bx3-02 ∷ Toff034 ∷ CCZ034 ∷ Bx3-02 ∷ []) (refl) ▸
       at 7 1 (CZ02 ∷ []) (refl) ▸
       at 10 1 (CZ02 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ013 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ013 ∷ CCZ034 ∷ Toff034 ∷ CZ02 ∷ Toff034 ∷ CCZ034 ∷ CZ02 ∷ []) (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ [])
  b1 = at 5 6 (CCZ234 ∷ []) (wp1068 c4) ▸
       at 0 2 (Toff301 ∷ CCZ013 ∷ CZ01 ∷ []) (wl0519 (lit c4)) ▸
       at 2 2 (CCZ234 ∷ CZ01 ∷ []) (c₂ (CZ) (CCZ)) ▸
       at 1 2 (CCZ234 ∷ CCZ013 ∷ []) (lem-cQ-at0310213442 c4) ▸
       at 2 4 (Toff301 ∷ []) (wl0520 (lit c4)) ▸ done


-- CXbc-box @0310213442: 17 steps
lem-CXbc-box-at0310213442 : Ws → ⟪ (CX14 ∷ Bx3-0142 ∷ CX14 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0142 ∷ CCZ012 ∷ []) ⟫ʷ
lem-CXbc-box-at0310213442 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX14 ∷ Bx3-0142 ∷ CX14 ∷ []) (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CX14 ∷ CCZ123 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CCZ234 ∷ CX01 ∷ CS02 ∷ CX14 ∷ [])
  b0 = at 1 1 (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ []) (lem-box-tQ-at0310213442 c4) ▸
       at 0 2 (Toff301 ∷ CX14 ∷ []) (wp1069 c4) ▸
       at 1 2 (CCZ234 ∷ CX14 ∷ CCZ123 ∷ []) (sym (wl1257 (lit c4))) ▸
       at 3 2 (Toff301 ∷ CCZ123 ∷ CCZ012 ∷ []) (wl1258 (lit c4)) ▸
       at 2 2 (Toff301 ∷ CX14 ∷ []) (wp1069 c4) ▸
       at 5 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wl0348 (lit c4)) ▸
       at 9 2 (CCZ234 ∷ CS02 ∷ []) (sym (wp0279 c4)) ▸
       at 8 2 (CCZ234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (CCZ)) ▸ done

  b1 : Chain (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CX14 ∷ CCZ123 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CCZ234 ∷ CX01 ∷ CS02 ∷ CX14 ∷ []) (Bx3-0142 ∷ CX14 ∷ CCZ012 ∷ CX14 ∷ [])
  b1 = at 7 2 (CCZ234 ∷ CS12⁻ ∷ []) (sym (wl0414 (lit c4))) ▸
       at 6 2 (CCZ234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (CCZ)) ▸
       at 5 2 (CCZ234 ∷ CS12 ∷ []) (sym (wl0415 (lit c4))) ▸
       at 6 5 (CCZ012 ∷ []) (sym (wl0348 (lit c4))) ▸
       at 4 2 (CCZ234 ∷ CCZ123 ∷ []) (wl0508 (lit c4)) ▸
       at 3 2 (CCZ234 ∷ CX14 ∷ CCZ123 ∷ []) (sym (wl1257 (lit c4))) ▸
       at 4 3 (CX14 ∷ []) (wl1259 (lit c4)) ▸
       at 0 4 (Bx3-0142 ∷ []) (sym (lem-box-tQ-at0310213442 c4)) ▸ done

  b2 : Chain (Bx3-0142 ∷ CX14 ∷ CCZ012 ∷ CX14 ∷ []) (Bx3-0142 ∷ CCZ012 ∷ [])
  b2 = at 1 3 (CCZ012 ∷ []) (sym (wp0728 c4)) ▸ done


-- CXcb-box @0310213442: 18 steps
lem-CXcb-box-at0310213442 : Ws → ⟪ (CX41 ∷ Bx3-0142 ∷ CX41 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0142 ∷ CCZ024 ∷ []) ⟫ʷ
lem-CXcb-box-at0310213442 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX41 ∷ Bx3-0142 ∷ CX41 ∷ []) (Toff301 ∷ CCZ234 ∷ CX41 ∷ Toff304 ∷ CS24 ∷ CX04 ∷ Toff301 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ CCZ234 ∷ CX41 ∷ [])
  b0 = at 1 1 (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ []) (lem-box-tQ-at0310213442 c4) ▸
       at 0 2 (Toff301 ∷ CX41 ∷ Toff304 ∷ []) (wp1070 c4) ▸
       at 2 2 (CCZ234 ∷ Toff304 ∷ CCZ024 ∷ []) (sym (wp1071 c4)) ▸
       at 1 2 (CCZ234 ∷ CX41 ∷ []) (sym (wl0302 (lit c4))) ▸
       at 4 1 (CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ []) (wp0013 c4) ▸
       at 8 2 (Toff301 ∷ CS02 ∷ []) (wl1260 (lit c4)) ▸
       at 7 2 (Toff301 ∷ CX04 ∷ []) (wp1072 c4) ▸
       at 6 2 (Toff301 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-TOFF301 (lit c4)) ▸ done

  b1 : Chain (Toff301 ∷ CCZ234 ∷ CX41 ∷ Toff304 ∷ CS24 ∷ CX04 ∷ Toff301 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ CCZ234 ∷ CX41 ∷ []) (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ CX41 ∷ CCZ024 ∷ CX41 ∷ [])
  b1 = at 5 2 (Toff301 ∷ CX04 ∷ []) (wp1072 c4) ▸
       at 4 2 (Toff301 ∷ CS24 ∷ []) (lem-comm-CS24-TOFF301 (lit c4)) ▸
       at 5 5 (CCZ024 ∷ []) (sym (wp0013 c4)) ▸
       at 3 2 (Toff301 ∷ Toff304 ∷ []) (sym (wp1066 c4)) ▸
       at 2 2 (Toff301 ∷ CX41 ∷ Toff304 ∷ []) (wp1070 c4) ▸
       at 3 3 (CX41 ∷ []) (wp1073 c4) ▸
       at 4 2 (CCZ234 ∷ CCZ024 ∷ []) (wp0090 c4) ▸
       at 3 2 (CCZ234 ∷ CX41 ∷ []) (sym (wl0302 (lit c4))) ▸ done

  b2 : Chain (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ CX41 ∷ CCZ024 ∷ CX41 ∷ []) (Bx3-0142 ∷ CCZ024 ∷ [])
  b2 = at 0 4 (Bx3-0142 ∷ []) (sym (lem-box-tQ-at0310213442 c4)) ▸
       at 1 3 (CCZ024 ∷ []) (sym (wp0727 c4)) ▸ done

