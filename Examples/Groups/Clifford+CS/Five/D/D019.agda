{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D019 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0003 ; wl0006 ; wl0037 ; wl0038 ; wl0044 ; wl0045 ; wl0084 ; wl0085 ; wl0157 ; wl0159 ; wl0181 ; wl0185 ; wl0199 ; wl0204 ; wl0210 ; wl0220 ; wl0225 ; wl0226 ; wl0227 ; wl0228 ; wl0229 ; wl0230 ; wl0232 ; wl0234 ; wl0241 ; wl0244 ; wl0245 ; wl0246 ; wl0247 ; wl0254 ; wl0257 ; wl0259 ; wl0261 ; wl0263 ; wl0292 ; wl0293 ; wl0305 ; wl0311 ; wl0318 ; wl0321 ; wl0324 ; wl0326 ; wl0342 ; wl0411 ; wl0434 ; wl0435 ; wl0436 ; wl0437 ; wl0438 ; wl0439 ; wl0440 ; wl0441 ; wl0442 ; wl0443 ; wl0448 ; wl0450 ; wl0464 ; wl0617 ; wl0621 ; wl0645 ; wl0667 ; wl0668 ; wl0669 ; wl0670 ; wl0671 ; wl0672 ; wl0674 ; wl0675 ; wl0677 ; wl0698 ; wl0702 ; wl0704 ; wl0707 ; wl0729 ; wl0749 ; wl0750 ; wl0781 ; wl0782 ; wl0783 ; wl0784 ; wl0785 ; wl0786 ; wl0787 ; wl0788 ; wl0835 ; wl0846 ; wl0847 ; wl0848 ; wl0851 ; wl0868 ; wl0974 ; wl0992 ; wl1020 ; wl1021 ; wl1022 ; wl1037 ; wl1126 ; wl1166 ; wl1167 ; wl1168 ; wl1172 ; wl1173 ; wl1174 ; wl1175 ; wl1176 ; wl1177 ; wl1178 ; wl1179 ; wl1180 ; wl1181 ; wl1182 ; wl1183 ; wl1184 ; wl1185 ; wl1186 ; wl1187 ; wl1188 ; wl1189 ; wl1190 ; wp0006 ; wp0011 ; wp0020 ; wp0023 ; wp0034 ; wp0035 ; wp0036 ; wp0048 ; wp0054 ; wp0077 ; wp0078 ; wp0079 ; wp0080 ; wp0081 ; wp0087 ; wp0088 ; wp0089 ; wp0090 ; wp0092 ; wp0094 ; wp0095 ; wp0097 ; wp0112 ; wp0113 ; wp0114 ; wp0135 ; wp0161 ; wp0163 ; wp0172 ; wp0185 ; wp0189 ; wp0205 ; wp0213 ; wp0251 ; wp0312 ; wp0314 ; wp0393 ; wp0394 ; wp0513 ; wp0523 ; wp0540 ; wp0543 ; wp0574 ; wp0590 ; wp0591 ; wp0594 ; wp0596 ; wp0617 ; wp0647 ; wp0653 ; wp0655 ; wp0669 ; wp0703 ; wp0734 ; wp0740 ; wp0742 ; wp0743 ; wp0749 ; wp0771 ; wp0806 ; wp0814 ; wp0820 ; wp0842 ; wp0843 ; wp0845 ; wp0886 ; wp0898 ; wp0899 ; wp0900 ; wp0909 ; wp0970 ; wp0979 ; wp0980 ; wp0981 ; wp0982 ; wp0983 ; wp0984 ; wp0985 ; wp0986 ; wp0987 ; wp0988 ; wp0989 ; wp0990 ; wp0991 ; wp0992 ; wp0993 ; wp0994 ; wp0995 ; wp0996 ; wp0997 ; wp0998 ; wp0999 ; wp1000 ; wp1001 ; wp1002 ; wp1003 ; wp1004 ; wp1005 ; wp1006 ; wp1007 ; wp1008)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-box-cP-at122441)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-box-cP-at13213442 ; lem-cQ-at12243143 ; lem-sym-ab-at13213442 ; lem-sym-bc-at12243143)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-sym-ab-at233442 ; lem-sym-ab-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D007 using (lem-box-cP-at12213443 ; lem-box-perm-1423-at122441 ; lem-box-tQ-at12213443 ; lem-box-tQ-at14233241 ; lem-box-tQ-at143143 ; lem-pairs-at143143 ; lem-sym-bc-at14213243 ; lem-tP-at12213443)
open import Examples.Groups.Clifford+CS.Five.D.D015 using (lem-S2-SBOX⟨0·2·43·1⟩)
open import Examples.Groups.Clifford+CS.Five.D.D017 using (lem-sym-ab-at1441)
open import Examples.Groups.Clifford+CS.Five.D.D018 using (lem-SWbc-box-at12213443 ; lem-nat-SWbc-at12213443 ; lem-pairs-at233442)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CS13-CCZ024 ; lem-comm-CSd12-TOFF034 ; lem-comm-CSd13-CCZ024 ; lem-comm-CX14-CCZ023)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-CS12-TOFF034 ; lem-comm-CSd24-TOFF013 ; lem-comm-CZ14-CCZ023 ; lem-comm-CZ24-CCZ013 ; lem-comm-TOFF024-CSd13)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-CS24-CCZ013 ; lem-comm-CSd24-CCZ013 ; lem-comm-CSd24-TOFF301 ; lem-comm-CX42-CCZ013)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-comm-CCZ024-CX13 ; lem-comm-CS02-CCZ134 ; lem-comm-CS02-TOFF314 ; lem-comm-CSd02-CCZ134 ; lem-comm-CSd02-TOFF314 ; lem-comm-CSd14-TOFF302 ; lem-comm-CX31-TOFF024 ; lem-comm-CX41-CCZ023 ; lem-comm-SWAP23-BOX⟨0·41⟩ ; lem-comm-TOFF314-CSd02)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-comm-CCZ034-CX21 ; lem-comm-CX14-TOFF302 ; lem-comm-SWAP12-BOX⟨3·40⟩ ; lem-comm-TOFF013-CS24 ; lem-comm-TOFF013-CX24)
-- sym-bc @12213443: 2 steps
lem-sym-bc-at12213443 : Ws → ⟪ (Bx0-2143 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2413 ∷ []) ⟫ʷ
lem-sym-bc-at12213443 c4 = run b0
  where
  b0 : Chain (Bx0-2143 ∷ []) (Bx0-2413 ∷ [])
  b0 = at 0 1 (Sw14 ∷ Bx0-2143 ∷ Sw14 ∷ []) (sym (lem-SWbc-box-at12213443 c4)) ▸
       at 0 3 (Bx0-2413 ∷ []) (lem-nat-SWbc-at12213443 c4) ▸ done


-- box-perm-1324 @12213443: 1 steps
lem-box-perm-1324-at12213443 : Ws → ⟪ (Bx0-2143 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2413 ∷ []) ⟫ʷ
lem-box-perm-1324-at12213443 c4 = run b0
  where
  b0 : Chain (Bx0-2143 ∷ []) (Bx0-2413 ∷ [])
  b0 = at 0 1 (Bx0-2413 ∷ []) (lem-sym-bc-at12213443 c4) ▸ done


-- tP @12243143: 7 steps
lem-tP-at12243143 : Ws → ⟪ (Toff024 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ Toff024 ∷ []) ⟫ʷ
lem-tP-at12243143 c4 = run b0
  where
  b0 : Chain (Toff024 ∷ Toff013 ∷ []) (Toff013 ∷ Toff024 ∷ [])
  b0 = at 0 1 (K0 ∷ CCZ024 ∷ K0⁻ ∷ []) (sym (wp0078 c4)) ▸
       at 3 1 (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) (sym (wl0226 (lit c4))) ▸
       at 2 2 [] (wl0157 (lit c4)) ▸
       at 1 2 (CCZ013 ∷ CCZ024 ∷ []) (lem-cQ-at12243143 c4) ▸
       at 2 0 (K0⁻ ∷ K0 ∷ []) (sym (wl0157 (lit c4))) ▸
       at 0 3 (Toff013 ∷ []) (wl0226 (lit c4)) ▸
       at 1 3 (Toff024 ∷ []) (wp0078 c4) ▸ done


-- VPQ @12243143: 14 steps
lem-VPQ-at12243143 : Ws → ⟪ (Toff024 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ []) ⟫ʷ
lem-VPQ-at12243143 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff024 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ []) (CS13⁻ ∷ CS24⁻ ∷ S0 ∷ Toff013 ∷ Toff024 ∷ S0⁻ ∷ [])
  b0 = at 0 2 (CS24⁻ ∷ S0 ∷ Toff024 ∷ S0⁻ ∷ []) (sym (wp0079 c4)) ▸
       at 4 2 (CS13⁻ ∷ S0 ∷ Toff013 ∷ S0⁻ ∷ []) (sym (wl0227 (lit c4))) ▸
       at 3 2 (CS13⁻ ∷ S0⁻ ∷ []) (c₁ (S • S • S) (Swap ↑ • (CS • CS • CS) • Swap ↑)) ▸
       at 2 2 (CS13⁻ ∷ Toff024 ∷ []) (lem-comm-TOFF024-CSd13 (lit c4)) ▸
       at 1 2 (CS13⁻ ∷ S0 ∷ []) (c₁ (S) (Swap ↑ • (CS • CS • CS) • Swap ↑)) ▸
       at 0 2 (CS13⁻ ∷ CS24⁻ ∷ []) (sym (wl0228 (lit c4))) ▸
       at 4 2 [] (wl0159 (lit c4)) ▸
       at 3 2 (Toff013 ∷ Toff024 ∷ []) (lem-tP-at12243143 c4) ▸ done

  b1 : Chain (CS13⁻ ∷ CS24⁻ ∷ S0 ∷ Toff013 ∷ Toff024 ∷ S0⁻ ∷ []) (Toff013 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ [])
  b1 = at 4 0 (S0⁻ ∷ S0 ∷ []) (sym (wl0159 (lit c4))) ▸
       at 1 2 (S0 ∷ CS24⁻ ∷ []) (sym (c₁ (S) (Swap ↑ ↑ • ((CS • CS • CS) ↑) • Swap ↑ ↑))) ▸
       at 2 2 (Toff013 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-TOFF013 (lit c4)) ▸
       at 3 2 (S0⁻ ∷ CS24⁻ ∷ []) (sym (c₁ (S • S • S) (Swap ↑ ↑ • ((CS • CS • CS) ↑) • Swap ↑ ↑))) ▸
       at 0 4 (Toff013 ∷ CCZ013 ∷ []) (wl0227 (lit c4)) ▸
       at 2 4 (Toff024 ∷ CCZ024 ∷ []) (wp0079 c4) ▸ done


-- QVQ @12243143: 3 steps
lem-QVQ-at12243143 : Ws → ⟪ (CCZ013 ∷ Toff024 ∷ CCZ024 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ Toff024 ∷ CCZ024 ∷ Toff013 ∷ []) ⟫ʷ
lem-QVQ-at12243143 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ Toff024 ∷ CCZ024 ∷ CCZ013 ∷ []) (Toff013 ∷ Toff024 ∷ CCZ024 ∷ Toff013 ∷ [])
  b0 = at 0 0 (Toff013 ∷ Toff013 ∷ []) (sym (wl0229 (lit c4))) ▸
       at 1 4 (Toff024 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ []) (sym (lem-VPQ-at12243143 c4)) ▸
       at 4 2 [] (wl0230 (lit c4)) ▸ done


-- box-cP @12243143: 12 steps
lem-box-cP-at12243143 : Ws → ⟪ (Bx0-2413 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) ⟫ʷ
lem-box-cP-at12243143 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-2413 ∷ []) (CCZ024 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ CCZ012 ∷ Toff201 ∷ CZ23 ∷ Toff201 ∷ CCZ012 ∷ CZ23 ∷ [])
  b0 = at 0 1 (CCZ024 ∷ Toff024 ∷ Bx2-013 ∷ Toff024 ∷ CCZ024 ∷ Bx2-013 ∷ []) (refl) ▸
       at 2 1 (CCZ012 ∷ Toff201 ∷ Bx0-23 ∷ Toff201 ∷ CCZ012 ∷ Bx0-23 ∷ []) (refl) ▸
       at 4 1 (CZ23 ∷ []) (refl) ▸
       at 7 1 (CZ23 ∷ []) (refl) ▸
       at 2 6 (CCZ013 ∷ []) (wl0292 (lit c4)) ▸
       at 5 1 (CCZ012 ∷ Toff201 ∷ Bx0-23 ∷ Toff201 ∷ CCZ012 ∷ Bx0-23 ∷ []) (refl) ▸
       at 7 1 (CZ23 ∷ []) (refl) ▸
       at 10 1 (CZ23 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ024 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ CCZ012 ∷ Toff201 ∷ CZ23 ∷ Toff201 ∷ CCZ012 ∷ CZ23 ∷ []) (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ [])
  b1 = at 5 6 (CCZ013 ∷ []) (wl0292 (lit c4)) ▸
       at 2 4 (Toff013 ∷ Toff024 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-QVQ-at12243143 c4) ▸
       at 1 2 (Toff013 ∷ Toff024 ∷ []) (lem-tP-at12243143 c4) ▸
       at 2 2 [] (wp0080 c4) ▸ done


-- Xb-box @12243143: 18 steps
lem-Xb-box-at12243143 : Ws → ⟪ (X4 ∷ Bx0-2413 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2413 ∷ CCZ123 ∷ []) ⟫ʷ
lem-Xb-box-at12243143 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ Bx0-2413 ∷ X4 ∷ []) (CCZ024 ∷ Toff013 ∷ X4 ∷ CZ02 ∷ CS13 ∷ CX21 ∷ CCZ024 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ Toff013 ∷ X4 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at12243143 c4) ▸
       at 0 2 (CCZ024 ∷ X4 ∷ CZ02 ∷ []) (sym (wp0020 c4)) ▸
       at 2 2 (Toff013 ∷ CZ02 ∷ CCZ123 ∷ []) (wl0232 (lit c4)) ▸
       at 1 2 (Toff013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • Toff • Swap ↑ ↑) (X))) ▸
       at 4 1 (CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ []) (wl0326 (lit c4)) ▸
       at 8 2 (CCZ024 ∷ CS23 ∷ []) (sym (wp0092 c4)) ▸
       at 7 2 (CCZ024 ∷ CX21 ∷ []) (sym (wp0749 c4)) ▸
       at 6 2 (CCZ024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-CCZ024 (lit c4)) ▸ done

  b1 : Chain (CCZ024 ∷ Toff013 ∷ X4 ∷ CZ02 ∷ CS13 ∷ CX21 ∷ CCZ024 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ Toff013 ∷ X4 ∷ []) (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ X4 ∷ CCZ123 ∷ X4 ∷ [])
  b1 = at 5 2 (CCZ024 ∷ CX21 ∷ []) (sym (wp0749 c4)) ▸
       at 4 2 (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 (lit c4)) ▸
       at 5 5 (CCZ123 ∷ []) (sym (wl0326 (lit c4))) ▸
       at 3 2 (CCZ024 ∷ CZ02 ∷ []) (sym (wp0023 c4)) ▸
       at 2 2 (CCZ024 ∷ X4 ∷ CZ02 ∷ []) (sym (wp0020 c4)) ▸
       at 3 3 (X4 ∷ []) (wl0185 (lit c4)) ▸
       at 4 2 (Toff013 ∷ CCZ123 ∷ []) (wl0234 (lit c4)) ▸
       at 3 2 (Toff013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • Toff • Swap ↑ ↑) (X))) ▸ done

  b2 : Chain (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (Bx0-2413 ∷ CCZ123 ∷ [])
  b2 = at 0 4 (Bx0-2413 ∷ []) (sym (lem-box-cP-at12243143 c4)) ▸
       at 1 3 (CCZ123 ∷ []) (sym (wl0210 (lit c4))) ▸ done


-- box-perm-1324 @12243143: 1 steps
lem-box-perm-1324-at12243143 : Ws → ⟪ (Bx0-2413 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2143 ∷ []) ⟫ʷ
lem-box-perm-1324-at12243143 c4 = run b0
  where
  b0 : Chain (Bx0-2413 ∷ []) (Bx0-2143 ∷ [])
  b0 = at 0 1 (Bx0-2143 ∷ []) (lem-sym-bc-at12243143 c4) ▸ done


-- CKc-box @12213443: 61 steps
lem-CKc-box-at12213443 : Ws → ⟪ (Bx0-2143 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CK43 ∷ CCZ123 ∷ Bx0-2143 ∷ []) ⟫ʷ
lem-CKc-box-at12213443 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (run b7)))))))
  where
  b0 : Chain (Bx0-2143 ∷ CK43 ∷ []) (X4 ∷ Bx0-2143 ∷ CCZ123 ∷ K3 ∷ CK43 ∷ S4 ∷ CCZ123 ∷ X4 ∷ CCZ123 ∷ [])
  b0 = at 1 0 (CCZ123 ∷ CCZ123 ∷ []) (sym (wl0181 (lit c4))) ▸
       at 0 1 (Bx0-2413 ∷ []) (lem-box-perm-1324-at12213443 c4) ▸
       at 0 2 (X4 ∷ Bx0-2413 ∷ X4 ∷ []) (sym (lem-Xb-box-at12243143 c4)) ▸
       at 3 2 (CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ123 ∷ []) (sym (wl1172 (lit c4))) ▸
       at 2 2 (CCZ123 ∷ X4 ∷ []) (sym (c₄ (CCZ ↑) (X))) ▸
       at 3 2 (K3 ∷ CK43 ∷ S4 ∷ X4 ∷ []) (sym (wl0729 (lit c4))) ▸
       at 6 2 (CCZ123 ∷ X4 ∷ []) (sym (c₄ (CCZ ↑) (X))) ▸
       at 1 1 (Bx0-2143 ∷ []) (lem-box-perm-1324-at12243143 c4) ▸ done

  b1 : Chain (X4 ∷ Bx0-2143 ∷ CCZ123 ∷ K3 ∷ CK43 ∷ S4 ∷ CCZ123 ∷ X4 ∷ CCZ123 ∷ []) (X4 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ123 ∷ CCZ034 ∷ K3 ∷ CK43 ∷ S4 ∷ CCZ123 ∷ X4 ∷ CCZ123 ∷ [])
  b1 = at 1 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-box-tQ-at12213443 c4) ▸
       at 5 1 (CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ []) (wl0326 (lit c4)) ▸
       at 4 2 (CS13 ∷ CCZ034 ∷ []) (wp0312 c4) ▸
       at 5 2 (CX21 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX21 (lit c4)) ▸
       at 6 2 (CS13⁻ ∷ CCZ034 ∷ []) (wp0734 c4) ▸
       at 7 2 (CX21 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX21 (lit c4)) ▸
       at 8 2 (CS23 ∷ CCZ034 ∷ []) (wp0314 c4) ▸
       at 4 5 (CCZ123 ∷ []) (sym (wl0326 (lit c4))) ▸ done

  b2 : Chain (X4 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ123 ∷ CCZ034 ∷ K3 ∷ CK43 ∷ S4 ∷ CCZ123 ∷ X4 ∷ CCZ123 ∷ []) (X4 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ123 ∷ K3 ∷ Toff304 ∷ CCZ034 ∷ CZ03 ∷ CK43 ∷ CZ03 ∷ S4 ∷ CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CCZ034 ∷ CS23 ∷ X4 ∷ CCZ123 ∷ [])
  b2 = at 5 2 (K3 ∷ Toff304 ∷ CCZ034 ∷ CCZ034 ∷ []) (wp0979 c4) ▸
       at 8 2 (CZ03 ∷ CK43 ∷ CZ03 ∷ CCZ034 ∷ []) (wp0980 c4) ▸
       at 11 2 (S4 ∷ CCZ034 ∷ []) (wp0981 c4) ▸
       at 13 1 (CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ []) (wl0326 (lit c4)) ▸
       at 12 2 (CS13 ∷ CCZ034 ∷ []) (wp0312 c4) ▸
       at 13 2 (CX21 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX21 (lit c4)) ▸
       at 14 2 (CS13⁻ ∷ CCZ034 ∷ []) (wp0734 c4) ▸
       at 15 2 (CX21 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX21 (lit c4)) ▸ done

  b3 : Chain (X4 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ123 ∷ K3 ∷ Toff304 ∷ CCZ034 ∷ CZ03 ∷ CK43 ∷ CZ03 ∷ S4 ∷ CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CCZ034 ∷ CS23 ∷ X4 ∷ CCZ123 ∷ []) (X4 ∷ Toff012 ∷ CCZ034 ∷ CCZ123 ∷ K3 ∷ CK43 ∷ S4 ∷ CCZ123 ∷ Toff012 ∷ CCZ034 ∷ X4 ∷ CCZ123 ∷ [])
  b3 = at 16 2 (CS23 ∷ CCZ034 ∷ []) (wp0314 c4) ▸
       at 12 5 (CCZ123 ∷ []) (sym (wl0326 (lit c4))) ▸
       at 5 7 (K3 ∷ CK43 ∷ S4 ∷ []) (sym (wp0982 c4)) ▸
       at 3 2 (CCZ123 ∷ Toff012 ∷ []) (sym (wl0464 (lit c4))) ▸
       at 4 2 (K3 ∷ Toff012 ∷ []) (c₃ (Toff) (K)) ▸
       at 5 2 (CK43 ∷ Toff012 ∷ []) (c₃ (Toff) (CK₁₀)) ▸
       at 6 2 (S4 ∷ Toff012 ∷ []) (c₃ (Toff) (S ↑)) ▸
       at 7 2 (CCZ123 ∷ Toff012 ∷ []) (sym (wl0464 (lit c4))) ▸ done

  b4 : Chain (X4 ∷ Toff012 ∷ CCZ034 ∷ CCZ123 ∷ K3 ∷ CK43 ∷ S4 ∷ CCZ123 ∷ Toff012 ∷ CCZ034 ∷ X4 ∷ CCZ123 ∷ []) (X4 ∷ Toff012 ∷ CCZ123 ∷ K3 ∷ Toff304 ∷ CCZ034 ∷ CCZ034 ∷ CK43 ∷ S4 ∷ CCZ123 ∷ Toff012 ∷ CCZ034 ∷ X4 ∷ CCZ123 ∷ [])
  b4 = at 3 1 (CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ []) (wl0326 (lit c4)) ▸
       at 2 2 (CS13 ∷ CCZ034 ∷ []) (wp0312 c4) ▸
       at 3 2 (CX21 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX21 (lit c4)) ▸
       at 4 2 (CS13⁻ ∷ CCZ034 ∷ []) (wp0734 c4) ▸
       at 5 2 (CX21 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX21 (lit c4)) ▸
       at 6 2 (CS23 ∷ CCZ034 ∷ []) (wp0314 c4) ▸
       at 2 5 (CCZ123 ∷ []) (sym (wl0326 (lit c4))) ▸
       at 3 2 (K3 ∷ Toff304 ∷ CCZ034 ∷ CCZ034 ∷ []) (wp0979 c4) ▸ done

  b5 : Chain (X4 ∷ Toff012 ∷ CCZ123 ∷ K3 ∷ Toff304 ∷ CCZ034 ∷ CCZ034 ∷ CK43 ∷ S4 ∷ CCZ123 ∷ Toff012 ∷ CCZ034 ∷ X4 ∷ CCZ123 ∷ []) (X4 ∷ Toff012 ∷ CCZ123 ∷ K3 ∷ Toff304 ∷ CCZ034 ∷ CZ03 ∷ CK43 ∷ CZ03 ∷ S4 ∷ CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ X4 ∷ CCZ123 ∷ [])
  b5 = at 6 2 (CZ03 ∷ CK43 ∷ CZ03 ∷ CCZ034 ∷ []) (wp0980 c4) ▸
       at 9 2 (S4 ∷ CCZ034 ∷ []) (wp0981 c4) ▸
       at 11 1 (CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ []) (wl0326 (lit c4)) ▸
       at 10 2 (CS13 ∷ CCZ034 ∷ []) (wp0312 c4) ▸
       at 11 2 (CX21 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX21 (lit c4)) ▸
       at 12 2 (CS13⁻ ∷ CCZ034 ∷ []) (wp0734 c4) ▸
       at 13 2 (CX21 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX21 (lit c4)) ▸
       at 14 2 (CS23 ∷ CCZ034 ∷ []) (wp0314 c4) ▸ done

  b6 : Chain (X4 ∷ Toff012 ∷ CCZ123 ∷ K3 ∷ Toff304 ∷ CCZ034 ∷ CZ03 ∷ CK43 ∷ CZ03 ∷ S4 ∷ CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ X4 ∷ CCZ123 ∷ []) (X4 ∷ CCZ123 ∷ K3 ∷ CK43 ∷ S4 ∷ CCZ123 ∷ Bx0-2143 ∷ X4 ∷ CCZ123 ∷ [])
  b6 = at 10 5 (CCZ123 ∷ []) (sym (wl0326 (lit c4))) ▸
       at 3 7 (K3 ∷ CK43 ∷ S4 ∷ []) (sym (wp0982 c4)) ▸
       at 1 2 (CCZ123 ∷ Toff012 ∷ []) (sym (wl0464 (lit c4))) ▸
       at 2 2 (K3 ∷ Toff012 ∷ []) (c₃ (Toff) (K)) ▸
       at 3 2 (CK43 ∷ Toff012 ∷ []) (c₃ (Toff) (CK₁₀)) ▸
       at 4 2 (S4 ∷ Toff012 ∷ []) (c₃ (Toff) (S ↑)) ▸
       at 5 2 (CCZ123 ∷ Toff012 ∷ []) (sym (wl0464 (lit c4))) ▸
       at 6 4 (Bx0-2143 ∷ []) (sym (lem-box-tQ-at12213443 c4)) ▸ done

  b7 : Chain (X4 ∷ CCZ123 ∷ K3 ∷ CK43 ∷ S4 ∷ CCZ123 ∷ Bx0-2143 ∷ X4 ∷ CCZ123 ∷ []) (CCZ123 ∷ CK43 ∷ CCZ123 ∷ Bx0-2143 ∷ [])
  b7 = at 6 1 (Bx0-2413 ∷ []) (sym (lem-box-perm-1324-at12243143 c4)) ▸
       at 0 6 (CCZ123 ∷ CK43 ∷ CCZ123 ∷ X4 ∷ []) (sym (wl1173 (lit c4))) ▸
       at 3 3 (Bx0-2413 ∷ CCZ123 ∷ []) (lem-Xb-box-at12243143 c4) ▸
       at 4 2 [] (wl0181 (lit c4)) ▸
       at 3 1 (Bx0-2143 ∷ []) (lem-box-perm-1324-at12243143 c4) ▸ done


-- P-box @12213443: 8 steps
lem-P-box-at12213443 : Ws → ⟪ (Toff034 ∷ Bx0-2143 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2143 ∷ []) ⟫ʷ
lem-P-box-at12213443 c4 = run b0
  where
  b0 : Chain (Toff034 ∷ Bx0-2143 ∷ Toff034 ∷ []) (Bx0-2143 ∷ [])
  b0 = at 1 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-box-tQ-at12213443 c4) ▸
       at 0 2 (Toff012 ∷ Toff034 ∷ []) (sym (lem-tP-at12213443 c4)) ▸
       at 1 2 (CCZ034 ∷ CZ34 ∷ Toff034 ∷ []) (sym (wp0112 c4)) ▸
       at 3 2 (Toff012 ∷ Toff034 ∷ []) (sym (lem-tP-at12213443 c4)) ▸
       at 4 3 (CCZ034 ∷ CZ34 ∷ []) (sym (wp0113 c4)) ▸
       at 2 2 (Toff012 ∷ CZ34 ∷ []) (sym (c₃ (Toff) (CZ))) ▸
       at 3 3 (CCZ034 ∷ []) (sym (wp0114 c4)) ▸
       at 0 4 (Bx0-2143 ∷ []) (sym (lem-box-tQ-at12213443 c4)) ▸ done


-- pairs @12213443: 4 steps
lem-pairs-at12213443 : Ws → ⟪ (Bx0-2143 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4321 ∷ []) ⟫ʷ
lem-pairs-at12213443 c4 = run b0
  where
  b0 : Chain (Bx0-2143 ∷ []) (Bx0-4321 ∷ [])
  b0 = at 0 1 (Toff034 ∷ Bx0-2143 ∷ Toff034 ∷ []) (sym (lem-P-box-at12213443 c4)) ▸
       at 1 1 (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ []) (lem-box-cP-at12213443 c4) ▸
       at 4 2 [] (wp0006 c4) ▸
       at 0 4 (Bx0-4321 ∷ []) (sym (lem-box-tQ-at14233241 c4)) ▸ done


-- CXbc-box @14233241: 17 steps
lem-CXbc-box-at14233241 : Ws → ⟪ (CX32 ∷ Bx0-4321 ∷ CX32 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4321 ∷ CCZ134 ∷ []) ⟫ʷ
lem-CXbc-box-at14233241 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX32 ∷ Bx0-4321 ∷ CX32 ∷ []) (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CX32 ∷ CCZ013 ∷ CS13 ∷ CX43 ∷ CS13⁻ ∷ CCZ012 ∷ CX43 ∷ CS14 ∷ CX32 ∷ [])
  b0 = at 1 1 (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ []) (lem-box-tQ-at14233241 c4) ▸
       at 0 2 (Toff034 ∷ CX32 ∷ []) (wp0172 c4) ▸
       at 1 2 (CCZ012 ∷ CX32 ∷ CCZ013 ∷ []) (sym (wl1174 (lit c4))) ▸
       at 3 2 (Toff034 ∷ CCZ013 ∷ CCZ134 ∷ []) (wp0771 c4) ▸
       at 2 2 (Toff034 ∷ CX32 ∷ []) (wp0172 c4) ▸
       at 5 1 (CS13 ∷ CX43 ∷ CS13⁻ ∷ CX43 ∷ CS14 ∷ []) (wl0707 (lit c4)) ▸
       at 9 2 (CCZ012 ∷ CS14 ∷ []) (sym (wp0011 c4)) ▸
       at 8 2 (CCZ012 ∷ CX43 ∷ []) (sym (c₃ (CCZ) (CX₁₀))) ▸ done

  b1 : Chain (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CX32 ∷ CCZ013 ∷ CS13 ∷ CX43 ∷ CS13⁻ ∷ CCZ012 ∷ CX43 ∷ CS14 ∷ CX32 ∷ []) (Bx0-4321 ∷ CX32 ∷ CCZ134 ∷ CX32 ∷ [])
  b1 = at 7 2 (CCZ012 ∷ CS13⁻ ∷ []) (sym (wl0992 (lit c4))) ▸
       at 6 2 (CCZ012 ∷ CX43 ∷ []) (sym (c₃ (CCZ) (CX₁₀))) ▸
       at 5 2 (CCZ012 ∷ CS13 ∷ []) (sym (wl0311 (lit c4))) ▸
       at 6 5 (CCZ134 ∷ []) (sym (wl0707 (lit c4))) ▸
       at 4 2 (CCZ012 ∷ CCZ013 ∷ []) (sym (wl0704 (lit c4))) ▸
       at 3 2 (CCZ012 ∷ CX32 ∷ CCZ013 ∷ []) (sym (wl1174 (lit c4))) ▸
       at 4 3 (CX32 ∷ []) (wl1175 (lit c4)) ▸
       at 0 4 (Bx0-4321 ∷ []) (sym (lem-box-tQ-at14233241 c4)) ▸ done

  b2 : Chain (Bx0-4321 ∷ CX32 ∷ CCZ134 ∷ CX32 ∷ []) (Bx0-4321 ∷ CCZ134 ∷ [])
  b2 = at 1 3 (CCZ134 ∷ []) (sym (wl0254 (lit c4))) ▸ done


-- CXcb-box @14233241: 18 steps
lem-CXcb-box-at14233241 : Ws → ⟪ (CX23 ∷ Bx0-4321 ∷ CX23 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4321 ∷ CCZ124 ∷ []) ⟫ʷ
lem-CXcb-box-at14233241 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX23 ∷ Bx0-4321 ∷ CX23 ∷ []) (Toff034 ∷ CCZ012 ∷ CX23 ∷ Toff024 ∷ CS12 ∷ CX42 ∷ Toff034 ∷ CS12⁻ ∷ CX42 ∷ CS14 ∷ CCZ012 ∷ CX23 ∷ [])
  b0 = at 1 1 (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ []) (lem-box-tQ-at14233241 c4) ▸
       at 0 2 (Toff034 ∷ CX23 ∷ Toff024 ∷ []) (wp0983 c4) ▸
       at 2 2 (CCZ012 ∷ Toff024 ∷ CCZ124 ∷ []) (sym (wp0984 c4)) ▸
       at 1 2 (CCZ012 ∷ CX23 ∷ []) (sym (wl0411 (lit c4))) ▸
       at 4 1 (CS12 ∷ CX42 ∷ CS12⁻ ∷ CX42 ∷ CS14 ∷ []) (wl0702 (lit c4)) ▸
       at 8 2 (Toff034 ∷ CS14 ∷ []) (wp0251 c4) ▸
       at 7 2 (Toff034 ∷ CX42 ∷ []) (wp0163 c4) ▸
       at 6 2 (Toff034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-TOFF034 (lit c4)) ▸ done

  b1 : Chain (Toff034 ∷ CCZ012 ∷ CX23 ∷ Toff024 ∷ CS12 ∷ CX42 ∷ Toff034 ∷ CS12⁻ ∷ CX42 ∷ CS14 ∷ CCZ012 ∷ CX23 ∷ []) (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ CX23 ∷ CCZ124 ∷ CX23 ∷ [])
  b1 = at 5 2 (Toff034 ∷ CX42 ∷ []) (wp0163 c4) ▸
       at 4 2 (Toff034 ∷ CS12 ∷ []) (lem-comm-CS12-TOFF034 (lit c4)) ▸
       at 5 5 (CCZ124 ∷ []) (sym (wl0702 (lit c4))) ▸
       at 3 2 (Toff034 ∷ Toff024 ∷ []) (wp0591 c4) ▸
       at 2 2 (Toff034 ∷ CX23 ∷ Toff024 ∷ []) (wp0983 c4) ▸
       at 3 3 (CX23 ∷ []) (wp0985 c4) ▸
       at 4 2 (CCZ012 ∷ CCZ124 ∷ []) (sym (wp0205 c4)) ▸
       at 3 2 (CCZ012 ∷ CX23 ∷ []) (sym (wl0411 (lit c4))) ▸ done

  b2 : Chain (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ CX23 ∷ CCZ124 ∷ CX23 ∷ []) (Bx0-4321 ∷ CCZ124 ∷ [])
  b2 = at 0 4 (Bx0-4321 ∷ []) (sym (lem-box-tQ-at14233241 c4)) ▸
       at 1 3 (CCZ124 ∷ []) (sym (wl0257 (lit c4))) ▸ done


-- SWbc-box @14233241: 11 steps
lem-SWbc-box-at14233241 : Ws → ⟪ (Sw23 ∷ Bx0-4321 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4321 ∷ []) ⟫ʷ
lem-SWbc-box-at14233241 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw23 ∷ Bx0-4321 ∷ Sw23 ∷ []) (CX32 ∷ Bx0-4321 ∷ CX32 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ [])
  b0 = at 0 1 (CX32 ∷ CX23 ∷ CX32 ∷ []) (sym (wl1020 (lit c4))) ▸
       at 4 1 (CX32 ∷ CX23 ∷ CX32 ∷ []) (sym (wl1020 (lit c4))) ▸
       at 2 3 (Bx0-4321 ∷ CCZ134 ∷ []) (lem-CXbc-box-at14233241 c4) ▸
       at 3 2 (CX23 ∷ CCZ124 ∷ CCZ134 ∷ []) (wl0261 (lit c4)) ▸
       at 1 3 (Bx0-4321 ∷ CCZ124 ∷ []) (lem-CXcb-box-at14233241 c4) ▸
       at 4 2 (CX32 ∷ CCZ134 ∷ []) (wl1021 (lit c4)) ▸
       at 3 2 (CX32 ∷ CCZ134 ∷ CCZ124 ∷ []) (wl0259 (lit c4)) ▸
       at 2 2 (CX32 ∷ CCZ134 ∷ CCZ124 ∷ []) (wl0259 (lit c4)) ▸ done

  b1 : Chain (CX32 ∷ Bx0-4321 ∷ CX32 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ []) (Bx0-4321 ∷ [])
  b1 = at 3 5 (CCZ134 ∷ []) (wl1022 (lit c4)) ▸
       at 0 3 (Bx0-4321 ∷ CCZ134 ∷ []) (lem-CXbc-box-at14233241 c4) ▸
       at 1 2 [] (wl0321 (lit c4)) ▸ done


-- nat-SWbc @14233241: 23 steps
lem-nat-SWbc-at14233241 : Ws → ⟪ (Sw23 ∷ Bx0-4321 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4231 ∷ []) ⟫ʷ
lem-nat-SWbc-at14233241 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw23 ∷ Bx0-4321 ∷ Sw23 ∷ []) (CCZ024 ∷ Toff024 ∷ CCZ034 ∷ Toff403 ∷ Bx0-41 ∷ Toff403 ∷ Sw23 ∷ CCZ024 ∷ Bx0-41 ∷ Toff034 ∷ CCZ034 ∷ Bx4-021 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff034 ∷ Bx4-021 ∷ Toff034 ∷ CCZ034 ∷ Bx4-021 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw23 ∷ []) (sym (wp0596 c4)) ▸
       at 1 2 (Toff024 ∷ Sw23 ∷ []) (wp0986 c4) ▸
       at 3 1 (CCZ024 ∷ Toff402 ∷ Bx0-41 ∷ Toff402 ∷ CCZ024 ∷ Bx0-41 ∷ []) (refl) ▸
       at 2 2 (CCZ034 ∷ Sw23 ∷ []) (sym (wp0594 c4)) ▸
       at 3 2 (Toff403 ∷ Sw23 ∷ []) (wp0987 c4) ▸
       at 4 2 (Bx0-41 ∷ Sw23 ∷ []) (lem-comm-SWAP23-BOX⟨0·41⟩ (lit c4)) ▸
       at 5 2 (Toff403 ∷ Sw23 ∷ []) (wp0987 c4) ▸ done

  b1 : Chain (CCZ024 ∷ Toff024 ∷ CCZ034 ∷ Toff403 ∷ Bx0-41 ∷ Toff403 ∷ Sw23 ∷ CCZ024 ∷ Bx0-41 ∷ Toff034 ∷ CCZ034 ∷ Bx4-021 ∷ Sw23 ∷ []) (CCZ024 ∷ Toff024 ∷ CCZ034 ∷ Toff403 ∷ Bx0-41 ∷ Toff403 ∷ CCZ034 ∷ Bx0-41 ∷ Toff024 ∷ CCZ024 ∷ CCZ034 ∷ Toff403 ∷ Bx0-41 ∷ Sw23 ∷ Toff402 ∷ CCZ024 ∷ Bx0-41 ∷ Sw23 ∷ [])
  b1 = at 6 2 (CCZ034 ∷ Sw23 ∷ []) (sym (wp0594 c4)) ▸
       at 7 2 (Bx0-41 ∷ Sw23 ∷ []) (lem-comm-SWAP23-BOX⟨0·41⟩ (lit c4)) ▸
       at 8 2 (Toff024 ∷ Sw23 ∷ []) (wp0986 c4) ▸
       at 9 2 (CCZ024 ∷ Sw23 ∷ []) (sym (wp0596 c4)) ▸
       at 11 1 (CCZ024 ∷ Toff402 ∷ Bx0-41 ∷ Toff402 ∷ CCZ024 ∷ Bx0-41 ∷ []) (refl) ▸
       at 10 2 (CCZ034 ∷ Sw23 ∷ []) (sym (wp0594 c4)) ▸
       at 11 2 (Toff403 ∷ Sw23 ∷ []) (wp0987 c4) ▸
       at 12 2 (Bx0-41 ∷ Sw23 ∷ []) (lem-comm-SWAP23-BOX⟨0·41⟩ (lit c4)) ▸ done

  b2 : Chain (CCZ024 ∷ Toff024 ∷ CCZ034 ∷ Toff403 ∷ Bx0-41 ∷ Toff403 ∷ CCZ034 ∷ Bx0-41 ∷ Toff024 ∷ CCZ024 ∷ CCZ034 ∷ Toff403 ∷ Bx0-41 ∷ Sw23 ∷ Toff402 ∷ CCZ024 ∷ Bx0-41 ∷ Sw23 ∷ []) (Bx0-4231 ∷ [])
  b2 = at 13 2 (Toff403 ∷ Sw23 ∷ []) (wp0987 c4) ▸
       at 14 2 (CCZ034 ∷ Sw23 ∷ []) (sym (wp0594 c4)) ▸
       at 15 2 (Bx0-41 ∷ Sw23 ∷ []) (lem-comm-SWAP23-BOX⟨0·41⟩ (lit c4)) ▸
       at 16 2 [] (wl0003 (lit c4)) ▸
       at 2 6 (Bx4-031 ∷ []) (refl) ▸
       at 5 6 (Bx4-031 ∷ []) (refl) ▸
       at 0 6 (Bx0-4231 ∷ []) (refl) ▸ done


-- sym-bc @14233241: 2 steps
lem-sym-bc-at14233241 : Ws → ⟪ (Bx0-4321 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4231 ∷ []) ⟫ʷ
lem-sym-bc-at14233241 c4 = run b0
  where
  b0 : Chain (Bx0-4321 ∷ []) (Bx0-4231 ∷ [])
  b0 = at 0 1 (Sw23 ∷ Bx0-4321 ∷ Sw23 ∷ []) (sym (lem-SWbc-box-at14233241 c4)) ▸
       at 0 3 (Bx0-4231 ∷ []) (lem-nat-SWbc-at14233241 c4) ▸ done


-- box-perm-1342 @12213443: 3 steps
lem-box-perm-1342-at12213443 : Ws → ⟪ (Bx0-2143 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ []) ⟫ʷ
lem-box-perm-1342-at12213443 c4 = run b0
  where
  b0 : Chain (Bx0-2143 ∷ []) (Bx0-2431 ∷ [])
  b0 = at 0 1 (Bx0-4321 ∷ []) (lem-pairs-at12213443 c4) ▸
       at 0 1 (Bx0-4231 ∷ []) (lem-sym-bc-at14233241 c4) ▸
       at 0 1 (Bx0-2431 ∷ []) (lem-sym-ab-at1441 c4) ▸ done


-- nf-X-CS1@2: 115 steps
lem-nf-X-CS1at2 : Ws → ⟪ (Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ CCZ123 ∷ S4 ∷ CS24 ∷ Bx0-2431 ∷ []) ⟫ʷ
lem-nf-X-CS1at2 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (run b14))))))))))))))
  where
  b0 : Chain (Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ CS24 ∷ []) (CCZ234 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ CCZ024 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ CS24 ∷ [])
  b0 = at 0 2 (CCZ234 ∷ []) (lem-S2-SBOX⟨0·2·43·1⟩ c4) ▸
       at 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 3 1 (CS12 ∷ []) (refl) ▸
       at 5 1 (CS12⁻ ∷ []) (refl) ▸
       at 1 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 4 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp0843 c4) ▸
       at 3 2 (Toff034 ∷ CCZ234 ∷ CCZ024 ∷ []) (wp0845 c4) ▸
       at 6 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸ done

  b1 : Chain (CCZ234 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ CCZ024 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ CS24 ∷ []) (CCZ234 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ CS24 ∷ [])
  b1 = at 5 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸
       at 6 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 7 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 8 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 9 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 10 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 11 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 5 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸ done

  b2 : Chain (CCZ234 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ CS24 ∷ []) (CCZ234 ∷ CCZ024 ∷ Toff034 ∷ CCZ234 ∷ Toff013 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ CS24 ∷ [])
  b2 = at 2 2 (Toff034 ∷ Toff013 ∷ []) (wp0097 c4) ▸
       at 4 1 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (wl0245 (lit c4)) ▸
       at 3 2 (CS34 ∷ Toff013 ∷ []) (sym (wp0095 c4)) ▸
       at 4 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 5 2 (CS34⁻ ∷ Toff013 ∷ []) (sym (wp0094 c4)) ▸
       at 6 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 7 2 (CS23 ∷ Toff013 ∷ []) (sym (wl0246 (lit c4))) ▸
       at 3 5 (CCZ234 ∷ []) (sym (wl0245 (lit c4))) ▸ done

  b3 : Chain (CCZ234 ∷ CCZ024 ∷ Toff034 ∷ CCZ234 ∷ Toff013 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ CS24 ∷ []) (CCZ234 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CCZ024 ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ CS24 ∷ [])
  b3 = at 4 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp0843 c4) ▸
       at 2 3 (CCZ234 ∷ []) (sym (wp0842 c4)) ▸
       at 1 2 (CCZ234 ∷ CCZ024 ∷ []) (wp0090 c4) ▸
       at 3 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 2 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸
       at 3 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 4 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 5 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸ done

  b4 : Chain (CCZ234 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CCZ024 ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ CS24 ∷ []) (CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12⁻ ∷ CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ CS24 ∷ [])
  b4 = at 6 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 7 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 8 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 2 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 3 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 3 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 6 2 (CS12 ∷ Toff013 ∷ []) (sym (wl0247 (lit c4))) ▸
       at 5 2 (CS12 ∷ CCZ024 ∷ []) (wp0081 c4) ▸ done

  b5 : Chain (CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12⁻ ∷ CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ CS24 ∷ []) (CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ K1 ∷ CCZ024 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CS12⁻ ∷ CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ CS24 ∷ [])
  b5 = at 4 2 (CS12 ∷ Toff013 ∷ []) (sym (wl0247 (lit c4))) ▸
       at 3 2 (CS12 ∷ CCZ024 ∷ []) (wp0081 c4) ▸
       at 4 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 4 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 7 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp0843 c4) ▸
       at 6 2 (Toff034 ∷ CCZ234 ∷ CCZ024 ∷ []) (wp0845 c4) ▸
       at 9 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 8 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸ done

  b6 : Chain (CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ K1 ∷ CCZ024 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CS12⁻ ∷ CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ CS24 ∷ []) (CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff034 ∷ Toff013 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ CS24 ∷ [])
  b6 = at 9 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 10 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 11 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 12 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 13 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 14 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 8 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 5 2 (Toff034 ∷ Toff013 ∷ []) (wp0097 c4) ▸ done

  b7 : Chain (CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff034 ∷ Toff013 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ CS24 ∷ []) (CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff034 ∷ CCZ234 ∷ Toff034 ∷ Toff134 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ CS24 ∷ [])
  b7 = at 7 1 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (wl0245 (lit c4)) ▸
       at 6 2 (CS34 ∷ Toff013 ∷ []) (sym (wp0095 c4)) ▸
       at 7 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 8 2 (CS34⁻ ∷ Toff013 ∷ []) (sym (wp0094 c4)) ▸
       at 9 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 10 2 (CS23 ∷ Toff013 ∷ []) (sym (wl0246 (lit c4))) ▸
       at 6 5 (CCZ234 ∷ []) (sym (wl0245 (lit c4))) ▸
       at 7 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp0843 c4) ▸ done

  b8 : Chain (CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff034 ∷ CCZ234 ∷ Toff034 ∷ Toff134 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ CS24 ∷ []) (CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ CS24 ∷ [])
  b8 = at 5 3 (CCZ234 ∷ []) (sym (wp0842 c4)) ▸
       at 4 2 (CCZ234 ∷ CCZ024 ∷ []) (wp0090 c4) ▸
       at 6 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 5 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸
       at 6 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 7 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 8 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 9 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸ done

  b9 : Chain (CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ CS24 ∷ []) (CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ CS12⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ CS24 ∷ [])
  b9 = at 10 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 11 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 5 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 6 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 6 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 9 2 (CS12⁻ ∷ Toff013 ∷ []) (sym (wl0244 (lit c4))) ▸
       at 8 2 (CS12⁻ ∷ CCZ024 ∷ []) (wp0087 c4) ▸
       at 7 2 (CS12⁻ ∷ Toff013 ∷ []) (sym (wl0244 (lit c4))) ▸ done

  b10 : Chain (CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ CS12⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ CS24 ∷ []) (CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ024 ∷ Toff013 ∷ CS34 ∷ CCZ024 ∷ Toff013 ∷ CS34 ∷ CK43 ∷ S4 ∷ CS24 ∷ [])
  b10 = at 6 2 (CS12⁻ ∷ CCZ024 ∷ []) (wp0087 c4) ▸
       at 7 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 7 1 (Bx0-2143 ∷ []) (lem-box-perm-1423-at122441 c4) ▸
       at 7 2 (CCZ123 ∷ CK43 ∷ CCZ123 ∷ Bx0-2143 ∷ []) (lem-CKc-box-at12213443 c4) ▸
       at 10 1 (Bx0-2431 ∷ []) (lem-box-perm-1342-at12213443 c4) ▸
       at 10 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 13 2 (CS34 ∷ Toff013 ∷ []) (sym (wp0095 c4)) ▸
       at 12 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸ done

  b11 : Chain (CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ024 ∷ Toff013 ∷ CS34 ∷ CCZ024 ∷ Toff013 ∷ CS34 ∷ CK43 ∷ S4 ∷ CS24 ∷ []) (CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CS34 ∷ CS34 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CK43 ∷ S4 ∷ CS24 ∷ [])
  b11 = at 11 2 (CS34 ∷ Toff013 ∷ []) (sym (wp0095 c4)) ▸
       at 10 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 11 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 11 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 14 2 (CS34 ∷ Toff013 ∷ []) (sym (wp0095 c4)) ▸
       at 13 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 12 2 (CS34 ∷ Toff013 ∷ []) (sym (wp0095 c4)) ▸
       at 11 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸ done

  b12 : Chain (CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CS34 ∷ CS34 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CK43 ∷ S4 ∷ CS24 ∷ []) (CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CS34 ∷ CS34 ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ024 ∷ S4 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS24 ∷ [])
  b12 = at 12 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 12 1 (Bx0-2143 ∷ []) (lem-box-perm-1423-at122441 c4) ▸
       at 12 2 (CCZ123 ∷ CK43 ∷ CCZ123 ∷ Bx0-2143 ∷ []) (lem-CKc-box-at12213443 c4) ▸
       at 15 1 (Bx0-2431 ∷ []) (lem-box-perm-1342-at12213443 c4) ▸
       at 15 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 18 2 (S4 ∷ Toff013 ∷ []) (sym (wp0647 c4)) ▸
       at 17 2 (S4 ∷ CCZ024 ∷ []) (wp0617 c4) ▸
       at 16 2 (S4 ∷ Toff013 ∷ []) (sym (wp0647 c4)) ▸ done

  b13 : Chain (CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CS34 ∷ CS34 ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ024 ∷ S4 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS24 ∷ []) (CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CS34 ∷ CS34 ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ S4 ∷ CS24 ∷ Bx0-2431 ∷ [])
  b13 = at 15 2 (S4 ∷ CCZ024 ∷ []) (wp0617 c4) ▸
       at 16 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 16 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 19 2 (CS24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CS24 (lit c4)) ▸
       at 18 2 (CS24 ∷ CCZ024 ∷ []) (wp0909 c4) ▸
       at 17 2 (CS24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CS24 (lit c4)) ▸
       at 16 2 (CS24 ∷ CCZ024 ∷ []) (wp0909 c4) ▸
       at 17 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸ done

  b14 : Chain (CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ CS34 ∷ CS34 ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ S4 ∷ CS24 ∷ Bx0-2431 ∷ []) (Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ CCZ123 ∷ S4 ∷ CS24 ∷ Bx0-2431 ∷ [])
  b14 = at 0 2 [] (wl0305 (lit c4)) ▸
       at 7 3 (CS34 ∷ CS34 ∷ CCZ123 ∷ []) (wl1176 (lit c4)) ▸
       at 9 2 [] (wl0181 (lit c4)) ▸ done


-- F1-X-CS1@2: 86 steps
lem-F1-X-CS1at2 : Ws → ⟪ (CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ CS24 ∷ []) ⟫ʷ
lem-F1-X-CS1at2 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (run b10))))))))))
  where
  b0 : Chain (CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ Sb0-2-43-1 ∷ []) (CX43 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ CCZ024 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b0 = at 5 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 7 1 (CS12 ∷ []) (refl) ▸
       at 9 1 (CS12⁻ ∷ []) (refl) ▸
       at 0 5 (CX43 ∷ []) (wl1177 (lit c4)) ▸
       at 1 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 4 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp0843 c4) ▸
       at 3 2 (Toff034 ∷ CCZ234 ∷ CCZ024 ∷ []) (wp0845 c4) ▸
       at 6 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸ done

  b1 : Chain (CX43 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ CCZ024 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (CX43 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b1 = at 5 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸
       at 6 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 7 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 8 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 9 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 10 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 11 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 5 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸ done

  b2 : Chain (CX43 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (CX43 ∷ CCZ024 ∷ Toff034 ∷ CCZ234 ∷ Toff013 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b2 = at 2 2 (Toff034 ∷ Toff013 ∷ []) (wp0097 c4) ▸
       at 4 1 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (wl0245 (lit c4)) ▸
       at 3 2 (CS34 ∷ Toff013 ∷ []) (sym (wp0095 c4)) ▸
       at 4 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 5 2 (CS34⁻ ∷ Toff013 ∷ []) (sym (wp0094 c4)) ▸
       at 6 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 7 2 (CS23 ∷ Toff013 ∷ []) (sym (wl0246 (lit c4))) ▸
       at 3 5 (CCZ234 ∷ []) (sym (wl0245 (lit c4))) ▸ done

  b3 : Chain (CX43 ∷ CCZ024 ∷ Toff034 ∷ CCZ234 ∷ Toff013 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (CX43 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CCZ024 ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b3 = at 4 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp0843 c4) ▸
       at 2 3 (CCZ234 ∷ []) (sym (wp0842 c4)) ▸
       at 1 2 (CCZ234 ∷ CCZ024 ∷ []) (wp0090 c4) ▸
       at 3 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 2 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸
       at 3 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 4 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 5 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸ done

  b4 : Chain (CX43 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CCZ024 ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (CX43 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b4 = at 6 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 7 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 8 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 2 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 3 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 3 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 6 2 (CS12 ∷ Toff013 ∷ []) (sym (wl0247 (lit c4))) ▸
       at 5 2 (CS12 ∷ CCZ024 ∷ []) (wp0081 c4) ▸ done

  b5 : Chain (CX43 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12⁻ ∷ []) (CX43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ K1 ∷ CCZ024 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CS12⁻ ∷ [])
  b5 = at 4 2 (CS12 ∷ Toff013 ∷ []) (sym (wl0247 (lit c4))) ▸
       at 3 2 (CS12 ∷ CCZ024 ∷ []) (wp0081 c4) ▸
       at 4 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 4 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 7 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp0843 c4) ▸
       at 6 2 (Toff034 ∷ CCZ234 ∷ CCZ024 ∷ []) (wp0845 c4) ▸
       at 9 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 8 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸ done

  b6 : Chain (CX43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ K1 ∷ CCZ024 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CS12⁻ ∷ []) (CX43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff034 ∷ Toff013 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ [])
  b6 = at 9 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 10 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 11 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 12 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 13 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 14 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 8 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 5 2 (Toff034 ∷ Toff013 ∷ []) (wp0097 c4) ▸ done

  b7 : Chain (CX43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff034 ∷ Toff013 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ []) (CX43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff034 ∷ CCZ234 ∷ Toff034 ∷ Toff134 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ [])
  b7 = at 7 1 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (wl0245 (lit c4)) ▸
       at 6 2 (CS34 ∷ Toff013 ∷ []) (sym (wp0095 c4)) ▸
       at 7 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 8 2 (CS34⁻ ∷ Toff013 ∷ []) (sym (wp0094 c4)) ▸
       at 9 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 10 2 (CS23 ∷ Toff013 ∷ []) (sym (wl0246 (lit c4))) ▸
       at 6 5 (CCZ234 ∷ []) (sym (wl0245 (lit c4))) ▸
       at 7 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp0843 c4) ▸ done

  b8 : Chain (CX43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff034 ∷ CCZ234 ∷ Toff034 ∷ Toff134 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ []) (CX43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ [])
  b8 = at 5 3 (CCZ234 ∷ []) (sym (wp0842 c4)) ▸
       at 4 2 (CCZ234 ∷ CCZ024 ∷ []) (wp0090 c4) ▸
       at 6 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 5 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸
       at 6 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 7 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 8 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 9 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸ done

  b9 : Chain (CX43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ []) (CX43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ CS12⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ [])
  b9 = at 10 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 11 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 5 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 6 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 6 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 9 2 (CS12⁻ ∷ Toff013 ∷ []) (sym (wl0244 (lit c4))) ▸
       at 8 2 (CS12⁻ ∷ CCZ024 ∷ []) (wp0087 c4) ▸
       at 7 2 (CS12⁻ ∷ Toff013 ∷ []) (sym (wl0244 (lit c4))) ▸ done

  b10 : Chain (CX43 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ CS12⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ CS24 ∷ [])
  b10 = at 6 2 (CS12⁻ ∷ CCZ024 ∷ []) (wp0087 c4) ▸
       at 7 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 1 3 (Toff134 ∷ CS12 ∷ CCZ234 ∷ []) (wl1037 (lit c4)) ▸
       at 3 2 [] (wl0305 (lit c4)) ▸
       at 0 5 (Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ CCZ123 ∷ S4 ∷ CS24 ∷ []) (wl1178 (lit c4)) ▸
       at 0 14 (Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ CS24 ∷ []) (sym (lem-nf-X-CS1at2 c4)) ▸ done


-- box-perm-2314 @243243: 2 steps
lem-box-perm-2314-at243243 : Ws → ⟪ (Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4213 ∷ []) ⟫ʷ
lem-box-perm-2314-at243243 c4 = run b0
  where
  b0 : Chain (Bx0-1423 ∷ []) (Bx0-4213 ∷ [])
  b0 = at 0 1 (Bx0-4123 ∷ []) (lem-sym-ab-at243243 c4) ▸
       at 0 1 (Bx0-4213 ∷ []) (lem-sym-bc-at14213243 c4) ▸ done


-- cQ @03143140: 7 steps
lem-cQ-at03143140 : Ws → ⟪ (CCZ234 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ CCZ234 ∷ []) ⟫ʷ
lem-cQ-at03143140 c4 = run b0
  where
  b0 : Chain (CCZ234 ∷ CCZ013 ∷ []) (CCZ013 ∷ CCZ234 ∷ [])
  b0 = at 0 1 (CS23 ∷ CX42 ∷ CS23⁻ ∷ CX42 ∷ CS34 ∷ []) (wl0675 (lit c4)) ▸
       at 4 2 (CCZ013 ∷ CS34 ∷ []) (sym (wp0185 c4)) ▸
       at 3 2 (CCZ013 ∷ CX42 ∷ []) (lem-comm-CX42-CCZ013 (lit c4)) ▸
       at 2 2 (CCZ013 ∷ CS23⁻ ∷ []) (sym (wl1167 (lit c4))) ▸
       at 1 2 (CCZ013 ∷ CX42 ∷ []) (lem-comm-CX42-CCZ013 (lit c4)) ▸
       at 0 2 (CCZ013 ∷ CS23 ∷ []) (sym (wl0324 (lit c4))) ▸
       at 1 5 (CCZ234 ∷ []) (sym (wl0675 (lit c4))) ▸ done


-- box-tQ @03143140: 13 steps
lem-box-tQ-at03143140 : Ws → ⟪ (Bx3-4210 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ []) ⟫ʷ
lem-box-tQ-at03143140 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-4210 ∷ []) (CCZ234 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ234 ∷ CCZ134 ∷ Toff413 ∷ CZ04 ∷ Toff413 ∷ CCZ134 ∷ CZ04 ∷ [])
  b0 = at 0 1 (CCZ234 ∷ Toff324 ∷ Bx4-310 ∷ Toff324 ∷ CCZ234 ∷ Bx4-310 ∷ []) (refl) ▸
       at 2 1 (CCZ134 ∷ Toff413 ∷ Bx3-40 ∷ Toff413 ∷ CCZ134 ∷ Bx3-40 ∷ []) (refl) ▸
       at 4 1 (CZ04 ∷ []) (refl) ▸
       at 7 1 (CZ04 ∷ []) (refl) ▸
       at 2 6 (CCZ013 ∷ []) (sym (wp0988 c4)) ▸
       at 5 1 (CCZ134 ∷ Toff413 ∷ Bx3-40 ∷ Toff413 ∷ CCZ134 ∷ Bx3-40 ∷ []) (refl) ▸
       at 7 1 (CZ04 ∷ []) (refl) ▸
       at 10 1 (CZ04 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ234 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ234 ∷ CCZ134 ∷ Toff413 ∷ CZ04 ∷ Toff413 ∷ CCZ134 ∷ CZ04 ∷ []) (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ [])
  b1 = at 5 6 (CCZ013 ∷ []) (sym (wp0988 c4)) ▸
       at 0 2 (Toff324 ∷ CCZ234 ∷ CZ24 ∷ []) (wl0846 (lit c4)) ▸
       at 2 2 (CCZ013 ∷ CZ24 ∷ []) (lem-comm-CZ24-CCZ013 (lit c4)) ▸
       at 1 2 (CCZ013 ∷ CCZ234 ∷ []) (lem-cQ-at03143140 c4) ▸
       at 2 4 (Toff324 ∷ []) (wl0847 (lit c4)) ▸ done


-- CXbc-box @03143140: 17 steps
lem-CXbc-box-at03143140 : Ws → ⟪ (CX21 ∷ Bx3-4210 ∷ CX21 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4210 ∷ CCZ024 ∷ []) ⟫ʷ
lem-CXbc-box-at03143140 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX21 ∷ Bx3-4210 ∷ CX21 ∷ []) (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CX21 ∷ CCZ023 ∷ CS02 ∷ CX42 ∷ CS02⁻ ∷ CCZ013 ∷ CX42 ∷ CS04 ∷ CX21 ∷ [])
  b0 = at 1 1 (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ []) (lem-box-tQ-at03143140 c4) ▸
       at 0 2 (Toff324 ∷ CX21 ∷ []) (wl0851 (lit c4)) ▸
       at 1 2 (CCZ013 ∷ CX21 ∷ CCZ023 ∷ []) (sym (wl1166 (lit c4))) ▸
       at 3 2 (Toff324 ∷ CCZ023 ∷ CCZ024 ∷ []) (wp0989 c4) ▸
       at 2 2 (Toff324 ∷ CX21 ∷ []) (wl0851 (lit c4)) ▸
       at 5 1 (CS02 ∷ CX42 ∷ CS02⁻ ∷ CX42 ∷ CS04 ∷ []) (wp0213 c4) ▸
       at 9 2 (CCZ013 ∷ CS04 ∷ []) (sym (wp0077 c4)) ▸
       at 8 2 (CCZ013 ∷ CX42 ∷ []) (lem-comm-CX42-CCZ013 (lit c4)) ▸ done

  b1 : Chain (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CX21 ∷ CCZ023 ∷ CS02 ∷ CX42 ∷ CS02⁻ ∷ CCZ013 ∷ CX42 ∷ CS04 ∷ CX21 ∷ []) (Bx3-4210 ∷ CX21 ∷ CCZ024 ∷ CX21 ∷ [])
  b1 = at 7 2 (CCZ013 ∷ CS02⁻ ∷ []) (sym (wl0342 (lit c4))) ▸
       at 6 2 (CCZ013 ∷ CX42 ∷ []) (lem-comm-CX42-CCZ013 (lit c4)) ▸
       at 5 2 (CCZ013 ∷ CS02 ∷ []) (sym (wl0225 (lit c4))) ▸
       at 6 5 (CCZ024 ∷ []) (sym (wp0213 c4)) ▸
       at 4 2 (CCZ013 ∷ CCZ023 ∷ []) (sym (wl0671 (lit c4))) ▸
       at 3 2 (CCZ013 ∷ CX21 ∷ CCZ023 ∷ []) (sym (wl1166 (lit c4))) ▸
       at 4 3 (CX21 ∷ []) (wl1168 (lit c4)) ▸
       at 0 4 (Bx3-4210 ∷ []) (sym (lem-box-tQ-at03143140 c4)) ▸ done

  b2 : Chain (Bx3-4210 ∷ CX21 ∷ CCZ024 ∷ CX21 ∷ []) (Bx3-4210 ∷ CCZ024 ∷ [])
  b2 = at 1 3 (CCZ024 ∷ []) (sym (wp0898 c4)) ▸ done


-- CXcb-box @03143140: 18 steps
lem-CXcb-box-at03143140 : Ws → ⟪ (CX12 ∷ Bx3-4210 ∷ CX12 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4210 ∷ CCZ014 ∷ []) ⟫ʷ
lem-CXcb-box-at03143140 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX12 ∷ Bx3-4210 ∷ CX12 ∷ []) (Toff324 ∷ CCZ013 ∷ CX12 ∷ Toff314 ∷ CS01 ∷ CX41 ∷ Toff324 ∷ CS01⁻ ∷ CX41 ∷ CS04 ∷ CCZ013 ∷ CX12 ∷ [])
  b0 = at 1 1 (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ []) (lem-box-tQ-at03143140 c4) ▸
       at 0 2 (Toff324 ∷ CX12 ∷ Toff314 ∷ []) (wl1179 (lit c4)) ▸
       at 2 2 (CCZ013 ∷ Toff314 ∷ CCZ014 ∷ []) (sym (wp0990 c4)) ▸
       at 1 2 (CCZ013 ∷ CX12 ∷ []) (sym (wl0448 (lit c4))) ▸
       at 4 1 (CS01 ∷ CX41 ∷ CS01⁻ ∷ CX41 ∷ CS04 ∷ []) (wp0540 c4) ▸
       at 8 2 (Toff324 ∷ CS04 ∷ []) (wp0393 c4) ▸
       at 7 2 (Toff324 ∷ CX41 ∷ []) (wl0848 (lit c4)) ▸
       at 6 2 (Toff324 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (K ↑ • CCZ • K ↑ • iI)) ▸ done

  b1 : Chain (Toff324 ∷ CCZ013 ∷ CX12 ∷ Toff314 ∷ CS01 ∷ CX41 ∷ Toff324 ∷ CS01⁻ ∷ CX41 ∷ CS04 ∷ CCZ013 ∷ CX12 ∷ []) (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ CX12 ∷ CCZ014 ∷ CX12 ∷ [])
  b1 = at 5 2 (Toff324 ∷ CX41 ∷ []) (wl0848 (lit c4)) ▸
       at 4 2 (Toff324 ∷ CS01 ∷ []) (c₂ (CS) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 5 5 (CCZ014 ∷ []) (sym (wp0540 c4)) ▸
       at 3 2 (Toff324 ∷ Toff314 ∷ []) (wl1180 (lit c4)) ▸
       at 2 2 (Toff324 ∷ CX12 ∷ Toff314 ∷ []) (wl1179 (lit c4)) ▸
       at 3 3 (CX12 ∷ []) (wl1181 (lit c4)) ▸
       at 4 2 (CCZ013 ∷ CCZ014 ∷ []) (sym (wp0394 c4)) ▸
       at 3 2 (CCZ013 ∷ CX12 ∷ []) (sym (wl0448 (lit c4))) ▸ done

  b2 : Chain (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ CX12 ∷ CCZ014 ∷ CX12 ∷ []) (Bx3-4210 ∷ CCZ014 ∷ [])
  b2 = at 0 4 (Bx3-4210 ∷ []) (sym (lem-box-tQ-at03143140 c4)) ▸
       at 1 3 (CCZ014 ∷ []) (sym (wp0655 c4)) ▸ done


-- SWbc-box @03143140: 11 steps
lem-SWbc-box-at03143140 : Ws → ⟪ (Sw12 ∷ Bx3-4210 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4210 ∷ []) ⟫ʷ
lem-SWbc-box-at03143140 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw12 ∷ Bx3-4210 ∷ Sw12 ∷ []) (CX21 ∷ Bx3-4210 ∷ CX21 ∷ CCZ024 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ024 ∷ [])
  b0 = at 0 1 (CX21 ∷ CX12 ∷ CX21 ∷ []) (sym (wl0835 (lit c4))) ▸
       at 4 1 (CX21 ∷ CX12 ∷ CX21 ∷ []) (sym (wl0835 (lit c4))) ▸
       at 2 3 (Bx3-4210 ∷ CCZ024 ∷ []) (lem-CXbc-box-at03143140 c4) ▸
       at 3 2 (CX12 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp0653 c4) ▸
       at 1 3 (Bx3-4210 ∷ CCZ014 ∷ []) (lem-CXcb-box-at03143140 c4) ▸
       at 4 2 (CX21 ∷ CCZ024 ∷ []) (wp0749 c4) ▸
       at 3 2 (CX21 ∷ CCZ024 ∷ CCZ014 ∷ []) (wp0899 c4) ▸
       at 2 2 (CX21 ∷ CCZ024 ∷ CCZ014 ∷ []) (wp0899 c4) ▸ done

  b1 : Chain (CX21 ∷ Bx3-4210 ∷ CX21 ∷ CCZ024 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ024 ∷ []) (Bx3-4210 ∷ [])
  b1 = at 3 5 (CCZ024 ∷ []) (wp0991 c4) ▸
       at 0 3 (Bx3-4210 ∷ CCZ024 ∷ []) (lem-CXbc-box-at03143140 c4) ▸
       at 1 2 [] (wp0135 c4) ▸ done


-- nat-SWbc @03143140: 23 steps
lem-nat-SWbc-at03143140 : Ws → ⟪ (Sw12 ∷ Bx3-4210 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4120 ∷ []) ⟫ʷ
lem-nat-SWbc-at03143140 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw12 ∷ Bx3-4210 ∷ Sw12 ∷ []) (CCZ134 ∷ Toff314 ∷ CCZ234 ∷ Toff423 ∷ Bx3-40 ∷ Toff423 ∷ Sw12 ∷ CCZ134 ∷ Bx3-40 ∷ Toff324 ∷ CCZ234 ∷ Bx4-310 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff324 ∷ Bx4-310 ∷ Toff324 ∷ CCZ234 ∷ Bx4-310 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0037 (lit c4))) ▸
       at 1 2 (Toff314 ∷ Sw12 ∷ []) (wl0038 (lit c4)) ▸
       at 3 1 (CCZ134 ∷ Toff413 ∷ Bx3-40 ∷ Toff413 ∷ CCZ134 ∷ Bx3-40 ∷ []) (refl) ▸
       at 2 2 (CCZ234 ∷ Sw12 ∷ []) (sym (wl0044 (lit c4))) ▸
       at 3 2 (Toff423 ∷ Sw12 ∷ []) (wl0084 (lit c4)) ▸
       at 4 2 (Bx3-40 ∷ Sw12 ∷ []) (lem-comm-SWAP12-BOX⟨3·40⟩ (lit c4)) ▸
       at 5 2 (Toff423 ∷ Sw12 ∷ []) (wl0084 (lit c4)) ▸ done

  b1 : Chain (CCZ134 ∷ Toff314 ∷ CCZ234 ∷ Toff423 ∷ Bx3-40 ∷ Toff423 ∷ Sw12 ∷ CCZ134 ∷ Bx3-40 ∷ Toff324 ∷ CCZ234 ∷ Bx4-310 ∷ Sw12 ∷ []) (CCZ134 ∷ Toff314 ∷ CCZ234 ∷ Toff423 ∷ Bx3-40 ∷ Toff423 ∷ CCZ234 ∷ Bx3-40 ∷ Toff314 ∷ CCZ134 ∷ CCZ234 ∷ Toff423 ∷ Bx3-40 ∷ Sw12 ∷ Toff413 ∷ CCZ134 ∷ Bx3-40 ∷ Sw12 ∷ [])
  b1 = at 6 2 (CCZ234 ∷ Sw12 ∷ []) (sym (wl0044 (lit c4))) ▸
       at 7 2 (Bx3-40 ∷ Sw12 ∷ []) (lem-comm-SWAP12-BOX⟨3·40⟩ (lit c4)) ▸
       at 8 2 (Toff314 ∷ Sw12 ∷ []) (wl0038 (lit c4)) ▸
       at 9 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0037 (lit c4))) ▸
       at 11 1 (CCZ134 ∷ Toff413 ∷ Bx3-40 ∷ Toff413 ∷ CCZ134 ∷ Bx3-40 ∷ []) (refl) ▸
       at 10 2 (CCZ234 ∷ Sw12 ∷ []) (sym (wl0044 (lit c4))) ▸
       at 11 2 (Toff423 ∷ Sw12 ∷ []) (wl0084 (lit c4)) ▸
       at 12 2 (Bx3-40 ∷ Sw12 ∷ []) (lem-comm-SWAP12-BOX⟨3·40⟩ (lit c4)) ▸ done

  b2 : Chain (CCZ134 ∷ Toff314 ∷ CCZ234 ∷ Toff423 ∷ Bx3-40 ∷ Toff423 ∷ CCZ234 ∷ Bx3-40 ∷ Toff314 ∷ CCZ134 ∷ CCZ234 ∷ Toff423 ∷ Bx3-40 ∷ Sw12 ∷ Toff413 ∷ CCZ134 ∷ Bx3-40 ∷ Sw12 ∷ []) (Bx3-4120 ∷ [])
  b2 = at 13 2 (Toff423 ∷ Sw12 ∷ []) (wl0084 (lit c4)) ▸
       at 14 2 (CCZ234 ∷ Sw12 ∷ []) (sym (wl0044 (lit c4))) ▸
       at 15 2 (Bx3-40 ∷ Sw12 ∷ []) (lem-comm-SWAP12-BOX⟨3·40⟩ (lit c4)) ▸
       at 16 2 [] (wl0006 (lit c4)) ▸
       at 2 6 (Bx4-320 ∷ []) (refl) ▸
       at 5 6 (Bx4-320 ∷ []) (refl) ▸
       at 0 6 (Bx3-4120 ∷ []) (refl) ▸ done


-- sym-bc @03143140: 2 steps
lem-sym-bc-at03143140 : Ws → ⟪ (Bx3-4210 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4120 ∷ []) ⟫ʷ
lem-sym-bc-at03143140 c4 = run b0
  where
  b0 : Chain (Bx3-4210 ∷ []) (Bx3-4120 ∷ [])
  b0 = at 0 1 (Sw12 ∷ Bx3-4210 ∷ Sw12 ∷ []) (sym (lem-SWbc-box-at03143140 c4)) ▸
       at 0 3 (Bx3-4120 ∷ []) (lem-nat-SWbc-at03143140 c4) ▸ done


-- box-perm-1324 @03143140: 1 steps
lem-box-perm-1324-at03143140 : Ws → ⟪ (Bx3-4210 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4120 ∷ []) ⟫ʷ
lem-box-perm-1324-at03143140 c4 = run b0
  where
  b0 : Chain (Bx3-4210 ∷ []) (Bx3-4120 ∷ [])
  b0 = at 0 1 (Bx3-4120 ∷ []) (lem-sym-bc-at03143140 c4) ▸ done


-- cQ @0314213240: 7 steps
lem-cQ-at0314213240 : Ws → ⟪ (CCZ134 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ CCZ134 ∷ []) ⟫ʷ
lem-cQ-at0314213240 c4 = run b0
  where
  b0 : Chain (CCZ134 ∷ CCZ023 ∷ []) (CCZ023 ∷ CCZ134 ∷ [])
  b0 = at 0 1 (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ []) (wl0617 (lit c4)) ▸
       at 4 2 (CCZ023 ∷ CS34 ∷ []) (sym (wp0543 c4)) ▸
       at 3 2 (CCZ023 ∷ CX41 ∷ []) (lem-comm-CX41-CCZ023 (lit c4)) ▸
       at 2 2 (CCZ023 ∷ CS13⁻ ∷ []) (sym (wl0669 (lit c4))) ▸
       at 1 2 (CCZ023 ∷ CX41 ∷ []) (lem-comm-CX41-CCZ023 (lit c4)) ▸
       at 0 2 (CCZ023 ∷ CS13 ∷ []) (sym (wl0670 (lit c4))) ▸
       at 1 5 (CCZ134 ∷ []) (sym (wl0617 (lit c4))) ▸ done


-- tP @0314213240: 7 steps
lem-tP-at0314213240 : Ws → ⟪ (Toff314 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ Toff314 ∷ []) ⟫ʷ
lem-tP-at0314213240 c4 = run b0
  where
  b0 : Chain (Toff314 ∷ Toff302 ∷ []) (Toff302 ∷ Toff314 ∷ [])
  b0 = at 0 1 (K3 ∷ CCZ134 ∷ K3⁻ ∷ []) (sym (wl0781 (lit c4))) ▸
       at 3 1 (K3 ∷ CCZ023 ∷ K3⁻ ∷ []) (sym (wl0782 (lit c4))) ▸
       at 2 2 [] (wl0436 (lit c4)) ▸
       at 1 2 (CCZ023 ∷ CCZ134 ∷ []) (lem-cQ-at0314213240 c4) ▸
       at 2 0 (K3⁻ ∷ K3 ∷ []) (sym (wl0436 (lit c4))) ▸
       at 0 3 (Toff302 ∷ []) (wl0782 (lit c4)) ▸
       at 1 3 (Toff314 ∷ []) (wl0781 (lit c4)) ▸ done


-- VPQ @0314213240: 14 steps
lem-VPQ-at0314213240 : Ws → ⟪ (Toff314 ∷ CCZ134 ∷ Toff302 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ []) ⟫ʷ
lem-VPQ-at0314213240 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff314 ∷ CCZ134 ∷ Toff302 ∷ CCZ023 ∷ []) (CS02⁻ ∷ CS14⁻ ∷ S3 ∷ Toff302 ∷ Toff314 ∷ S3⁻ ∷ [])
  b0 = at 0 2 (CS14⁻ ∷ S3 ∷ Toff314 ∷ S3⁻ ∷ []) (sym (wl0783 (lit c4))) ▸
       at 4 2 (CS02⁻ ∷ S3 ∷ Toff302 ∷ S3⁻ ∷ []) (sym (wl0784 (lit c4))) ▸
       at 3 2 (CS02⁻ ∷ S3⁻ ∷ []) (sym (c₃ (Swap ↑ • (CS • CS • CS) • Swap ↑) (S • S • S))) ▸
       at 2 2 (CS02⁻ ∷ Toff314 ∷ []) (lem-comm-TOFF314-CSd02 (lit c4)) ▸
       at 1 2 (CS02⁻ ∷ S3 ∷ []) (sym (c₃ (Swap ↑ • (CS • CS • CS) • Swap ↑) (S))) ▸
       at 0 2 (CS02⁻ ∷ CS14⁻ ∷ []) (sym (wp0703 c4)) ▸
       at 4 2 [] (wl0441 (lit c4)) ▸
       at 3 2 (Toff302 ∷ Toff314 ∷ []) (lem-tP-at0314213240 c4) ▸ done

  b1 : Chain (CS02⁻ ∷ CS14⁻ ∷ S3 ∷ Toff302 ∷ Toff314 ∷ S3⁻ ∷ []) (Toff302 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ [])
  b1 = at 4 0 (S3⁻ ∷ S3 ∷ []) (sym (wl0441 (lit c4))) ▸
       at 1 2 (S3 ∷ CS14⁻ ∷ []) (wl0785 (lit c4)) ▸
       at 2 2 (Toff302 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-TOFF302 (lit c4)) ▸
       at 3 2 (S3⁻ ∷ CS14⁻ ∷ []) (wl0786 (lit c4)) ▸
       at 0 4 (Toff302 ∷ CCZ023 ∷ []) (wl0784 (lit c4)) ▸
       at 2 4 (Toff314 ∷ CCZ134 ∷ []) (wl0783 (lit c4)) ▸ done


-- QVQ @0314213240: 3 steps
lem-QVQ-at0314213240 : Ws → ⟪ (CCZ023 ∷ Toff314 ∷ CCZ134 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ Toff314 ∷ CCZ134 ∷ Toff302 ∷ []) ⟫ʷ
lem-QVQ-at0314213240 c4 = run b0
  where
  b0 : Chain (CCZ023 ∷ Toff314 ∷ CCZ134 ∷ CCZ023 ∷ []) (Toff302 ∷ Toff314 ∷ CCZ134 ∷ Toff302 ∷ [])
  b0 = at 0 0 (Toff302 ∷ Toff302 ∷ []) (sym (wl0787 (lit c4))) ▸
       at 1 4 (Toff314 ∷ CCZ134 ∷ Toff302 ∷ CCZ023 ∷ []) (sym (lem-VPQ-at0314213240 c4)) ▸
       at 4 2 [] (wl0204 (lit c4)) ▸ done


-- box-cP @0314213240: 12 steps
lem-box-cP-at0314213240 : Ws → ⟪ (Bx3-4120 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) ⟫ʷ
lem-box-cP-at0314213240 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-4120 ∷ []) (CCZ134 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ CCZ234 ∷ Toff423 ∷ CZ04 ∷ Toff423 ∷ CCZ234 ∷ CZ04 ∷ [])
  b0 = at 0 1 (CCZ134 ∷ Toff314 ∷ Bx4-320 ∷ Toff314 ∷ CCZ134 ∷ Bx4-320 ∷ []) (refl) ▸
       at 2 1 (CCZ234 ∷ Toff423 ∷ Bx3-40 ∷ Toff423 ∷ CCZ234 ∷ Bx3-40 ∷ []) (refl) ▸
       at 4 1 (CZ04 ∷ []) (refl) ▸
       at 7 1 (CZ04 ∷ []) (refl) ▸
       at 2 6 (CCZ023 ∷ []) (sym (wp0992 c4)) ▸
       at 5 1 (CCZ234 ∷ Toff423 ∷ Bx3-40 ∷ Toff423 ∷ CCZ234 ∷ Bx3-40 ∷ []) (refl) ▸
       at 7 1 (CZ04 ∷ []) (refl) ▸
       at 10 1 (CZ04 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ134 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ CCZ234 ∷ Toff423 ∷ CZ04 ∷ Toff423 ∷ CCZ234 ∷ CZ04 ∷ []) (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ [])
  b1 = at 5 6 (CCZ023 ∷ []) (sym (wp0992 c4)) ▸
       at 2 4 (Toff302 ∷ Toff314 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-QVQ-at0314213240 c4) ▸
       at 1 2 (Toff302 ∷ Toff314 ∷ []) (lem-tP-at0314213240 c4) ▸
       at 2 2 [] (wl0788 (lit c4)) ▸ done


-- sym-ab @0314213240: 18 steps
lem-sym-ab-at0314213240 : Ws → ⟪ (Bx3-4120 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1420 ∷ []) ⟫ʷ
lem-sym-ab-at0314213240 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx3-4120 ∷ []) (CCZ134 ∷ Toff314 ∷ CCZ123 ∷ Toff123 ∷ Bx3-10 ∷ Toff123 ∷ CCZ123 ∷ Bx3-10 ∷ Toff314 ∷ CCZ134 ∷ Bx4-320 ∷ [])
  b0 = at 0 1 (CCZ134 ∷ Toff314 ∷ Bx4-320 ∷ Toff314 ∷ CCZ134 ∷ Bx4-320 ∷ []) (refl) ▸
       at 2 1 (CCZ234 ∷ Toff423 ∷ Bx3-40 ∷ Toff423 ∷ CCZ234 ∷ Bx3-40 ∷ []) (refl) ▸
       at 4 1 (CZ04 ∷ []) (refl) ▸
       at 7 1 (CZ04 ∷ []) (refl) ▸
       at 2 6 (CCZ023 ∷ []) (sym (wp0992 c4)) ▸
       at 2 1 (CCZ123 ∷ Toff123 ∷ CZ01 ∷ Toff123 ∷ CCZ123 ∷ CZ01 ∷ []) (wl1126 (lit c4)) ▸
       at 4 1 (Bx3-10 ∷ []) (refl) ▸
       at 7 1 (Bx3-10 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ134 ∷ Toff314 ∷ CCZ123 ∷ Toff123 ∷ Bx3-10 ∷ Toff123 ∷ CCZ123 ∷ Bx3-10 ∷ Toff314 ∷ CCZ134 ∷ Bx4-320 ∷ []) (CCZ134 ∷ Toff314 ∷ Bx1-320 ∷ Toff314 ∷ CCZ134 ∷ CCZ123 ∷ Toff123 ∷ Bx3-10 ∷ Toff123 ∷ CCZ123 ∷ Bx3-10 ∷ [])
  b1 = at 2 6 (Bx1-320 ∷ []) (refl) ▸
       at 5 1 (CCZ234 ∷ Toff423 ∷ Bx3-40 ∷ Toff423 ∷ CCZ234 ∷ Bx3-40 ∷ []) (refl) ▸
       at 7 1 (CZ04 ∷ []) (refl) ▸
       at 10 1 (CZ04 ∷ []) (refl) ▸
       at 5 6 (CCZ023 ∷ []) (sym (wp0992 c4)) ▸
       at 5 1 (CCZ123 ∷ Toff123 ∷ CZ01 ∷ Toff123 ∷ CCZ123 ∷ CZ01 ∷ []) (wl1126 (lit c4)) ▸
       at 7 1 (Bx3-10 ∷ []) (refl) ▸
       at 10 1 (Bx3-10 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ134 ∷ Toff314 ∷ Bx1-320 ∷ Toff314 ∷ CCZ134 ∷ CCZ123 ∷ Toff123 ∷ Bx3-10 ∷ Toff123 ∷ CCZ123 ∷ Bx3-10 ∷ []) (Bx3-1420 ∷ [])
  b2 = at 5 6 (Bx1-320 ∷ []) (refl) ▸
       at 0 6 (Bx3-1420 ∷ []) (refl) ▸ done


-- box-perm-3124 @03143140: 2 steps
lem-box-perm-3124-at03143140 : Ws → ⟪ (Bx3-4210 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1420 ∷ []) ⟫ʷ
lem-box-perm-3124-at03143140 c4 = run b0
  where
  b0 : Chain (Bx3-4210 ∷ []) (Bx3-1420 ∷ [])
  b0 = at 0 1 (Bx3-4120 ∷ []) (lem-sym-bc-at03143140 c4) ▸
       at 0 1 (Bx3-1420 ∷ []) (lem-sym-ab-at0314213240 c4) ▸ done


-- box-perm-4312 @143143: 2 steps
lem-box-perm-4312-at143143 : Ws → ⟪ (Bx0-4213 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3142 ∷ []) ⟫ʷ
lem-box-perm-4312-at143143 c4 = run b0
  where
  b0 : Chain (Bx0-4213 ∷ []) (Bx0-3142 ∷ [])
  b0 = at 0 1 (Bx0-1342 ∷ []) (lem-pairs-at143143 c4) ▸
       at 0 1 (Bx0-3142 ∷ []) (lem-sym-ab-at233442 c4) ▸ done


-- cQ @03243240: 7 steps
lem-cQ-at03243240 : Ws → ⟪ (CCZ134 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ CCZ134 ∷ []) ⟫ʷ
lem-cQ-at03243240 c4 = run b0
  where
  b0 : Chain (CCZ134 ∷ CCZ023 ∷ []) (CCZ023 ∷ CCZ134 ∷ [])
  b0 = at 0 1 (CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ []) (wl0698 (lit c4)) ▸
       at 4 2 (CCZ023 ∷ CS13 ∷ []) (sym (wl0670 (lit c4))) ▸
       at 3 2 (CCZ023 ∷ CX14 ∷ []) (lem-comm-CX14-CCZ023 (lit c4)) ▸
       at 2 2 (CCZ023 ∷ CS34⁻ ∷ []) (sym (wp0574 c4)) ▸
       at 1 2 (CCZ023 ∷ CX14 ∷ []) (lem-comm-CX14-CCZ023 (lit c4)) ▸
       at 0 2 (CCZ023 ∷ CS34 ∷ []) (sym (wp0543 c4)) ▸
       at 1 5 (CCZ134 ∷ []) (sym (wl0698 (lit c4))) ▸ done


-- box-tQ @03243240: 13 steps
lem-box-tQ-at03243240 : Ws → ⟪ (Bx3-1420 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ []) ⟫ʷ
lem-box-tQ-at03243240 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-1420 ∷ []) (CCZ134 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ CCZ123 ∷ Toff123 ∷ CZ01 ∷ Toff123 ∷ CCZ123 ∷ CZ01 ∷ [])
  b0 = at 0 1 (CCZ134 ∷ Toff314 ∷ Bx1-320 ∷ Toff314 ∷ CCZ134 ∷ Bx1-320 ∷ []) (refl) ▸
       at 2 1 (CCZ123 ∷ Toff123 ∷ Bx3-10 ∷ Toff123 ∷ CCZ123 ∷ Bx3-10 ∷ []) (refl) ▸
       at 4 1 (CZ01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 2 6 (CCZ023 ∷ []) (sym (wl1126 (lit c4))) ▸
       at 5 1 (CCZ123 ∷ Toff123 ∷ Bx3-10 ∷ Toff123 ∷ CCZ123 ∷ Bx3-10 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 10 1 (CZ01 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ134 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ CCZ123 ∷ Toff123 ∷ CZ01 ∷ Toff123 ∷ CCZ123 ∷ CZ01 ∷ []) (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ [])
  b1 = at 5 6 (CCZ023 ∷ []) (sym (wl1126 (lit c4))) ▸
       at 0 2 (Toff314 ∷ CCZ134 ∷ CZ14 ∷ []) (wl0749 (lit c4)) ▸
       at 2 2 (CCZ023 ∷ CZ14 ∷ []) (lem-comm-CZ14-CCZ023 (lit c4)) ▸
       at 1 2 (CCZ023 ∷ CCZ134 ∷ []) (lem-cQ-at03243240 c4) ▸
       at 2 4 (Toff314 ∷ []) (wl0750 (lit c4)) ▸ done


-- box-box-4 @03243240: 103 steps
lem-box-box-4-at03243240 : Ws → ⟪ (Bx3-1420 ∷ Bx0-3142 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3142 ∷ Bx3-1420 ∷ []) ⟫ʷ
lem-box-box-4-at03243240 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (run b12))))))))))))
  where
  b0 : Chain (Bx3-1420 ∷ Bx0-3142 ∷ []) (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ013 ∷ Toff024 ∷ CS24 ∷ CX34 ∷ CS24⁻ ∷ CCZ013 ∷ CX34 ∷ CS23 ∷ CCZ023 ∷ Toff024 ∷ [])
  b0 = at 0 1 (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ []) (lem-box-tQ-at03243240 c4) ▸
       at 4 1 (CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ []) (lem-box-cP-at13213442 c4) ▸
       at 3 2 (CCZ013 ∷ CCZ023 ∷ []) (sym (wl0671 (lit c4))) ▸
       at 4 2 (Toff024 ∷ CCZ234 ∷ CCZ023 ∷ []) (wp0993 c4) ▸
       at 6 2 (CCZ013 ∷ CCZ023 ∷ []) (sym (wl0671 (lit c4))) ▸
       at 5 1 (CS24 ∷ CX34 ∷ CS24⁻ ∷ CX34 ∷ CS23 ∷ []) (wl0293 (lit c4)) ▸
       at 9 2 (CCZ013 ∷ CS23 ∷ []) (sym (wl0324 (lit c4))) ▸
       at 8 2 (CCZ013 ∷ CX34 ∷ []) (sym (wp0523 c4)) ▸ done

  b1 : Chain (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ013 ∷ Toff024 ∷ CS24 ∷ CX34 ∷ CS24⁻ ∷ CCZ013 ∷ CX34 ∷ CS23 ∷ CCZ023 ∷ Toff024 ∷ []) (Toff314 ∷ CCZ023 ∷ CCZ013 ∷ Toff314 ∷ CCZ014 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ023 ∷ [])
  b1 = at 7 2 (CCZ013 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-CCZ013 (lit c4)) ▸
       at 6 2 (CCZ013 ∷ CX34 ∷ []) (sym (wp0523 c4)) ▸
       at 5 2 (CCZ013 ∷ CS24 ∷ []) (lem-comm-CS24-CCZ013 (lit c4)) ▸
       at 6 5 (CCZ234 ∷ []) (sym (wl0293 (lit c4))) ▸
       at 6 3 (Toff024 ∷ CCZ023 ∷ []) (wp0994 c4) ▸
       at 3 4 (Bx0-3142 ∷ []) (sym (lem-box-cP-at13213442 c4)) ▸
       at 3 1 (CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ []) (lem-box-cP-at13213442 c4) ▸
       at 2 2 (CCZ013 ∷ Toff314 ∷ CCZ014 ∷ []) (sym (wp0990 c4)) ▸ done

  b2 : Chain (Toff314 ∷ CCZ023 ∷ CCZ013 ∷ Toff314 ∷ CCZ014 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ023 ∷ []) (Toff314 ∷ CCZ023 ∷ CCZ013 ∷ K3 ∷ Toff024 ∷ CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ K3⁻ ∷ CCZ124 ∷ CCZ014 ∷ CCZ013 ∷ Toff024 ∷ CCZ023 ∷ [])
  b2 = at 4 2 (Toff024 ∷ CCZ124 ∷ CCZ014 ∷ []) (wp0806 c4) ▸
       at 3 1 (K3 ∷ CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ K3⁻ ∷ []) (sym (wl1182 (lit c4))) ▸
       at 9 2 (Toff024 ∷ K3⁻ ∷ []) (wp0740 c4) ▸
       at 8 2 (Toff024 ∷ CS34 ∷ []) (wp0970 c4) ▸
       at 7 2 (Toff024 ∷ CX31 ∷ []) (lem-comm-CX31-TOFF024 (lit c4)) ▸
       at 6 2 (Toff024 ∷ CS14⁻ ∷ []) (wp0995 c4) ▸
       at 5 2 (Toff024 ∷ CX31 ∷ []) (lem-comm-CX31-TOFF024 (lit c4)) ▸
       at 4 2 (Toff024 ∷ CS14 ∷ []) (wp0590 c4) ▸ done

  b3 : Chain (Toff314 ∷ CCZ023 ∷ CCZ013 ∷ K3 ∷ Toff024 ∷ CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ K3⁻ ∷ CCZ124 ∷ CCZ014 ∷ CCZ013 ∷ Toff024 ∷ CCZ023 ∷ []) (Toff314 ∷ CCZ023 ∷ CCZ013 ∷ Toff024 ∷ Toff314 ∷ CS24 ∷ CCZ013 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ CCZ014 ∷ Toff024 ∷ CCZ023 ∷ [])
  b3 = at 3 2 (Toff024 ∷ K3 ∷ []) (wp0742 c4) ▸
       at 4 7 (Toff314 ∷ []) (wl1182 (lit c4)) ▸
       at 6 2 (CCZ013 ∷ CCZ014 ∷ []) (sym (wp0394 c4)) ▸
       at 5 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 9 2 (CCZ013 ∷ CS12 ∷ []) (sym (wl0645 (lit c4))) ▸
       at 8 2 (CCZ013 ∷ CX14 ∷ []) (sym (wp0189 c4)) ▸
       at 7 2 (CCZ013 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-CCZ013 (lit c4)) ▸
       at 6 2 (CCZ013 ∷ CX14 ∷ []) (sym (wp0189 c4)) ▸ done

  b4 : Chain (Toff314 ∷ CCZ023 ∷ CCZ013 ∷ Toff024 ∷ Toff314 ∷ CS24 ∷ CCZ013 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ CCZ014 ∷ Toff024 ∷ CCZ023 ∷ []) (Toff314 ∷ CCZ023 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ K3 ∷ CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ Toff024 ∷ CS34 ∷ K3⁻ ∷ CCZ124 ∷ CCZ023 ∷ [])
  b4 = at 5 2 (CCZ013 ∷ CS24 ∷ []) (lem-comm-CS24-CCZ013 (lit c4)) ▸
       at 6 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 4 2 (CCZ013 ∷ Toff314 ∷ CCZ014 ∷ []) (sym (wp0990 c4)) ▸
       at 6 3 (CCZ124 ∷ []) (wp0996 c4) ▸
       at 6 2 (Toff024 ∷ CCZ124 ∷ []) (wp0743 c4) ▸
       at 5 1 (K3 ∷ CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ K3⁻ ∷ []) (sym (wl1182 (lit c4))) ▸
       at 11 2 (Toff024 ∷ K3⁻ ∷ []) (wp0740 c4) ▸
       at 10 2 (Toff024 ∷ CS34 ∷ []) (wp0970 c4) ▸ done

  b5 : Chain (Toff314 ∷ CCZ023 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ K3 ∷ CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ Toff024 ∷ CS34 ∷ K3⁻ ∷ CCZ124 ∷ CCZ023 ∷ []) (Toff314 ∷ CCZ023 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ Toff314 ∷ CCZ124 ∷ CCZ023 ∷ [])
  b5 = at 9 2 (Toff024 ∷ CX31 ∷ []) (lem-comm-CX31-TOFF024 (lit c4)) ▸
       at 8 2 (Toff024 ∷ CS14⁻ ∷ []) (wp0995 c4) ▸
       at 7 2 (Toff024 ∷ CX31 ∷ []) (lem-comm-CX31-TOFF024 (lit c4)) ▸
       at 6 2 (Toff024 ∷ CS14 ∷ []) (wp0590 c4) ▸
       at 5 2 (Toff024 ∷ K3 ∷ []) (wp0742 c4) ▸
       at 6 7 (Toff314 ∷ []) (wl1182 (lit c4)) ▸
       at 2 4 (Bx0-3142 ∷ []) (sym (lem-box-cP-at13213442 c4)) ▸
       at 2 1 (CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ []) (lem-box-cP-at13213442 c4) ▸ done

  b6 : Chain (Toff314 ∷ CCZ023 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ Toff314 ∷ CCZ124 ∷ CCZ023 ∷ []) (Toff314 ∷ CCZ013 ∷ Toff024 ∷ CS24 ∷ CCZ013 ∷ CX34 ∷ CS24⁻ ∷ CX34 ∷ CS23 ∷ CCZ023 ∷ Toff024 ∷ Toff314 ∷ CCZ124 ∷ CCZ023 ∷ [])
  b6 = at 1 2 (CCZ013 ∷ CCZ023 ∷ []) (sym (wl0671 (lit c4))) ▸
       at 2 2 (Toff024 ∷ CCZ234 ∷ CCZ023 ∷ []) (wp0993 c4) ▸
       at 4 2 (CCZ013 ∷ CCZ023 ∷ []) (sym (wl0671 (lit c4))) ▸
       at 3 1 (CS24 ∷ CX34 ∷ CS24⁻ ∷ CX34 ∷ CS23 ∷ []) (wl0293 (lit c4)) ▸
       at 7 2 (CCZ013 ∷ CS23 ∷ []) (sym (wl0324 (lit c4))) ▸
       at 6 2 (CCZ013 ∷ CX34 ∷ []) (sym (wp0523 c4)) ▸
       at 5 2 (CCZ013 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-CCZ013 (lit c4)) ▸
       at 4 2 (CCZ013 ∷ CX34 ∷ []) (sym (wp0523 c4)) ▸ done

  b7 : Chain (Toff314 ∷ CCZ013 ∷ Toff024 ∷ CS24 ∷ CCZ013 ∷ CX34 ∷ CS24⁻ ∷ CX34 ∷ CS23 ∷ CCZ023 ∷ Toff024 ∷ Toff314 ∷ CCZ124 ∷ CCZ023 ∷ []) (CCZ013 ∷ K3 ∷ CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ K3⁻ ∷ Toff024 ∷ CCZ124 ∷ CCZ014 ∷ CCZ013 ∷ Toff024 ∷ CCZ023 ∷ Toff314 ∷ CCZ124 ∷ CCZ023 ∷ [])
  b7 = at 3 2 (CCZ013 ∷ CS24 ∷ []) (lem-comm-CS24-CCZ013 (lit c4)) ▸
       at 4 5 (CCZ234 ∷ []) (sym (wl0293 (lit c4))) ▸
       at 4 3 (Toff024 ∷ CCZ023 ∷ []) (wp0994 c4) ▸
       at 1 4 (Bx0-3142 ∷ []) (sym (lem-box-cP-at13213442 c4)) ▸
       at 1 1 (CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ []) (lem-box-cP-at13213442 c4) ▸
       at 0 2 (CCZ013 ∷ Toff314 ∷ CCZ014 ∷ []) (sym (wp0990 c4)) ▸
       at 2 2 (Toff024 ∷ CCZ124 ∷ CCZ014 ∷ []) (wp0806 c4) ▸
       at 1 1 (K3 ∷ CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ K3⁻ ∷ []) (sym (wl1182 (lit c4))) ▸ done

  b8 : Chain (CCZ013 ∷ K3 ∷ CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ K3⁻ ∷ Toff024 ∷ CCZ124 ∷ CCZ014 ∷ CCZ013 ∷ Toff024 ∷ CCZ023 ∷ Toff314 ∷ CCZ124 ∷ CCZ023 ∷ []) (CCZ013 ∷ Toff024 ∷ Toff314 ∷ CCZ124 ∷ CCZ014 ∷ CCZ013 ∷ Toff024 ∷ CCZ023 ∷ Toff314 ∷ CCZ124 ∷ CCZ023 ∷ [])
  b8 = at 7 2 (Toff024 ∷ K3⁻ ∷ []) (wp0740 c4) ▸
       at 6 2 (Toff024 ∷ CS34 ∷ []) (wp0970 c4) ▸
       at 5 2 (Toff024 ∷ CX31 ∷ []) (lem-comm-CX31-TOFF024 (lit c4)) ▸
       at 4 2 (Toff024 ∷ CS14⁻ ∷ []) (wp0995 c4) ▸
       at 3 2 (Toff024 ∷ CX31 ∷ []) (lem-comm-CX31-TOFF024 (lit c4)) ▸
       at 2 2 (Toff024 ∷ CS14 ∷ []) (wp0590 c4) ▸
       at 1 2 (Toff024 ∷ K3 ∷ []) (wp0742 c4) ▸
       at 2 7 (Toff314 ∷ []) (wl1182 (lit c4)) ▸ done

  b9 : Chain (CCZ013 ∷ Toff024 ∷ Toff314 ∷ CCZ124 ∷ CCZ014 ∷ CCZ013 ∷ Toff024 ∷ CCZ023 ∷ Toff314 ∷ CCZ124 ∷ CCZ023 ∷ []) (CCZ013 ∷ Toff024 ∷ Toff314 ∷ CCZ013 ∷ CCZ124 ∷ CCZ014 ∷ Toff024 ∷ CCZ023 ∷ Toff314 ∷ CCZ124 ∷ CCZ023 ∷ [])
  b9 = at 4 2 (CCZ013 ∷ CCZ014 ∷ []) (sym (wp0394 c4)) ▸
       at 3 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 7 2 (CCZ013 ∷ CS12 ∷ []) (sym (wl0645 (lit c4))) ▸
       at 6 2 (CCZ013 ∷ CX14 ∷ []) (sym (wp0189 c4)) ▸
       at 5 2 (CCZ013 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-CCZ013 (lit c4)) ▸
       at 4 2 (CCZ013 ∷ CX14 ∷ []) (sym (wp0189 c4)) ▸
       at 3 2 (CCZ013 ∷ CS24 ∷ []) (lem-comm-CS24-CCZ013 (lit c4)) ▸
       at 4 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸ done

  b10 : Chain (CCZ013 ∷ Toff024 ∷ Toff314 ∷ CCZ013 ∷ CCZ124 ∷ CCZ014 ∷ Toff024 ∷ CCZ023 ∷ Toff314 ∷ CCZ124 ∷ CCZ023 ∷ []) (CCZ013 ∷ Toff024 ∷ CCZ013 ∷ K3 ∷ CS14 ∷ CX31 ∷ Toff024 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ K3⁻ ∷ CCZ124 ∷ CCZ023 ∷ Toff314 ∷ CCZ124 ∷ CCZ023 ∷ [])
  b10 = at 2 2 (CCZ013 ∷ Toff314 ∷ CCZ014 ∷ []) (sym (wp0990 c4)) ▸
       at 4 3 (CCZ124 ∷ []) (wp0996 c4) ▸
       at 4 2 (Toff024 ∷ CCZ124 ∷ []) (wp0743 c4) ▸
       at 3 1 (K3 ∷ CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ K3⁻ ∷ []) (sym (wl1182 (lit c4))) ▸
       at 9 2 (Toff024 ∷ K3⁻ ∷ []) (wp0740 c4) ▸
       at 8 2 (Toff024 ∷ CS34 ∷ []) (wp0970 c4) ▸
       at 7 2 (Toff024 ∷ CX31 ∷ []) (lem-comm-CX31-TOFF024 (lit c4)) ▸
       at 6 2 (Toff024 ∷ CS14⁻ ∷ []) (wp0995 c4) ▸ done

  b11 : Chain (CCZ013 ∷ Toff024 ∷ CCZ013 ∷ K3 ∷ CS14 ∷ CX31 ∷ Toff024 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ K3⁻ ∷ CCZ124 ∷ CCZ023 ∷ Toff314 ∷ CCZ124 ∷ CCZ023 ∷ []) (Bx0-3142 ∷ Toff314 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CCZ023 ∷ CX14 ∷ CS12 ∷ Toff314 ∷ CCZ124 ∷ CCZ023 ∷ [])
  b11 = at 5 2 (Toff024 ∷ CX31 ∷ []) (lem-comm-CX31-TOFF024 (lit c4)) ▸
       at 4 2 (Toff024 ∷ CS14 ∷ []) (wp0590 c4) ▸
       at 3 2 (Toff024 ∷ K3 ∷ []) (wp0742 c4) ▸
       at 4 7 (Toff314 ∷ []) (wl1182 (lit c4)) ▸
       at 0 4 (Bx0-3142 ∷ []) (sym (lem-box-cP-at13213442 c4)) ▸
       at 2 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 6 2 (CCZ023 ∷ CS12 ∷ []) (sym (wl0621 (lit c4))) ▸
       at 5 2 (CCZ023 ∷ CX14 ∷ []) (lem-comm-CX14-CCZ023 (lit c4)) ▸ done

  b12 : Chain (Bx0-3142 ∷ Toff314 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CCZ023 ∷ CX14 ∷ CS12 ∷ Toff314 ∷ CCZ124 ∷ CCZ023 ∷ []) (Bx0-3142 ∷ Bx3-1420 ∷ [])
  b12 = at 4 2 (CCZ023 ∷ CS24⁻ ∷ []) (sym (wp0820 c4)) ▸
       at 3 2 (CCZ023 ∷ CX14 ∷ []) (lem-comm-CX14-CCZ023 (lit c4)) ▸
       at 2 2 (CCZ023 ∷ CS24 ∷ []) (sym (wp0513 c4)) ▸
       at 3 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 3 2 (Toff314 ∷ CCZ124 ∷ []) (wl0974 (lit c4)) ▸
       at 4 2 [] (wl0263 (lit c4)) ▸
       at 1 4 (Bx3-1420 ∷ []) (sym (lem-box-tQ-at03243240 c4)) ▸ done


-- box-perm-3421 @13213442: 2 steps
lem-box-perm-3421-at13213442 : Ws → ⟪ (Bx0-3142 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4213 ∷ []) ⟫ʷ
lem-box-perm-3421-at13213442 c4 = run b0
  where
  b0 : Chain (Bx0-3142 ∷ []) (Bx0-4213 ∷ [])
  b0 = at 0 1 (Bx0-1342 ∷ []) (lem-sym-ab-at13213442 c4) ▸
       at 0 1 (Bx0-4213 ∷ []) (lem-pairs-at233442 c4) ▸ done


-- sym-ab @03243240: 18 steps
lem-sym-ab-at03243240 : Ws → ⟪ (Bx3-1420 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4120 ∷ []) ⟫ʷ
lem-sym-ab-at03243240 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx3-1420 ∷ []) (CCZ134 ∷ Toff314 ∷ CCZ234 ∷ Toff423 ∷ Bx3-40 ∷ Toff423 ∷ CCZ234 ∷ Bx3-40 ∷ Toff314 ∷ CCZ134 ∷ Bx1-320 ∷ [])
  b0 = at 0 1 (CCZ134 ∷ Toff314 ∷ Bx1-320 ∷ Toff314 ∷ CCZ134 ∷ Bx1-320 ∷ []) (refl) ▸
       at 2 1 (CCZ123 ∷ Toff123 ∷ Bx3-10 ∷ Toff123 ∷ CCZ123 ∷ Bx3-10 ∷ []) (refl) ▸
       at 4 1 (CZ01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 2 6 (CCZ023 ∷ []) (sym (wl1126 (lit c4))) ▸
       at 2 1 (CCZ234 ∷ Toff423 ∷ CZ04 ∷ Toff423 ∷ CCZ234 ∷ CZ04 ∷ []) (wp0992 c4) ▸
       at 4 1 (Bx3-40 ∷ []) (refl) ▸
       at 7 1 (Bx3-40 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ134 ∷ Toff314 ∷ CCZ234 ∷ Toff423 ∷ Bx3-40 ∷ Toff423 ∷ CCZ234 ∷ Bx3-40 ∷ Toff314 ∷ CCZ134 ∷ Bx1-320 ∷ []) (CCZ134 ∷ Toff314 ∷ Bx4-320 ∷ Toff314 ∷ CCZ134 ∷ CCZ234 ∷ Toff423 ∷ Bx3-40 ∷ Toff423 ∷ CCZ234 ∷ Bx3-40 ∷ [])
  b1 = at 2 6 (Bx4-320 ∷ []) (refl) ▸
       at 5 1 (CCZ123 ∷ Toff123 ∷ Bx3-10 ∷ Toff123 ∷ CCZ123 ∷ Bx3-10 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 10 1 (CZ01 ∷ []) (refl) ▸
       at 5 6 (CCZ023 ∷ []) (sym (wl1126 (lit c4))) ▸
       at 5 1 (CCZ234 ∷ Toff423 ∷ CZ04 ∷ Toff423 ∷ CCZ234 ∷ CZ04 ∷ []) (wp0992 c4) ▸
       at 7 1 (Bx3-40 ∷ []) (refl) ▸
       at 10 1 (Bx3-40 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ134 ∷ Toff314 ∷ Bx4-320 ∷ Toff314 ∷ CCZ134 ∷ CCZ234 ∷ Toff423 ∷ Bx3-40 ∷ Toff423 ∷ CCZ234 ∷ Bx3-40 ∷ []) (Bx3-4120 ∷ [])
  b2 = at 5 6 (Bx4-320 ∷ []) (refl) ▸
       at 0 6 (Bx3-4120 ∷ []) (refl) ▸ done


-- box-tQ @0314213240: 13 steps
lem-box-tQ-at0314213240 : Ws → ⟪ (Bx3-4120 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ []) ⟫ʷ
lem-box-tQ-at0314213240 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-4120 ∷ []) (CCZ134 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ CCZ234 ∷ Toff423 ∷ CZ04 ∷ Toff423 ∷ CCZ234 ∷ CZ04 ∷ [])
  b0 = at 0 1 (CCZ134 ∷ Toff314 ∷ Bx4-320 ∷ Toff314 ∷ CCZ134 ∷ Bx4-320 ∷ []) (refl) ▸
       at 2 1 (CCZ234 ∷ Toff423 ∷ Bx3-40 ∷ Toff423 ∷ CCZ234 ∷ Bx3-40 ∷ []) (refl) ▸
       at 4 1 (CZ04 ∷ []) (refl) ▸
       at 7 1 (CZ04 ∷ []) (refl) ▸
       at 2 6 (CCZ023 ∷ []) (sym (wp0992 c4)) ▸
       at 5 1 (CCZ234 ∷ Toff423 ∷ Bx3-40 ∷ Toff423 ∷ CCZ234 ∷ Bx3-40 ∷ []) (refl) ▸
       at 7 1 (CZ04 ∷ []) (refl) ▸
       at 10 1 (CZ04 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ134 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ CCZ234 ∷ Toff423 ∷ CZ04 ∷ Toff423 ∷ CCZ234 ∷ CZ04 ∷ []) (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ [])
  b1 = at 5 6 (CCZ023 ∷ []) (sym (wp0992 c4)) ▸
       at 0 2 (Toff314 ∷ CCZ134 ∷ CZ14 ∷ []) (wl0749 (lit c4)) ▸
       at 2 2 (CCZ023 ∷ CZ14 ∷ []) (lem-comm-CZ14-CCZ023 (lit c4)) ▸
       at 1 2 (CCZ023 ∷ CCZ134 ∷ []) (lem-cQ-at0314213240 c4) ▸
       at 2 4 (Toff314 ∷ []) (wl0750 (lit c4)) ▸ done


-- CXbc-box @0314213240: 17 steps
lem-CXbc-box-at0314213240 : Ws → ⟪ (CX12 ∷ Bx3-4120 ∷ CX12 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4120 ∷ CCZ014 ∷ []) ⟫ʷ
lem-CXbc-box-at0314213240 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX12 ∷ Bx3-4120 ∷ CX12 ∷ []) (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CX12 ∷ CCZ013 ∷ CS01 ∷ CX41 ∷ CS01⁻ ∷ CCZ023 ∷ CX41 ∷ CS04 ∷ CX12 ∷ [])
  b0 = at 1 1 (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ []) (lem-box-tQ-at0314213240 c4) ▸
       at 0 2 (Toff314 ∷ CX12 ∷ []) (wl1183 (lit c4)) ▸
       at 1 2 (CCZ023 ∷ CX12 ∷ CCZ013 ∷ []) (sym (wl0668 (lit c4))) ▸
       at 3 2 (Toff314 ∷ CCZ013 ∷ CCZ014 ∷ []) (wp0997 c4) ▸
       at 2 2 (Toff314 ∷ CX12 ∷ []) (wl1183 (lit c4)) ▸
       at 5 1 (CS01 ∷ CX41 ∷ CS01⁻ ∷ CX41 ∷ CS04 ∷ []) (wp0540 c4) ▸
       at 9 2 (CCZ023 ∷ CS04 ∷ []) (sym (wp0048 c4)) ▸
       at 8 2 (CCZ023 ∷ CX41 ∷ []) (lem-comm-CX41-CCZ023 (lit c4)) ▸ done

  b1 : Chain (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CX12 ∷ CCZ013 ∷ CS01 ∷ CX41 ∷ CS01⁻ ∷ CCZ023 ∷ CX41 ∷ CS04 ∷ CX12 ∷ []) (Bx3-4120 ∷ CX12 ∷ CCZ014 ∷ CX12 ∷ [])
  b1 = at 7 2 (CCZ023 ∷ CS01⁻ ∷ []) (sym (wl0667 (lit c4))) ▸
       at 6 2 (CCZ023 ∷ CX41 ∷ []) (lem-comm-CX41-CCZ023 (lit c4)) ▸
       at 5 2 (CCZ023 ∷ CS01 ∷ []) (sym (wl0199 (lit c4))) ▸
       at 6 5 (CCZ014 ∷ []) (sym (wp0540 c4)) ▸
       at 4 2 (CCZ023 ∷ CCZ013 ∷ []) (wl0671 (lit c4)) ▸
       at 3 2 (CCZ023 ∷ CX12 ∷ CCZ013 ∷ []) (sym (wl0668 (lit c4))) ▸
       at 4 3 (CX12 ∷ []) (wl0672 (lit c4)) ▸
       at 0 4 (Bx3-4120 ∷ []) (sym (lem-box-tQ-at0314213240 c4)) ▸ done

  b2 : Chain (Bx3-4120 ∷ CX12 ∷ CCZ014 ∷ CX12 ∷ []) (Bx3-4120 ∷ CCZ014 ∷ [])
  b2 = at 1 3 (CCZ014 ∷ []) (sym (wp0655 c4)) ▸ done


-- CXcb-box @0314213240: 18 steps
lem-CXcb-box-at0314213240 : Ws → ⟪ (CX21 ∷ Bx3-4120 ∷ CX21 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4120 ∷ CCZ024 ∷ []) ⟫ʷ
lem-CXcb-box-at0314213240 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX21 ∷ Bx3-4120 ∷ CX21 ∷ []) (Toff314 ∷ CCZ023 ∷ CX21 ∷ Toff324 ∷ CS02 ∷ CX42 ∷ Toff314 ∷ CS02⁻ ∷ CX42 ∷ CS04 ∷ CCZ023 ∷ CX21 ∷ [])
  b0 = at 1 1 (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ []) (lem-box-tQ-at0314213240 c4) ▸
       at 0 2 (Toff314 ∷ CX21 ∷ Toff324 ∷ []) (wl1184 (lit c4)) ▸
       at 2 2 (CCZ023 ∷ Toff324 ∷ CCZ024 ∷ []) (sym (wp0814 c4)) ▸
       at 1 2 (CCZ023 ∷ CX21 ∷ []) (sym (wl0674 (lit c4))) ▸
       at 4 1 (CS02 ∷ CX42 ∷ CS02⁻ ∷ CX42 ∷ CS04 ∷ []) (wp0213 c4) ▸
       at 8 2 (Toff314 ∷ CS04 ∷ []) (wp0998 c4) ▸
       at 7 2 (Toff314 ∷ CX42 ∷ []) (wl1185 (lit c4)) ▸
       at 6 2 (Toff314 ∷ CS02⁻ ∷ []) (lem-comm-CSd02-TOFF314 (lit c4)) ▸ done

  b1 : Chain (Toff314 ∷ CCZ023 ∷ CX21 ∷ Toff324 ∷ CS02 ∷ CX42 ∷ Toff314 ∷ CS02⁻ ∷ CX42 ∷ CS04 ∷ CCZ023 ∷ CX21 ∷ []) (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ CX21 ∷ CCZ024 ∷ CX21 ∷ [])
  b1 = at 5 2 (Toff314 ∷ CX42 ∷ []) (wl1185 (lit c4)) ▸
       at 4 2 (Toff314 ∷ CS02 ∷ []) (lem-comm-CS02-TOFF314 (lit c4)) ▸
       at 5 5 (CCZ024 ∷ []) (sym (wp0213 c4)) ▸
       at 3 2 (Toff314 ∷ Toff324 ∷ []) (sym (wl1180 (lit c4))) ▸
       at 2 2 (Toff314 ∷ CX21 ∷ Toff324 ∷ []) (wl1184 (lit c4)) ▸
       at 3 3 (CX21 ∷ []) (wl1186 (lit c4)) ▸
       at 4 2 (CCZ023 ∷ CCZ024 ∷ []) (sym (wp0669 c4)) ▸
       at 3 2 (CCZ023 ∷ CX21 ∷ []) (sym (wl0674 (lit c4))) ▸ done

  b2 : Chain (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ CX21 ∷ CCZ024 ∷ CX21 ∷ []) (Bx3-4120 ∷ CCZ024 ∷ [])
  b2 = at 0 4 (Bx3-4120 ∷ []) (sym (lem-box-tQ-at0314213240 c4)) ▸
       at 1 3 (CCZ024 ∷ []) (sym (wp0898 c4)) ▸ done


-- SWbc-box @0314213240: 11 steps
lem-SWbc-box-at0314213240 : Ws → ⟪ (Sw12 ∷ Bx3-4120 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4120 ∷ []) ⟫ʷ
lem-SWbc-box-at0314213240 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw12 ∷ Bx3-4120 ∷ Sw12 ∷ []) (CX12 ∷ Bx3-4120 ∷ CX12 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ [])
  b0 = at 0 1 (CX12 ∷ CX21 ∷ CX12 ∷ []) (sym (wl0677 (lit c4))) ▸
       at 4 1 (CX12 ∷ CX21 ∷ CX12 ∷ []) (sym (wl0677 (lit c4))) ▸
       at 2 3 (Bx3-4120 ∷ CCZ014 ∷ []) (lem-CXbc-box-at0314213240 c4) ▸
       at 3 2 (CX21 ∷ CCZ024 ∷ CCZ014 ∷ []) (wp0899 c4) ▸
       at 1 3 (Bx3-4120 ∷ CCZ024 ∷ []) (lem-CXcb-box-at0314213240 c4) ▸
       at 4 2 (CX12 ∷ CCZ014 ∷ []) (wp0054 c4) ▸
       at 3 2 (CX12 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp0653 c4) ▸
       at 2 2 (CX12 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp0653 c4) ▸ done

  b1 : Chain (CX12 ∷ Bx3-4120 ∷ CX12 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ []) (Bx3-4120 ∷ [])
  b1 = at 3 5 (CCZ014 ∷ []) (wp0900 c4) ▸
       at 0 3 (Bx3-4120 ∷ CCZ014 ∷ []) (lem-CXbc-box-at0314213240 c4) ▸
       at 1 2 [] (wp0161 c4) ▸ done


-- nat-SWbc @0314213240: 23 steps
lem-nat-SWbc-at0314213240 : Ws → ⟪ (Sw12 ∷ Bx3-4120 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4210 ∷ []) ⟫ʷ
lem-nat-SWbc-at0314213240 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw12 ∷ Bx3-4120 ∷ Sw12 ∷ []) (CCZ234 ∷ Toff324 ∷ CCZ134 ∷ Toff413 ∷ Bx3-40 ∷ Toff413 ∷ Sw12 ∷ CCZ234 ∷ Bx3-40 ∷ Toff314 ∷ CCZ134 ∷ Bx4-320 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff314 ∷ Bx4-320 ∷ Toff314 ∷ CCZ134 ∷ Bx4-320 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw12 ∷ []) (sym (wl0044 (lit c4))) ▸
       at 1 2 (Toff324 ∷ Sw12 ∷ []) (wl0045 (lit c4)) ▸
       at 3 1 (CCZ234 ∷ Toff423 ∷ Bx3-40 ∷ Toff423 ∷ CCZ234 ∷ Bx3-40 ∷ []) (refl) ▸
       at 2 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0037 (lit c4))) ▸
       at 3 2 (Toff413 ∷ Sw12 ∷ []) (wl0085 (lit c4)) ▸
       at 4 2 (Bx3-40 ∷ Sw12 ∷ []) (lem-comm-SWAP12-BOX⟨3·40⟩ (lit c4)) ▸
       at 5 2 (Toff413 ∷ Sw12 ∷ []) (wl0085 (lit c4)) ▸ done

  b1 : Chain (CCZ234 ∷ Toff324 ∷ CCZ134 ∷ Toff413 ∷ Bx3-40 ∷ Toff413 ∷ Sw12 ∷ CCZ234 ∷ Bx3-40 ∷ Toff314 ∷ CCZ134 ∷ Bx4-320 ∷ Sw12 ∷ []) (CCZ234 ∷ Toff324 ∷ CCZ134 ∷ Toff413 ∷ Bx3-40 ∷ Toff413 ∷ CCZ134 ∷ Bx3-40 ∷ Toff324 ∷ CCZ234 ∷ CCZ134 ∷ Toff413 ∷ Bx3-40 ∷ Sw12 ∷ Toff423 ∷ CCZ234 ∷ Bx3-40 ∷ Sw12 ∷ [])
  b1 = at 6 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0037 (lit c4))) ▸
       at 7 2 (Bx3-40 ∷ Sw12 ∷ []) (lem-comm-SWAP12-BOX⟨3·40⟩ (lit c4)) ▸
       at 8 2 (Toff324 ∷ Sw12 ∷ []) (wl0045 (lit c4)) ▸
       at 9 2 (CCZ234 ∷ Sw12 ∷ []) (sym (wl0044 (lit c4))) ▸
       at 11 1 (CCZ234 ∷ Toff423 ∷ Bx3-40 ∷ Toff423 ∷ CCZ234 ∷ Bx3-40 ∷ []) (refl) ▸
       at 10 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0037 (lit c4))) ▸
       at 11 2 (Toff413 ∷ Sw12 ∷ []) (wl0085 (lit c4)) ▸
       at 12 2 (Bx3-40 ∷ Sw12 ∷ []) (lem-comm-SWAP12-BOX⟨3·40⟩ (lit c4)) ▸ done

  b2 : Chain (CCZ234 ∷ Toff324 ∷ CCZ134 ∷ Toff413 ∷ Bx3-40 ∷ Toff413 ∷ CCZ134 ∷ Bx3-40 ∷ Toff324 ∷ CCZ234 ∷ CCZ134 ∷ Toff413 ∷ Bx3-40 ∷ Sw12 ∷ Toff423 ∷ CCZ234 ∷ Bx3-40 ∷ Sw12 ∷ []) (Bx3-4210 ∷ [])
  b2 = at 13 2 (Toff413 ∷ Sw12 ∷ []) (wl0085 (lit c4)) ▸
       at 14 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0037 (lit c4))) ▸
       at 15 2 (Bx3-40 ∷ Sw12 ∷ []) (lem-comm-SWAP12-BOX⟨3·40⟩ (lit c4)) ▸
       at 16 2 [] (wl0006 (lit c4)) ▸
       at 2 6 (Bx4-310 ∷ []) (refl) ▸
       at 5 6 (Bx4-310 ∷ []) (refl) ▸
       at 0 6 (Bx3-4210 ∷ []) (refl) ▸ done


-- sym-bc @0314213240: 2 steps
lem-sym-bc-at0314213240 : Ws → ⟪ (Bx3-4120 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4210 ∷ []) ⟫ʷ
lem-sym-bc-at0314213240 c4 = run b0
  where
  b0 : Chain (Bx3-4120 ∷ []) (Bx3-4210 ∷ [])
  b0 = at 0 1 (Sw12 ∷ Bx3-4120 ∷ Sw12 ∷ []) (sym (lem-SWbc-box-at0314213240 c4)) ▸
       at 0 3 (Bx3-4210 ∷ []) (lem-nat-SWbc-at0314213240 c4) ▸ done


-- box-perm-2314 @03243240: 2 steps
lem-box-perm-2314-at03243240 : Ws → ⟪ (Bx3-1420 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4210 ∷ []) ⟫ʷ
lem-box-perm-2314-at03243240 c4 = run b0
  where
  b0 : Chain (Bx3-1420 ∷ []) (Bx3-4210 ∷ [])
  b0 = at 0 1 (Bx3-4120 ∷ []) (lem-sym-ab-at03243240 c4) ▸
       at 0 1 (Bx3-4210 ∷ []) (lem-sym-bc-at0314213240 c4) ▸ done


-- F0-B @01143043: 62 steps
lem-F0-B-at01143043 : Ws → ⟪ (CX03 ∷ Bx0-4213 ∷ CX03 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4213 ∷ Bx3-4210 ∷ []) ⟫ʷ
lem-F0-B-at01143043 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (run b7)))))))
  where
  b0 : Chain (CX03 ∷ Bx0-4213 ∷ CX03 ∷ []) (Toff024 ∷ Toff324 ∷ CCZ013 ∷ Toff024 ∷ Toff324 ∷ CZ01 ∷ CCZ124 ∷ CCZ013 ∷ CZ01 ∷ [])
  b0 = at 1 1 (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-box-tQ-at143143 c4) ▸
       at 0 2 (Toff024 ∷ Toff324 ∷ CX03 ∷ []) (wp0999 c4) ▸
       at 2 2 (CCZ013 ∷ CZ01 ∷ CX03 ∷ []) (sym (wl1187 (lit c4))) ▸
       at 4 2 (Toff024 ∷ Toff324 ∷ CX03 ∷ []) (wp0999 c4) ▸
       at 6 3 (CCZ013 ∷ CZ01 ∷ []) (sym (wl1188 (lit c4))) ▸
       at 3 2 (Toff024 ∷ CZ01 ∷ CCZ124 ∷ []) (wp0886 c4) ▸
       at 5 2 (Toff324 ∷ CCZ124 ∷ []) (wl0450 (lit c4)) ▸
       at 4 2 (Toff324 ∷ CZ01 ∷ []) (c₂ (CZ) (K ↑ • CCZ • K ↑ • iI)) ▸ done

  b1 : Chain (Toff024 ∷ Toff324 ∷ CCZ013 ∷ Toff024 ∷ Toff324 ∷ CZ01 ∷ CCZ124 ∷ CCZ013 ∷ CZ01 ∷ []) (K0 ∷ CS02 ∷ CX42 ∷ CS02⁻ ∷ CX42 ∷ CS04 ∷ K0⁻ ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ013 ∷ Toff024 ∷ CCZ124 ∷ CCZ013 ∷ [])
  b1 = at 5 2 (CCZ124 ∷ CZ01 ∷ []) (sym (wp1000 c4)) ▸
       at 6 3 (CCZ013 ∷ []) (sym (wl0868 (lit c4))) ▸
       at 3 2 (Toff324 ∷ Toff024 ∷ []) (wp1001 c4) ▸
       at 4 0 (CCZ013 ∷ CCZ013 ∷ []) (sym (wl0230 (lit c4))) ▸
       at 1 4 (Bx3-4210 ∷ []) (sym (lem-box-tQ-at03143140 c4)) ▸
       at 1 1 (Bx3-4120 ∷ []) (lem-box-perm-1324-at03143140 c4) ▸
       at 1 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at0314213240 c4) ▸
       at 0 1 (K0 ∷ CS02 ∷ CX42 ∷ CS02⁻ ∷ CX42 ∷ CS04 ∷ K0⁻ ∷ []) (sym (wp1002 c4)) ▸ done

  b2 : Chain (K0 ∷ CS02 ∷ CX42 ∷ CS02⁻ ∷ CX42 ∷ CS04 ∷ K0⁻ ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ013 ∷ Toff024 ∷ CCZ124 ∷ CCZ013 ∷ []) (CCZ134 ∷ Toff024 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ013 ∷ Toff024 ∷ CCZ124 ∷ CCZ013 ∷ [])
  b2 = at 6 2 (CCZ134 ∷ K0⁻ ∷ []) (c₁ (K • iI) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑)) ▸
       at 5 2 (CCZ134 ∷ CS04 ∷ []) (sym (wp1003 c4)) ▸
       at 4 2 (CCZ134 ∷ CX42 ∷ []) (sym (wl0318 (lit c4))) ▸
       at 3 2 (CCZ134 ∷ CS02⁻ ∷ []) (lem-comm-CSd02-CCZ134 (lit c4)) ▸
       at 2 2 (CCZ134 ∷ CX42 ∷ []) (sym (wl0318 (lit c4))) ▸
       at 1 2 (CCZ134 ∷ CS02 ∷ []) (lem-comm-CS02-CCZ134 (lit c4)) ▸
       at 0 2 (CCZ134 ∷ K0 ∷ []) (c₁ (K) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑)) ▸
       at 1 7 (Toff024 ∷ []) (wp1002 c4) ▸ done

  b3 : Chain (CCZ134 ∷ Toff024 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ013 ∷ Toff024 ∷ CCZ124 ∷ CCZ013 ∷ []) (CCZ134 ∷ Toff302 ∷ K0 ∷ CS02 ∷ CCZ134 ∷ CX42 ∷ CS02⁻ ∷ CX42 ∷ CS04 ∷ K0⁻ ∷ Toff324 ∷ CCZ124 ∷ Toff302 ∷ CCZ013 ∷ Toff024 ∷ CCZ124 ∷ CCZ013 ∷ [])
  b3 = at 1 2 (Toff302 ∷ Toff024 ∷ Toff324 ∷ []) (wp1004 c4) ▸
       at 3 2 (CCZ134 ∷ Toff324 ∷ CCZ124 ∷ []) (sym (wl1189 (lit c4))) ▸
       at 2 1 (K0 ∷ CS02 ∷ CX42 ∷ CS02⁻ ∷ CX42 ∷ CS04 ∷ K0⁻ ∷ []) (sym (wp1002 c4)) ▸
       at 8 2 (CCZ134 ∷ K0⁻ ∷ []) (c₁ (K • iI) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑)) ▸
       at 7 2 (CCZ134 ∷ CS04 ∷ []) (sym (wp1003 c4)) ▸
       at 6 2 (CCZ134 ∷ CX42 ∷ []) (sym (wl0318 (lit c4))) ▸
       at 5 2 (CCZ134 ∷ CS02⁻ ∷ []) (lem-comm-CSd02-CCZ134 (lit c4)) ▸
       at 4 2 (CCZ134 ∷ CX42 ∷ []) (sym (wl0318 (lit c4))) ▸ done

  b4 : Chain (CCZ134 ∷ Toff302 ∷ K0 ∷ CS02 ∷ CCZ134 ∷ CX42 ∷ CS02⁻ ∷ CX42 ∷ CS04 ∷ K0⁻ ∷ Toff324 ∷ CCZ124 ∷ Toff302 ∷ CCZ013 ∷ Toff024 ∷ CCZ124 ∷ CCZ013 ∷ []) (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff024 ∷ Toff324 ∷ CS24 ∷ Toff302 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ CCZ013 ∷ Toff024 ∷ CCZ124 ∷ CCZ013 ∷ [])
  b4 = at 3 2 (CCZ134 ∷ CS02 ∷ []) (lem-comm-CS02-CCZ134 (lit c4)) ▸
       at 2 2 (CCZ134 ∷ K0 ∷ []) (c₁ (K) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑)) ▸
       at 3 7 (Toff024 ∷ []) (wp1002 c4) ▸
       at 5 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 9 2 (Toff302 ∷ CS12 ∷ []) (wl1190 (lit c4)) ▸
       at 8 2 (Toff302 ∷ CX14 ∷ []) (lem-comm-CX14-TOFF302 (lit c4)) ▸
       at 7 2 (Toff302 ∷ CS24⁻ ∷ []) (wp1005 c4) ▸
       at 6 2 (Toff302 ∷ CX14 ∷ []) (lem-comm-CX14-TOFF302 (lit c4)) ▸ done

  b5 : Chain (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff024 ∷ Toff324 ∷ CS24 ∷ Toff302 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ CCZ013 ∷ Toff024 ∷ CCZ124 ∷ CCZ013 ∷ []) (Bx3-4210 ∷ Toff024 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ CCZ013 ∷ Toff024 ∷ CCZ124 ∷ CCZ013 ∷ [])
  b5 = at 5 2 (Toff302 ∷ CS24 ∷ []) (wp1006 c4) ▸
       at 6 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 4 2 (Toff302 ∷ Toff324 ∷ []) (sym (wp1007 c4)) ▸
       at 3 2 (Toff302 ∷ Toff024 ∷ Toff324 ∷ []) (wp1004 c4) ▸
       at 4 3 (Toff024 ∷ []) (wp1008 c4) ▸
       at 0 4 (Bx3-4120 ∷ []) (sym (lem-box-cP-at0314213240 c4)) ▸
       at 0 1 (Bx3-4210 ∷ []) (sym (lem-box-perm-1324-at03143140 c4)) ▸
       at 2 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸ done

  b6 : Chain (Bx3-4210 ∷ Toff024 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ CCZ013 ∷ Toff024 ∷ CCZ124 ∷ CCZ013 ∷ []) (Bx3-4210 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ [])
  b6 = at 6 2 (CCZ013 ∷ CS12 ∷ []) (sym (wl0645 (lit c4))) ▸
       at 5 2 (CCZ013 ∷ CX14 ∷ []) (sym (wp0189 c4)) ▸
       at 4 2 (CCZ013 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-CCZ013 (lit c4)) ▸
       at 3 2 (CCZ013 ∷ CX14 ∷ []) (sym (wp0189 c4)) ▸
       at 2 2 (CCZ013 ∷ CS24 ∷ []) (lem-comm-CS24-CCZ013 (lit c4)) ▸
       at 3 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 3 2 (Toff024 ∷ CCZ124 ∷ []) (wp0743 c4) ▸
       at 4 2 [] (wl0263 (lit c4)) ▸ done

  b7 : Chain (Bx3-4210 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (Bx0-4213 ∷ Bx3-4210 ∷ [])
  b7 = at 1 4 (Bx0-4213 ∷ []) (sym (lem-box-tQ-at143143 c4)) ▸
       at 0 1 (Bx3-1420 ∷ []) (lem-box-perm-3124-at03143140 c4) ▸
       at 1 1 (Bx0-3142 ∷ []) (lem-box-perm-4312-at143143 c4) ▸
       at 0 2 (Bx0-3142 ∷ Bx3-1420 ∷ []) (lem-box-box-4-at03243240 c4) ▸
       at 0 1 (Bx0-4213 ∷ []) (lem-box-perm-3421-at13213442 c4) ▸
       at 1 1 (Bx3-4210 ∷ []) (lem-box-perm-2314-at03243240 c4) ▸ done


-- tP @03143140: 7 steps
lem-tP-at03143140 : Ws → ⟪ (Toff324 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ Toff324 ∷ []) ⟫ʷ
lem-tP-at03143140 c4 = run b0
  where
  b0 : Chain (Toff324 ∷ Toff301 ∷ []) (Toff301 ∷ Toff324 ∷ [])
  b0 = at 0 1 (K3 ∷ CCZ234 ∷ K3⁻ ∷ []) (sym (wl0435 (lit c4))) ▸
       at 3 1 (K3 ∷ CCZ013 ∷ K3⁻ ∷ []) (sym (wl0434 (lit c4))) ▸
       at 2 2 [] (wl0436 (lit c4)) ▸
       at 1 2 (CCZ013 ∷ CCZ234 ∷ []) (lem-cQ-at03143140 c4) ▸
       at 2 0 (K3⁻ ∷ K3 ∷ []) (sym (wl0436 (lit c4))) ▸
       at 0 3 (Toff301 ∷ []) (wl0434 (lit c4)) ▸
       at 1 3 (Toff324 ∷ []) (wl0435 (lit c4)) ▸ done


-- VPQ @03143140: 14 steps
lem-VPQ-at03143140 : Ws → ⟪ (Toff324 ∷ CCZ234 ∷ Toff301 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CCZ013 ∷ Toff324 ∷ CCZ234 ∷ []) ⟫ʷ
lem-VPQ-at03143140 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff324 ∷ CCZ234 ∷ Toff301 ∷ CCZ013 ∷ []) (CS01⁻ ∷ CS24⁻ ∷ S3 ∷ Toff301 ∷ Toff324 ∷ S3⁻ ∷ [])
  b0 = at 0 2 (CS24⁻ ∷ S3 ∷ Toff324 ∷ S3⁻ ∷ []) (sym (wl0438 (lit c4))) ▸
       at 4 2 (CS01⁻ ∷ S3 ∷ Toff301 ∷ S3⁻ ∷ []) (sym (wl0437 (lit c4))) ▸
       at 3 2 (CS01⁻ ∷ S3⁻ ∷ []) (sym (c₂ (CS • CS • CS) ((S • S • S) ↑))) ▸
       at 2 2 (CS01⁻ ∷ Toff324 ∷ []) (sym (c₂ (CS • CS • CS) (K ↑ • CCZ • K ↑ • iI))) ▸
       at 1 2 (CS01⁻ ∷ S3 ∷ []) (sym (c₂ (CS • CS • CS) (S ↑))) ▸
       at 0 2 (CS01⁻ ∷ CS24⁻ ∷ []) (sym (c₂ (CS • CS • CS) (Swap ↑ • (CS • CS • CS) • Swap ↑))) ▸
       at 4 2 [] (wl0441 (lit c4)) ▸
       at 3 2 (Toff301 ∷ Toff324 ∷ []) (lem-tP-at03143140 c4) ▸ done

  b1 : Chain (CS01⁻ ∷ CS24⁻ ∷ S3 ∷ Toff301 ∷ Toff324 ∷ S3⁻ ∷ []) (Toff301 ∷ CCZ013 ∷ Toff324 ∷ CCZ234 ∷ [])
  b1 = at 4 0 (S3⁻ ∷ S3 ∷ []) (sym (wl0441 (lit c4))) ▸
       at 1 2 (S3 ∷ CS24⁻ ∷ []) (wl0440 (lit c4)) ▸
       at 2 2 (Toff301 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-TOFF301 (lit c4)) ▸
       at 3 2 (S3⁻ ∷ CS24⁻ ∷ []) (wl0439 (lit c4)) ▸
       at 0 4 (Toff301 ∷ CCZ013 ∷ []) (wl0437 (lit c4)) ▸
       at 2 4 (Toff324 ∷ CCZ234 ∷ []) (wl0438 (lit c4)) ▸ done


-- QVQ @03143140: 3 steps
lem-QVQ-at03143140 : Ws → ⟪ (CCZ013 ∷ Toff324 ∷ CCZ234 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ Toff324 ∷ CCZ234 ∷ Toff301 ∷ []) ⟫ʷ
lem-QVQ-at03143140 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ Toff324 ∷ CCZ234 ∷ CCZ013 ∷ []) (Toff301 ∷ Toff324 ∷ CCZ234 ∷ Toff301 ∷ [])
  b0 = at 0 0 (Toff301 ∷ Toff301 ∷ []) (sym (wl0443 (lit c4))) ▸
       at 1 4 (Toff324 ∷ CCZ234 ∷ Toff301 ∷ CCZ013 ∷ []) (sym (lem-VPQ-at03143140 c4)) ▸
       at 4 2 [] (wl0230 (lit c4)) ▸ done


-- box-cP @03143140: 12 steps
lem-box-cP-at03143140 : Ws → ⟪ (Bx3-4210 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ []) ⟫ʷ
lem-box-cP-at03143140 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-4210 ∷ []) (CCZ234 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ234 ∷ CCZ134 ∷ Toff413 ∷ CZ04 ∷ Toff413 ∷ CCZ134 ∷ CZ04 ∷ [])
  b0 = at 0 1 (CCZ234 ∷ Toff324 ∷ Bx4-310 ∷ Toff324 ∷ CCZ234 ∷ Bx4-310 ∷ []) (refl) ▸
       at 2 1 (CCZ134 ∷ Toff413 ∷ Bx3-40 ∷ Toff413 ∷ CCZ134 ∷ Bx3-40 ∷ []) (refl) ▸
       at 4 1 (CZ04 ∷ []) (refl) ▸
       at 7 1 (CZ04 ∷ []) (refl) ▸
       at 2 6 (CCZ013 ∷ []) (sym (wp0988 c4)) ▸
       at 5 1 (CCZ134 ∷ Toff413 ∷ Bx3-40 ∷ Toff413 ∷ CCZ134 ∷ Bx3-40 ∷ []) (refl) ▸
       at 7 1 (CZ04 ∷ []) (refl) ▸
       at 10 1 (CZ04 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ234 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ234 ∷ CCZ134 ∷ Toff413 ∷ CZ04 ∷ Toff413 ∷ CCZ134 ∷ CZ04 ∷ []) (CCZ234 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ [])
  b1 = at 5 6 (CCZ013 ∷ []) (sym (wp0988 c4)) ▸
       at 2 4 (Toff301 ∷ Toff324 ∷ CCZ234 ∷ Toff301 ∷ []) (lem-QVQ-at03143140 c4) ▸
       at 1 2 (Toff301 ∷ Toff324 ∷ []) (lem-tP-at03143140 c4) ▸
       at 2 2 [] (wl0442 (lit c4)) ▸ done

