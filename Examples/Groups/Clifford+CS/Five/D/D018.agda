{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D018 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0004 ; wl0006 ; wl0157 ; wl0159 ; wl0181 ; wl0190 ; wl0191 ; wl0193 ; wl0194 ; wl0195 ; wl0196 ; wl0197 ; wl0200 ; wl0201 ; wl0202 ; wl0203 ; wl0204 ; wl0206 ; wl0208 ; wl0209 ; wl0210 ; wl0217 ; wl0219 ; wl0220 ; wl0221 ; wl0222 ; wl0230 ; wl0234 ; wl0242 ; wl0245 ; wl0247 ; wl0263 ; wl0295 ; wl0299 ; wl0301 ; wl0303 ; wl0305 ; wl0306 ; wl0324 ; wl0326 ; wl0344 ; wl0423 ; wl0424 ; wl0425 ; wl0448 ; wl0547 ; wl0613 ; wl0617 ; wl0621 ; wl0646 ; wl0648 ; wl0649 ; wl0650 ; wl0651 ; wl0652 ; wl0653 ; wl0671 ; wl0673 ; wl0675 ; wl0676 ; wl0678 ; wl0680 ; wl0720 ; wl0725 ; wl0727 ; wl0743 ; wl0747 ; wl0835 ; wl0836 ; wl0837 ; wl0905 ; wl1000 ; wl1008 ; wl1009 ; wl1131 ; wl1142 ; wl1144 ; wl1145 ; wl1146 ; wl1147 ; wl1151 ; wl1152 ; wl1159 ; wl1160 ; wl1161 ; wl1162 ; wl1163 ; wl1164 ; wl1165 ; wl1166 ; wl1167 ; wl1168 ; wl1169 ; wl1170 ; wl1171 ; wp0021 ; wp0032 ; wp0033 ; wp0034 ; wp0035 ; wp0036 ; wp0037 ; wp0038 ; wp0041 ; wp0044 ; wp0049 ; wp0050 ; wp0051 ; wp0052 ; wp0053 ; wp0055 ; wp0060 ; wp0061 ; wp0062 ; wp0063 ; wp0064 ; wp0065 ; wp0066 ; wp0067 ; wp0069 ; wp0070 ; wp0072 ; wp0074 ; wp0080 ; wp0081 ; wp0091 ; wp0092 ; wp0129 ; wp0132 ; wp0133 ; wp0134 ; wp0161 ; wp0181 ; wp0185 ; wp0186 ; wp0191 ; wp0192 ; wp0194 ; wp0196 ; wp0281 ; wp0286 ; wp0312 ; wp0314 ; wp0357 ; wp0398 ; wp0513 ; wp0548 ; wp0551 ; wp0553 ; wp0569 ; wp0570 ; wp0593 ; wp0617 ; wp0632 ; wp0633 ; wp0651 ; wp0654 ; wp0669 ; wp0680 ; wp0734 ; wp0735 ; wp0736 ; wp0784 ; wp0786 ; wp0795 ; wp0805 ; wp0806 ; wp0815 ; wp0820 ; wp0827 ; wp0906 ; wp0908 ; wp0911 ; wp0912 ; wp0914 ; wp0919 ; wp0920 ; wp0922 ; wp0936 ; wp0937 ; wp0938 ; wp0951 ; wp0952 ; wp0953 ; wp0954 ; wp0955 ; wp0956 ; wp0957 ; wp0958 ; wp0959 ; wp0960 ; wp0961 ; wp0962 ; wp0963 ; wp0964 ; wp0965 ; wp0966 ; wp0967 ; wp0968 ; wp0969 ; wp0970 ; wp0971 ; wp0972 ; wp0973 ; wp0974 ; wp0975 ; wp0976 ; wp0977 ; wp0978)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-box-cP-at0210243143 ; lem-box-cP-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-box-tQ-at233442 ; lem-box-tQ-at2442 ; lem-cQ-at2442)
open import Examples.Groups.Clifford+CS.Five.D.D006 using (lem-box-perm-1423-at0210243143 ; lem-box-tQ-at0210233441)
open import Examples.Groups.Clifford+CS.Five.D.D007 using (lem-box-cP-at233442 ; lem-box-perm-1423-at243243 ; lem-box-tQ-at12213443 ; lem-box-tQ-at143143 ; lem-tP-at233442)
open import Examples.Groups.Clifford+CS.Five.D.D008 using (lem-pairs-at0210233441)
open import Examples.Groups.Clifford+CS.Five.D.D009 using (lem-sym-ab-at0214203143 ; lem-sym-bc-at0214213043)
open import Examples.Groups.Clifford+CS.Five.D.D012 using (lem-sym-ab-at14213243)
open import Examples.Groups.Clifford+CS.Five.D.D014 using (lem-S2-SBOX⟨0·1·42·3⟩ ; lem-S2-SBOX⟨2·0·41·3⟩)
open import Examples.Groups.Clifford+CS.Five.D.D017 using (lem-Xb-box-at02102441 ; lem-box-perm-1324-at0210233441 ; lem-box-perm-1324-at02102441)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CSd14-TOFF023 ; lem-comm-CSd23-CCZ014 ; lem-comm-CX13-CCZ024 ; lem-comm-CX14-CCZ023 ; lem-comm-TOFF014-CSd23)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-CS23-CCZ014 ; lem-comm-CSd13-TOFF024 ; lem-comm-CSd23-TOFF014 ; lem-comm-CSd24-TOFF013 ; lem-comm-CX21-CCZ034 ; lem-comm-CZ24-TOFF013)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-CS13-TOFF024 ; lem-comm-CS24-TOFF013 ; lem-comm-CX42-CCZ013 ; lem-comm-SWAP14-BOX⟨0·23⟩)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-comm-CCZ024-CX13 ; lem-comm-CS23-TOFF014 ; lem-comm-TOFF013-CK42 ; lem-comm-TOFF213-CX04)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-comm-CCZ014-CX23 ; lem-comm-CCZ124-CX03 ; lem-comm-TOFF023-CS14 ; lem-comm-TOFF023-CX14 ; lem-comm-TOFF203-CK41 ; lem-comm-TOFF213-CS04)
-- CKc-box @0210233441: 61 steps
lem-CKc-box-at0210233441 : Ws → ⟪ (Bx2-0341 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ CK41 ∷ CCZ013 ∷ Bx2-0341 ∷ []) ⟫ʷ
lem-CKc-box-at0210233441 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (run b7)))))))
  where
  b0 : Chain (Bx2-0341 ∷ CK41 ∷ []) (X4 ∷ Bx2-0341 ∷ CCZ013 ∷ K1 ∷ CK41 ∷ S4 ∷ CCZ013 ∷ X4 ∷ CCZ013 ∷ [])
  b0 = at 1 0 (CCZ013 ∷ CCZ013 ∷ []) (sym (wl0230 (lit c4))) ▸
       at 0 1 (Bx2-0431 ∷ []) (lem-box-perm-1324-at0210233441 c4) ▸
       at 0 2 (X4 ∷ Bx2-0431 ∷ X4 ∷ []) (sym (lem-Xb-box-at02102441 c4)) ▸
       at 3 2 (CCZ013 ∷ CK41 ∷ CCZ013 ∷ CCZ013 ∷ []) (sym (wp0951 c4)) ▸
       at 2 2 (CCZ013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • CCZ • Swap ↑ ↑) (X))) ▸
       at 3 2 (K1 ∷ CK41 ∷ S4 ∷ X4 ∷ []) (sym (wl0720 (lit c4))) ▸
       at 6 2 (CCZ013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • CCZ • Swap ↑ ↑) (X))) ▸
       at 1 1 (Bx2-0341 ∷ []) (lem-box-perm-1324-at02102441 c4) ▸ done

  b1 : Chain (X4 ∷ Bx2-0341 ∷ CCZ013 ∷ K1 ∷ CK41 ∷ S4 ∷ CCZ013 ∷ X4 ∷ CCZ013 ∷ []) (X4 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ013 ∷ CCZ124 ∷ K1 ∷ CK41 ∷ S4 ∷ CCZ013 ∷ X4 ∷ CCZ013 ∷ [])
  b1 = at 1 1 (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ []) (lem-box-tQ-at0210233441 c4) ▸
       at 5 1 (CS13 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ []) (wl0905 (lit c4)) ▸
       at 4 2 (CS13 ∷ CCZ124 ∷ []) (wl1152 (lit c4)) ▸
       at 5 2 (CX03 ∷ CCZ124 ∷ []) (lem-comm-CCZ124-CX03 (lit c4)) ▸
       at 6 2 (CS13⁻ ∷ CCZ124 ∷ []) (wl1151 (lit c4)) ▸
       at 7 2 (CX03 ∷ CCZ124 ∷ []) (lem-comm-CCZ124-CX03 (lit c4)) ▸
       at 8 2 (CS01 ∷ CCZ124 ∷ []) (wp0919 c4) ▸
       at 4 5 (CCZ013 ∷ []) (sym (wl0905 (lit c4))) ▸ done

  b2 : Chain (X4 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ013 ∷ CCZ124 ∷ K1 ∷ CK41 ∷ S4 ∷ CCZ013 ∷ X4 ∷ CCZ013 ∷ []) (X4 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ013 ∷ K1 ∷ Toff124 ∷ CCZ124 ∷ CZ12 ∷ CK41 ∷ CZ12 ∷ S4 ∷ CS13 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ CCZ124 ∷ CS01 ∷ X4 ∷ CCZ013 ∷ [])
  b2 = at 5 2 (K1 ∷ Toff124 ∷ CCZ124 ∷ CCZ124 ∷ []) (wl1159 (lit c4)) ▸
       at 8 2 (CZ12 ∷ CK41 ∷ CZ12 ∷ CCZ124 ∷ []) (wl1160 (lit c4)) ▸
       at 11 2 (S4 ∷ CCZ124 ∷ []) (wl1161 (lit c4)) ▸
       at 13 1 (CS13 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ []) (wl0905 (lit c4)) ▸
       at 12 2 (CS13 ∷ CCZ124 ∷ []) (wl1152 (lit c4)) ▸
       at 13 2 (CX03 ∷ CCZ124 ∷ []) (lem-comm-CCZ124-CX03 (lit c4)) ▸
       at 14 2 (CS13⁻ ∷ CCZ124 ∷ []) (wl1151 (lit c4)) ▸
       at 15 2 (CX03 ∷ CCZ124 ∷ []) (lem-comm-CCZ124-CX03 (lit c4)) ▸ done

  b3 : Chain (X4 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ013 ∷ K1 ∷ Toff124 ∷ CCZ124 ∷ CZ12 ∷ CK41 ∷ CZ12 ∷ S4 ∷ CS13 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ CCZ124 ∷ CS01 ∷ X4 ∷ CCZ013 ∷ []) (X4 ∷ Toff203 ∷ CCZ124 ∷ CCZ013 ∷ K1 ∷ CK41 ∷ S4 ∷ CCZ013 ∷ Toff203 ∷ CCZ124 ∷ X4 ∷ CCZ013 ∷ [])
  b3 = at 16 2 (CS01 ∷ CCZ124 ∷ []) (wp0919 c4) ▸
       at 12 5 (CCZ013 ∷ []) (sym (wl0905 (lit c4))) ▸
       at 5 7 (K1 ∷ CK41 ∷ S4 ∷ []) (sym (wl1162 (lit c4))) ▸
       at 3 2 (CCZ013 ∷ Toff203 ∷ []) (sym (wl1131 (lit c4))) ▸
       at 4 2 (K1 ∷ Toff203 ∷ []) (sym (wl1163 (lit c4))) ▸
       at 5 2 (CK41 ∷ Toff203 ∷ []) (lem-comm-TOFF203-CK41 (lit c4)) ▸
       at 6 2 (S4 ∷ Toff203 ∷ []) (c₄ (Swap ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑) (S)) ▸
       at 7 2 (CCZ013 ∷ Toff203 ∷ []) (sym (wl1131 (lit c4))) ▸ done

  b4 : Chain (X4 ∷ Toff203 ∷ CCZ124 ∷ CCZ013 ∷ K1 ∷ CK41 ∷ S4 ∷ CCZ013 ∷ Toff203 ∷ CCZ124 ∷ X4 ∷ CCZ013 ∷ []) (X4 ∷ Toff203 ∷ CCZ013 ∷ K1 ∷ Toff124 ∷ CCZ124 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CCZ013 ∷ Toff203 ∷ CCZ124 ∷ X4 ∷ CCZ013 ∷ [])
  b4 = at 3 1 (CS13 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ []) (wl0905 (lit c4)) ▸
       at 2 2 (CS13 ∷ CCZ124 ∷ []) (wl1152 (lit c4)) ▸
       at 3 2 (CX03 ∷ CCZ124 ∷ []) (lem-comm-CCZ124-CX03 (lit c4)) ▸
       at 4 2 (CS13⁻ ∷ CCZ124 ∷ []) (wl1151 (lit c4)) ▸
       at 5 2 (CX03 ∷ CCZ124 ∷ []) (lem-comm-CCZ124-CX03 (lit c4)) ▸
       at 6 2 (CS01 ∷ CCZ124 ∷ []) (wp0919 c4) ▸
       at 2 5 (CCZ013 ∷ []) (sym (wl0905 (lit c4))) ▸
       at 3 2 (K1 ∷ Toff124 ∷ CCZ124 ∷ CCZ124 ∷ []) (wl1159 (lit c4)) ▸ done

  b5 : Chain (X4 ∷ Toff203 ∷ CCZ013 ∷ K1 ∷ Toff124 ∷ CCZ124 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CCZ013 ∷ Toff203 ∷ CCZ124 ∷ X4 ∷ CCZ013 ∷ []) (X4 ∷ Toff203 ∷ CCZ013 ∷ K1 ∷ Toff124 ∷ CCZ124 ∷ CZ12 ∷ CK41 ∷ CZ12 ∷ S4 ∷ CS13 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X4 ∷ CCZ013 ∷ [])
  b5 = at 6 2 (CZ12 ∷ CK41 ∷ CZ12 ∷ CCZ124 ∷ []) (wl1160 (lit c4)) ▸
       at 9 2 (S4 ∷ CCZ124 ∷ []) (wl1161 (lit c4)) ▸
       at 11 1 (CS13 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ []) (wl0905 (lit c4)) ▸
       at 10 2 (CS13 ∷ CCZ124 ∷ []) (wl1152 (lit c4)) ▸
       at 11 2 (CX03 ∷ CCZ124 ∷ []) (lem-comm-CCZ124-CX03 (lit c4)) ▸
       at 12 2 (CS13⁻ ∷ CCZ124 ∷ []) (wl1151 (lit c4)) ▸
       at 13 2 (CX03 ∷ CCZ124 ∷ []) (lem-comm-CCZ124-CX03 (lit c4)) ▸
       at 14 2 (CS01 ∷ CCZ124 ∷ []) (wp0919 c4) ▸ done

  b6 : Chain (X4 ∷ Toff203 ∷ CCZ013 ∷ K1 ∷ Toff124 ∷ CCZ124 ∷ CZ12 ∷ CK41 ∷ CZ12 ∷ S4 ∷ CS13 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X4 ∷ CCZ013 ∷ []) (X4 ∷ CCZ013 ∷ K1 ∷ CK41 ∷ S4 ∷ CCZ013 ∷ Bx2-0341 ∷ X4 ∷ CCZ013 ∷ [])
  b6 = at 10 5 (CCZ013 ∷ []) (sym (wl0905 (lit c4))) ▸
       at 3 7 (K1 ∷ CK41 ∷ S4 ∷ []) (sym (wl1162 (lit c4))) ▸
       at 1 2 (CCZ013 ∷ Toff203 ∷ []) (sym (wl1131 (lit c4))) ▸
       at 2 2 (K1 ∷ Toff203 ∷ []) (sym (wl1163 (lit c4))) ▸
       at 3 2 (CK41 ∷ Toff203 ∷ []) (lem-comm-TOFF203-CK41 (lit c4)) ▸
       at 4 2 (S4 ∷ Toff203 ∷ []) (c₄ (Swap ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑) (S)) ▸
       at 5 2 (CCZ013 ∷ Toff203 ∷ []) (sym (wl1131 (lit c4))) ▸
       at 6 4 (Bx2-0341 ∷ []) (sym (lem-box-tQ-at0210233441 c4)) ▸ done

  b7 : Chain (X4 ∷ CCZ013 ∷ K1 ∷ CK41 ∷ S4 ∷ CCZ013 ∷ Bx2-0341 ∷ X4 ∷ CCZ013 ∷ []) (CCZ013 ∷ CK41 ∷ CCZ013 ∷ Bx2-0341 ∷ [])
  b7 = at 6 1 (Bx2-0431 ∷ []) (sym (lem-box-perm-1324-at02102441 c4)) ▸
       at 0 6 (CCZ013 ∷ CK41 ∷ CCZ013 ∷ X4 ∷ []) (sym (wp0952 c4)) ▸
       at 3 3 (Bx2-0431 ∷ CCZ013 ∷ []) (lem-Xb-box-at02102441 c4) ▸
       at 4 2 [] (wl0230 (lit c4)) ▸
       at 3 1 (Bx2-0341 ∷ []) (lem-box-perm-1324-at02102441 c4) ▸ done


-- box-perm-1342 @0210233441: 3 steps
lem-box-perm-1342-at0210233441 : Ws → ⟪ (Bx2-0341 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ []) ⟫ʷ
lem-box-perm-1342-at0210233441 c4 = run b0
  where
  b0 : Chain (Bx2-0341 ∷ []) (Bx2-0413 ∷ [])
  b0 = at 0 1 (Bx2-4103 ∷ []) (lem-pairs-at0210233441 c4) ▸
       at 0 1 (Bx2-4013 ∷ []) (lem-sym-bc-at0214213043 c4) ▸
       at 0 1 (Bx2-0413 ∷ []) (lem-sym-ab-at0214203143 c4) ▸ done


-- nf-X-CS1@0: 115 steps
lem-nf-X-CS1at0 : Ws → ⟪ (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ CCZ013 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ CCZ013 ∷ S4 ∷ CS04 ∷ Bx2-0413 ∷ []) ⟫ʷ
lem-nf-X-CS1at0 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (run b14))))))))))))))
  where
  b0 : Chain (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS04 ∷ []) (CCZ014 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ CCZ014 ∷ CCZ024 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ Toff213 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS04 ∷ [])
  b0 = at 0 2 (CCZ014 ∷ []) (lem-S2-SBOX⟨2·0·41·3⟩ c4) ▸
       at 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 1 (CS03 ∷ []) (refl) ▸
       at 5 1 (CS03⁻ ∷ []) (refl) ▸
       at 1 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 4 2 (Toff214 ∷ Toff314 ∷ Toff213 ∷ []) (wl0747 (lit c4)) ▸
       at 3 2 (Toff214 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp0654 c4) ▸
       at 6 1 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (sym (wl0190 (lit c4))) ▸ done

  b1 : Chain (CCZ014 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ CCZ014 ∷ CCZ024 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ Toff213 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS04 ∷ []) (CCZ014 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ CCZ014 ∷ Toff314 ∷ CCZ024 ∷ Toff213 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS04 ∷ [])
  b1 = at 5 2 (K3 ∷ CCZ024 ∷ []) (wp0037 c4) ▸
       at 6 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 7 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 8 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 9 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 10 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 11 2 (K3⁻ ∷ CCZ024 ∷ []) (wp0033 c4) ▸
       at 5 7 (Toff314 ∷ []) (wl0190 (lit c4)) ▸ done

  b2 : Chain (CCZ014 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ CCZ014 ∷ Toff314 ∷ CCZ024 ∷ Toff213 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS04 ∷ []) (CCZ014 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff213 ∷ Toff314 ∷ CCZ024 ∷ Toff213 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS04 ∷ [])
  b2 = at 2 2 (Toff214 ∷ Toff213 ∷ []) (wl0197 (lit c4)) ▸
       at 4 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4) ▸
       at 3 2 (CS14 ∷ Toff213 ∷ []) (sym (wl0195 (lit c4))) ▸
       at 4 2 (CX04 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX04 (lit c4)) ▸
       at 5 2 (CS14⁻ ∷ Toff213 ∷ []) (sym (wl0194 (lit c4))) ▸
       at 6 2 (CX04 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX04 (lit c4)) ▸
       at 7 2 (CS01 ∷ Toff213 ∷ []) (sym (wl0193 (lit c4))) ▸
       at 3 5 (CCZ014 ∷ []) (sym (wp0041 c4)) ▸ done

  b3 : Chain (CCZ014 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff213 ∷ Toff314 ∷ CCZ024 ∷ Toff213 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS04 ∷ []) (CCZ014 ∷ CCZ014 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CCZ024 ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS04 ∷ [])
  b3 = at 4 2 (Toff214 ∷ Toff314 ∷ Toff213 ∷ []) (wl0747 (lit c4)) ▸
       at 2 3 (CCZ014 ∷ []) (sym (wp0044 c4)) ▸
       at 1 2 (CCZ014 ∷ CCZ024 ∷ []) (sym (wp0038 c4)) ▸
       at 3 1 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (sym (wl0190 (lit c4))) ▸
       at 2 2 (K3 ∷ CCZ024 ∷ []) (wp0037 c4) ▸
       at 3 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 4 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 5 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸ done

  b4 : Chain (CCZ014 ∷ CCZ014 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CCZ024 ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS04 ∷ []) (CCZ014 ∷ CCZ014 ∷ Toff314 ∷ CCZ024 ∷ Toff213 ∷ CS03 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03⁻ ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS04 ∷ [])
  b4 = at 6 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 7 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 8 2 (K3⁻ ∷ CCZ024 ∷ []) (wp0033 c4) ▸
       at 2 7 (Toff314 ∷ []) (wl0190 (lit c4)) ▸
       at 3 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 3 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 6 2 (CS03 ∷ Toff213 ∷ []) (sym (wl0196 (lit c4))) ▸
       at 5 2 (CS03 ∷ CCZ024 ∷ []) (wp0021 c4) ▸ done

  b5 : Chain (CCZ014 ∷ CCZ014 ∷ Toff314 ∷ CCZ024 ∷ Toff213 ∷ CS03 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03⁻ ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS04 ∷ []) (CCZ014 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ CCZ014 ∷ K3 ∷ CCZ024 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ Toff213 ∷ CS03⁻ ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS04 ∷ [])
  b5 = at 4 2 (CS03 ∷ Toff213 ∷ []) (sym (wl0196 (lit c4))) ▸
       at 3 2 (CS03 ∷ CCZ024 ∷ []) (wp0021 c4) ▸
       at 4 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 4 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 7 2 (Toff214 ∷ Toff314 ∷ Toff213 ∷ []) (wl0747 (lit c4)) ▸
       at 6 2 (Toff214 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp0654 c4) ▸
       at 9 1 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (sym (wl0190 (lit c4))) ▸
       at 8 2 (K3 ∷ CCZ024 ∷ []) (wp0037 c4) ▸ done

  b6 : Chain (CCZ014 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ CCZ014 ∷ K3 ∷ CCZ024 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ Toff213 ∷ CS03⁻ ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS04 ∷ []) (CCZ014 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ024 ∷ Toff214 ∷ Toff213 ∷ CCZ014 ∷ Toff314 ∷ CCZ024 ∷ Toff213 ∷ CS03⁻ ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS04 ∷ [])
  b6 = at 9 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 10 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 11 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 12 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 13 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 14 2 (K3⁻ ∷ CCZ024 ∷ []) (wp0033 c4) ▸
       at 8 7 (Toff314 ∷ []) (wl0190 (lit c4)) ▸
       at 5 2 (Toff214 ∷ Toff213 ∷ []) (wl0197 (lit c4)) ▸ done

  b7 : Chain (CCZ014 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ024 ∷ Toff214 ∷ Toff213 ∷ CCZ014 ∷ Toff314 ∷ CCZ024 ∷ Toff213 ∷ CS03⁻ ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS04 ∷ []) (CCZ014 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ Toff314 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS03⁻ ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS04 ∷ [])
  b7 = at 7 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4) ▸
       at 6 2 (CS14 ∷ Toff213 ∷ []) (sym (wl0195 (lit c4))) ▸
       at 7 2 (CX04 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX04 (lit c4)) ▸
       at 8 2 (CS14⁻ ∷ Toff213 ∷ []) (sym (wl0194 (lit c4))) ▸
       at 9 2 (CX04 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX04 (lit c4)) ▸
       at 10 2 (CS01 ∷ Toff213 ∷ []) (sym (wl0193 (lit c4))) ▸
       at 6 5 (CCZ014 ∷ []) (sym (wp0041 c4)) ▸
       at 7 2 (Toff214 ∷ Toff314 ∷ Toff213 ∷ []) (wl0747 (lit c4)) ▸ done

  b8 : Chain (CCZ014 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ Toff314 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS03⁻ ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS04 ∷ []) (CCZ014 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ K3⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS03⁻ ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS04 ∷ [])
  b8 = at 5 3 (CCZ014 ∷ []) (sym (wp0044 c4)) ▸
       at 4 2 (CCZ014 ∷ CCZ024 ∷ []) (sym (wp0038 c4)) ▸
       at 6 1 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (sym (wl0190 (lit c4))) ▸
       at 5 2 (K3 ∷ CCZ024 ∷ []) (wp0037 c4) ▸
       at 6 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 7 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 8 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 9 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸ done

  b9 : Chain (CCZ014 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ K3⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS03⁻ ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS04 ∷ []) (CCZ014 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CCZ024 ∷ CS03⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS04 ∷ [])
  b9 = at 10 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 11 2 (K3⁻ ∷ CCZ024 ∷ []) (wp0033 c4) ▸
       at 5 7 (Toff314 ∷ []) (wl0190 (lit c4)) ▸
       at 6 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 6 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 9 2 (CS03⁻ ∷ Toff213 ∷ []) (sym (wl0191 (lit c4))) ▸
       at 8 2 (CS03⁻ ∷ CCZ024 ∷ []) (wp0032 c4) ▸
       at 7 2 (CS03⁻ ∷ Toff213 ∷ []) (sym (wl0191 (lit c4))) ▸ done

  b10 : Chain (CCZ014 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CCZ024 ∷ CS03⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS04 ∷ []) (CCZ014 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ CCZ013 ∷ CK41 ∷ CCZ013 ∷ CCZ024 ∷ Toff213 ∷ CS14 ∷ CCZ024 ∷ Toff213 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS04 ∷ [])
  b10 = at 6 2 (CS03⁻ ∷ CCZ024 ∷ []) (wp0032 c4) ▸
       at 7 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 7 1 (Bx2-0341 ∷ []) (lem-box-perm-1423-at0210243143 c4) ▸
       at 7 2 (CCZ013 ∷ CK41 ∷ CCZ013 ∷ Bx2-0341 ∷ []) (lem-CKc-box-at0210233441 c4) ▸
       at 10 1 (Bx2-0413 ∷ []) (lem-box-perm-1342-at0210233441 c4) ▸
       at 10 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 13 2 (CS14 ∷ Toff213 ∷ []) (sym (wl0195 (lit c4))) ▸
       at 12 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸ done

  b11 : Chain (CCZ014 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ CCZ013 ∷ CK41 ∷ CCZ013 ∷ CCZ024 ∷ Toff213 ∷ CS14 ∷ CCZ024 ∷ Toff213 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS04 ∷ []) (CCZ014 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ CCZ013 ∷ CK41 ∷ CCZ013 ∷ CS14 ∷ CS14 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CK41 ∷ S4 ∷ CS04 ∷ [])
  b11 = at 11 2 (CS14 ∷ Toff213 ∷ []) (sym (wl0195 (lit c4))) ▸
       at 10 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 11 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 11 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 14 2 (CS14 ∷ Toff213 ∷ []) (sym (wl0195 (lit c4))) ▸
       at 13 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 12 2 (CS14 ∷ Toff213 ∷ []) (sym (wl0195 (lit c4))) ▸
       at 11 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸ done

  b12 : Chain (CCZ014 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ CCZ013 ∷ CK41 ∷ CCZ013 ∷ CS14 ∷ CS14 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CK41 ∷ S4 ∷ CS04 ∷ []) (CCZ014 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ CCZ013 ∷ CK41 ∷ CCZ013 ∷ CS14 ∷ CS14 ∷ CCZ013 ∷ CK41 ∷ CCZ013 ∷ CCZ024 ∷ S4 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS04 ∷ [])
  b12 = at 12 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 12 1 (Bx2-0341 ∷ []) (lem-box-perm-1423-at0210243143 c4) ▸
       at 12 2 (CCZ013 ∷ CK41 ∷ CCZ013 ∷ Bx2-0341 ∷ []) (lem-CKc-box-at0210233441 c4) ▸
       at 15 1 (Bx2-0413 ∷ []) (lem-box-perm-1342-at0210233441 c4) ▸
       at 15 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 18 2 (S4 ∷ Toff213 ∷ []) (sym (wl0727 (lit c4))) ▸
       at 17 2 (S4 ∷ CCZ024 ∷ []) (wp0617 c4) ▸
       at 16 2 (S4 ∷ Toff213 ∷ []) (sym (wl0727 (lit c4))) ▸ done

  b13 : Chain (CCZ014 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ CCZ013 ∷ CK41 ∷ CCZ013 ∷ CS14 ∷ CS14 ∷ CCZ013 ∷ CK41 ∷ CCZ013 ∷ CCZ024 ∷ S4 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS04 ∷ []) (CCZ014 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ CCZ013 ∷ CK41 ∷ CCZ013 ∷ CS14 ∷ CS14 ∷ CCZ013 ∷ CK41 ∷ CCZ013 ∷ S4 ∷ CS04 ∷ Bx2-0413 ∷ [])
  b13 = at 15 2 (S4 ∷ CCZ024 ∷ []) (wp0617 c4) ▸
       at 16 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 16 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 19 2 (CS04 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CS04 (lit c4)) ▸
       at 18 2 (CS04 ∷ CCZ024 ∷ []) (wp0906 c4) ▸
       at 17 2 (CS04 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CS04 (lit c4)) ▸
       at 16 2 (CS04 ∷ CCZ024 ∷ []) (wp0906 c4) ▸
       at 17 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸ done

  b14 : Chain (CCZ014 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ CCZ013 ∷ CK41 ∷ CCZ013 ∷ CS14 ∷ CS14 ∷ CCZ013 ∷ CK41 ∷ CCZ013 ∷ S4 ∷ CS04 ∷ Bx2-0413 ∷ []) (Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ CCZ013 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ CCZ013 ∷ S4 ∷ CS04 ∷ Bx2-0413 ∷ [])
  b14 = at 0 2 [] (wp0161 c4) ▸
       at 7 3 (CS14 ∷ CS14 ∷ CCZ013 ∷ []) (wp0953 c4) ▸
       at 9 2 [] (wl0230 (lit c4)) ▸ done


-- F1-X-CS1@0: 86 steps
lem-F1-X-CS1at0 : Ws → ⟪ (CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS04 ∷ []) ⟫ʷ
lem-F1-X-CS1at0 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (run b10))))))))))
  where
  b0 : Chain (CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ []) (CX41 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ CCZ014 ∷ CCZ024 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ Toff213 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b0 = at 5 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 7 1 (CS03 ∷ []) (refl) ▸
       at 9 1 (CS03⁻ ∷ []) (refl) ▸
       at 0 5 (CX41 ∷ []) (wl1142 (lit c4)) ▸
       at 1 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 4 2 (Toff214 ∷ Toff314 ∷ Toff213 ∷ []) (wl0747 (lit c4)) ▸
       at 3 2 (Toff214 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp0654 c4) ▸
       at 6 1 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (sym (wl0190 (lit c4))) ▸ done

  b1 : Chain (CX41 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ CCZ014 ∷ CCZ024 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ Toff213 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (CX41 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ CCZ014 ∷ Toff314 ∷ CCZ024 ∷ Toff213 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b1 = at 5 2 (K3 ∷ CCZ024 ∷ []) (wp0037 c4) ▸
       at 6 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 7 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 8 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 9 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 10 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 11 2 (K3⁻ ∷ CCZ024 ∷ []) (wp0033 c4) ▸
       at 5 7 (Toff314 ∷ []) (wl0190 (lit c4)) ▸ done

  b2 : Chain (CX41 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ CCZ014 ∷ Toff314 ∷ CCZ024 ∷ Toff213 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (CX41 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff213 ∷ Toff314 ∷ CCZ024 ∷ Toff213 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b2 = at 2 2 (Toff214 ∷ Toff213 ∷ []) (wl0197 (lit c4)) ▸
       at 4 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4) ▸
       at 3 2 (CS14 ∷ Toff213 ∷ []) (sym (wl0195 (lit c4))) ▸
       at 4 2 (CX04 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX04 (lit c4)) ▸
       at 5 2 (CS14⁻ ∷ Toff213 ∷ []) (sym (wl0194 (lit c4))) ▸
       at 6 2 (CX04 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX04 (lit c4)) ▸
       at 7 2 (CS01 ∷ Toff213 ∷ []) (sym (wl0193 (lit c4))) ▸
       at 3 5 (CCZ014 ∷ []) (sym (wp0041 c4)) ▸ done

  b3 : Chain (CX41 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff213 ∷ Toff314 ∷ CCZ024 ∷ Toff213 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (CX41 ∷ CCZ014 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CCZ024 ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b3 = at 4 2 (Toff214 ∷ Toff314 ∷ Toff213 ∷ []) (wl0747 (lit c4)) ▸
       at 2 3 (CCZ014 ∷ []) (sym (wp0044 c4)) ▸
       at 1 2 (CCZ014 ∷ CCZ024 ∷ []) (sym (wp0038 c4)) ▸
       at 3 1 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (sym (wl0190 (lit c4))) ▸
       at 2 2 (K3 ∷ CCZ024 ∷ []) (wp0037 c4) ▸
       at 3 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 4 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 5 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸ done

  b4 : Chain (CX41 ∷ CCZ014 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CCZ024 ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (CX41 ∷ CCZ014 ∷ Toff314 ∷ CCZ024 ∷ Toff213 ∷ CS03 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b4 = at 6 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 7 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 8 2 (K3⁻ ∷ CCZ024 ∷ []) (wp0033 c4) ▸
       at 2 7 (Toff314 ∷ []) (wl0190 (lit c4)) ▸
       at 3 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 3 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 6 2 (CS03 ∷ Toff213 ∷ []) (sym (wl0196 (lit c4))) ▸
       at 5 2 (CS03 ∷ CCZ024 ∷ []) (wp0021 c4) ▸ done

  b5 : Chain (CX41 ∷ CCZ014 ∷ Toff314 ∷ CCZ024 ∷ Toff213 ∷ CS03 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03⁻ ∷ []) (CX41 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ CCZ014 ∷ K3 ∷ CCZ024 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ Toff213 ∷ CS03⁻ ∷ [])
  b5 = at 4 2 (CS03 ∷ Toff213 ∷ []) (sym (wl0196 (lit c4))) ▸
       at 3 2 (CS03 ∷ CCZ024 ∷ []) (wp0021 c4) ▸
       at 4 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 4 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 7 2 (Toff214 ∷ Toff314 ∷ Toff213 ∷ []) (wl0747 (lit c4)) ▸
       at 6 2 (Toff214 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp0654 c4) ▸
       at 9 1 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (sym (wl0190 (lit c4))) ▸
       at 8 2 (K3 ∷ CCZ024 ∷ []) (wp0037 c4) ▸ done

  b6 : Chain (CX41 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ CCZ014 ∷ K3 ∷ CCZ024 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ Toff213 ∷ CS03⁻ ∷ []) (CX41 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ024 ∷ Toff214 ∷ Toff213 ∷ CCZ014 ∷ Toff314 ∷ CCZ024 ∷ Toff213 ∷ CS03⁻ ∷ [])
  b6 = at 9 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 10 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 11 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 12 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 13 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 14 2 (K3⁻ ∷ CCZ024 ∷ []) (wp0033 c4) ▸
       at 8 7 (Toff314 ∷ []) (wl0190 (lit c4)) ▸
       at 5 2 (Toff214 ∷ Toff213 ∷ []) (wl0197 (lit c4)) ▸ done

  b7 : Chain (CX41 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ024 ∷ Toff214 ∷ Toff213 ∷ CCZ014 ∷ Toff314 ∷ CCZ024 ∷ Toff213 ∷ CS03⁻ ∷ []) (CX41 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ Toff314 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS03⁻ ∷ [])
  b7 = at 7 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4) ▸
       at 6 2 (CS14 ∷ Toff213 ∷ []) (sym (wl0195 (lit c4))) ▸
       at 7 2 (CX04 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX04 (lit c4)) ▸
       at 8 2 (CS14⁻ ∷ Toff213 ∷ []) (sym (wl0194 (lit c4))) ▸
       at 9 2 (CX04 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX04 (lit c4)) ▸
       at 10 2 (CS01 ∷ Toff213 ∷ []) (sym (wl0193 (lit c4))) ▸
       at 6 5 (CCZ014 ∷ []) (sym (wp0041 c4)) ▸
       at 7 2 (Toff214 ∷ Toff314 ∷ Toff213 ∷ []) (wl0747 (lit c4)) ▸ done

  b8 : Chain (CX41 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ Toff314 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS03⁻ ∷ []) (CX41 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ K3⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS03⁻ ∷ [])
  b8 = at 5 3 (CCZ014 ∷ []) (sym (wp0044 c4)) ▸
       at 4 2 (CCZ014 ∷ CCZ024 ∷ []) (sym (wp0038 c4)) ▸
       at 6 1 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (sym (wl0190 (lit c4))) ▸
       at 5 2 (K3 ∷ CCZ024 ∷ []) (wp0037 c4) ▸
       at 6 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 7 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 8 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 9 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸ done

  b9 : Chain (CX41 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ K3⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS03⁻ ∷ []) (CX41 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CCZ024 ∷ CS03⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ [])
  b9 = at 10 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 11 2 (K3⁻ ∷ CCZ024 ∷ []) (wp0033 c4) ▸
       at 5 7 (Toff314 ∷ []) (wl0190 (lit c4)) ▸
       at 6 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 6 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 9 2 (CS03⁻ ∷ Toff213 ∷ []) (sym (wl0191 (lit c4))) ▸
       at 8 2 (CS03⁻ ∷ CCZ024 ∷ []) (wp0032 c4) ▸
       at 7 2 (CS03⁻ ∷ Toff213 ∷ []) (sym (wl0191 (lit c4))) ▸ done

  b10 : Chain (CX41 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CCZ024 ∷ CS03⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS04 ∷ [])
  b10 = at 6 2 (CS03⁻ ∷ CCZ024 ∷ []) (wp0032 c4) ▸
       at 7 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 1 3 (Toff314 ∷ CS03 ∷ CCZ014 ∷ []) (wp0651 c4) ▸
       at 3 2 [] (wp0161 c4) ▸
       at 0 5 (Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ CCZ013 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ CCZ013 ∷ S4 ∷ CS04 ∷ []) (wp0954 c4) ▸
       at 0 14 (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS04 ∷ []) (sym (lem-nf-X-CS1at0 c4)) ▸ done


-- CXbc-box @233442: 17 steps
lem-CXbc-box-at233442 : Ws → ⟪ (CX34 ∷ Bx0-1342 ∷ CX34 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1342 ∷ CCZ123 ∷ []) ⟫ʷ
lem-CXbc-box-at233442 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX34 ∷ Bx0-1342 ∷ CX34 ∷ []) (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CX34 ∷ CCZ023 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CCZ024 ∷ CX13 ∷ CS12 ∷ CX34 ∷ [])
  b0 = at 1 1 (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) (lem-box-tQ-at233442 c4) ▸
       at 0 2 (Toff013 ∷ CX34 ∷ []) (wp0286 c4) ▸
       at 1 2 (CCZ024 ∷ CX34 ∷ CCZ023 ∷ []) (sym (wp0911 c4)) ▸
       at 3 2 (Toff013 ∷ CCZ023 ∷ CCZ123 ∷ []) (wl1164 (lit c4)) ▸
       at 2 2 (Toff013 ∷ CX34 ∷ []) (wp0286 c4) ▸
       at 5 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0242 (lit c4)) ▸
       at 9 2 (CCZ024 ∷ CS12 ∷ []) (sym (wp0081 c4)) ▸
       at 8 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸ done

  b1 : Chain (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CX34 ∷ CCZ023 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CCZ024 ∷ CX13 ∷ CS12 ∷ CX34 ∷ []) (Bx0-1342 ∷ CX34 ∷ CCZ123 ∷ CX34 ∷ [])
  b1 = at 7 2 (CCZ024 ∷ CS23⁻ ∷ []) (sym (wp0091 c4)) ▸
       at 6 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ CS23 ∷ []) (sym (wp0092 c4)) ▸
       at 6 5 (CCZ123 ∷ []) (sym (wl0242 (lit c4))) ▸
       at 4 2 (CCZ024 ∷ CCZ023 ∷ []) (wp0669 c4) ▸
       at 3 2 (CCZ024 ∷ CX34 ∷ CCZ023 ∷ []) (sym (wp0911 c4)) ▸
       at 4 3 (CX34 ∷ []) (wp0912 c4) ▸
       at 0 4 (Bx0-1342 ∷ []) (sym (lem-box-tQ-at233442 c4)) ▸ done

  b2 : Chain (Bx0-1342 ∷ CX34 ∷ CCZ123 ∷ CX34 ∷ []) (Bx0-1342 ∷ CCZ123 ∷ [])
  b2 = at 1 3 (CCZ123 ∷ []) (sym (wl0648 (lit c4))) ▸ done


-- CXcb-box @233442: 18 steps
lem-CXcb-box-at233442 : Ws → ⟪ (CX43 ∷ Bx0-1342 ∷ CX43 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1342 ∷ CCZ124 ∷ []) ⟫ʷ
lem-CXcb-box-at233442 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX43 ∷ Bx0-1342 ∷ CX43 ∷ []) (Toff013 ∷ CCZ024 ∷ CX43 ∷ Toff014 ∷ CS24 ∷ CX14 ∷ Toff013 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ CCZ024 ∷ CX43 ∷ [])
  b0 = at 1 1 (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) (lem-box-tQ-at233442 c4) ▸
       at 0 2 (Toff013 ∷ CX43 ∷ Toff014 ∷ []) (wp0955 c4) ▸
       at 2 2 (CCZ024 ∷ Toff014 ∷ CCZ124 ∷ []) (sym (wp0784 c4)) ▸
       at 1 2 (CCZ024 ∷ CX43 ∷ []) (sym (wp0914 c4)) ▸
       at 4 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 8 2 (Toff013 ∷ CS12 ∷ []) (wl0247 (lit c4)) ▸
       at 7 2 (Toff013 ∷ CX14 ∷ []) (wp0281 c4) ▸
       at 6 2 (Toff013 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-TOFF013 (lit c4)) ▸ done

  b1 : Chain (Toff013 ∷ CCZ024 ∷ CX43 ∷ Toff014 ∷ CS24 ∷ CX14 ∷ Toff013 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ CCZ024 ∷ CX43 ∷ []) (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ CX43 ∷ CCZ124 ∷ CX43 ∷ [])
  b1 = at 5 2 (Toff013 ∷ CX14 ∷ []) (wp0281 c4) ▸
       at 4 2 (Toff013 ∷ CS24 ∷ []) (lem-comm-CS24-TOFF013 (lit c4)) ▸
       at 5 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 3 2 (Toff013 ∷ Toff014 ∷ []) (sym (wp0786 c4)) ▸
       at 2 2 (Toff013 ∷ CX43 ∷ Toff014 ∷ []) (wp0955 c4) ▸
       at 3 3 (CX43 ∷ []) (wp0956 c4) ▸
       at 4 2 (CCZ024 ∷ CCZ124 ∷ []) (sym (wp0827 c4)) ▸
       at 3 2 (CCZ024 ∷ CX43 ∷ []) (sym (wp0914 c4)) ▸ done

  b2 : Chain (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ CX43 ∷ CCZ124 ∷ CX43 ∷ []) (Bx0-1342 ∷ CCZ124 ∷ [])
  b2 = at 0 4 (Bx0-1342 ∷ []) (sym (lem-box-tQ-at233442 c4)) ▸
       at 1 3 (CCZ124 ∷ []) (sym (wl0646 (lit c4))) ▸ done


-- SWbc-box @233442: 11 steps
lem-SWbc-box-at233442 : Ws → ⟪ (Sw34 ∷ Bx0-1342 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1342 ∷ []) ⟫ʷ
lem-SWbc-box-at233442 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw34 ∷ Bx0-1342 ∷ Sw34 ∷ []) (CX34 ∷ Bx0-1342 ∷ CX34 ∷ CCZ123 ∷ CCZ124 ∷ CCZ123 ∷ CCZ124 ∷ CCZ123 ∷ [])
  b0 = at 0 1 (CX34 ∷ CX43 ∷ CX34 ∷ []) (sym (wl0547 (lit c4))) ▸
       at 4 1 (CX34 ∷ CX43 ∷ CX34 ∷ []) (sym (wl0547 (lit c4))) ▸
       at 2 3 (Bx0-1342 ∷ CCZ123 ∷ []) (lem-CXbc-box-at233442 c4) ▸
       at 3 2 (CX43 ∷ CCZ124 ∷ CCZ123 ∷ []) (wl0652 (lit c4)) ▸
       at 1 3 (Bx0-1342 ∷ CCZ124 ∷ []) (lem-CXcb-box-at233442 c4) ▸
       at 4 2 (CX34 ∷ CCZ123 ∷ []) (wl1008 (lit c4)) ▸
       at 3 2 (CX34 ∷ CCZ123 ∷ CCZ124 ∷ []) (wl0650 (lit c4)) ▸
       at 2 2 (CX34 ∷ CCZ123 ∷ CCZ124 ∷ []) (wl0650 (lit c4)) ▸ done

  b1 : Chain (CX34 ∷ Bx0-1342 ∷ CX34 ∷ CCZ123 ∷ CCZ124 ∷ CCZ123 ∷ CCZ124 ∷ CCZ123 ∷ []) (Bx0-1342 ∷ [])
  b1 = at 3 5 (CCZ123 ∷ []) (wl1009 (lit c4)) ▸
       at 0 3 (Bx0-1342 ∷ CCZ123 ∷ []) (lem-CXbc-box-at233442 c4) ▸
       at 1 2 [] (wl0181 (lit c4)) ▸ done


-- nat-SWbc @233442: 23 steps
lem-nat-SWbc-at233442 : Ws → ⟪ (Sw34 ∷ Bx0-1342 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1432 ∷ []) ⟫ʷ
lem-nat-SWbc-at233442 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw34 ∷ Bx0-1342 ∷ Sw34 ∷ []) (CCZ014 ∷ Toff014 ∷ CCZ013 ∷ Toff103 ∷ Bx0-12 ∷ Toff103 ∷ Sw34 ∷ CCZ014 ∷ Bx0-12 ∷ Toff013 ∷ CCZ013 ∷ Bx1-042 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff013 ∷ Bx1-042 ∷ Toff013 ∷ CCZ013 ∷ Bx1-042 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw34 ∷ []) (sym (wp0398 c4)) ▸
       at 1 2 (Toff014 ∷ Sw34 ∷ []) (wp0957 c4) ▸
       at 3 1 (CCZ014 ∷ Toff104 ∷ Bx0-12 ∷ Toff104 ∷ CCZ014 ∷ Bx0-12 ∷ []) (refl) ▸
       at 2 2 (CCZ013 ∷ Sw34 ∷ []) (sym (wp0958 c4)) ▸
       at 3 2 (Toff103 ∷ Sw34 ∷ []) (wp0959 c4) ▸
       at 4 2 (Bx0-12 ∷ Sw34 ∷ []) (sym (c₃ (CZ ↑) (Swap))) ▸
       at 5 2 (Toff103 ∷ Sw34 ∷ []) (wp0959 c4) ▸ done

  b1 : Chain (CCZ014 ∷ Toff014 ∷ CCZ013 ∷ Toff103 ∷ Bx0-12 ∷ Toff103 ∷ Sw34 ∷ CCZ014 ∷ Bx0-12 ∷ Toff013 ∷ CCZ013 ∷ Bx1-042 ∷ Sw34 ∷ []) (CCZ014 ∷ Toff014 ∷ CCZ013 ∷ Toff103 ∷ Bx0-12 ∷ Toff103 ∷ CCZ013 ∷ Bx0-12 ∷ Toff014 ∷ CCZ014 ∷ CCZ013 ∷ Toff103 ∷ Bx0-12 ∷ Sw34 ∷ Toff104 ∷ CCZ014 ∷ Bx0-12 ∷ Sw34 ∷ [])
  b1 = at 6 2 (CCZ013 ∷ Sw34 ∷ []) (sym (wp0958 c4)) ▸
       at 7 2 (Bx0-12 ∷ Sw34 ∷ []) (sym (c₃ (CZ ↑) (Swap))) ▸
       at 8 2 (Toff014 ∷ Sw34 ∷ []) (wp0957 c4) ▸
       at 9 2 (CCZ014 ∷ Sw34 ∷ []) (sym (wp0398 c4)) ▸
       at 11 1 (CCZ014 ∷ Toff104 ∷ Bx0-12 ∷ Toff104 ∷ CCZ014 ∷ Bx0-12 ∷ []) (refl) ▸
       at 10 2 (CCZ013 ∷ Sw34 ∷ []) (sym (wp0958 c4)) ▸
       at 11 2 (Toff103 ∷ Sw34 ∷ []) (wp0959 c4) ▸
       at 12 2 (Bx0-12 ∷ Sw34 ∷ []) (sym (c₃ (CZ ↑) (Swap))) ▸ done

  b2 : Chain (CCZ014 ∷ Toff014 ∷ CCZ013 ∷ Toff103 ∷ Bx0-12 ∷ Toff103 ∷ CCZ013 ∷ Bx0-12 ∷ Toff014 ∷ CCZ014 ∷ CCZ013 ∷ Toff103 ∷ Bx0-12 ∷ Sw34 ∷ Toff104 ∷ CCZ014 ∷ Bx0-12 ∷ Sw34 ∷ []) (Bx0-1432 ∷ [])
  b2 = at 13 2 (Toff103 ∷ Sw34 ∷ []) (wp0959 c4) ▸
       at 14 2 (CCZ013 ∷ Sw34 ∷ []) (sym (wp0958 c4)) ▸
       at 15 2 (Bx0-12 ∷ Sw34 ∷ []) (sym (c₃ (CZ ↑) (Swap))) ▸
       at 16 2 [] (wl0004 (lit c4)) ▸
       at 2 6 (Bx1-032 ∷ []) (refl) ▸
       at 5 6 (Bx1-032 ∷ []) (refl) ▸
       at 0 6 (Bx0-1432 ∷ []) (refl) ▸ done


-- sym-bc @233442: 2 steps
lem-sym-bc-at233442 : Ws → ⟪ (Bx0-1342 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1432 ∷ []) ⟫ʷ
lem-sym-bc-at233442 c4 = run b0
  where
  b0 : Chain (Bx0-1342 ∷ []) (Bx0-1432 ∷ [])
  b0 = at 0 1 (Sw34 ∷ Bx0-1342 ∷ Sw34 ∷ []) (sym (lem-SWbc-box-at233442 c4)) ▸
       at 0 3 (Bx0-1432 ∷ []) (lem-nat-SWbc-at233442 c4) ▸ done


-- box-perm-1324 @233442: 1 steps
lem-box-perm-1324-at233442 : Ws → ⟪ (Bx0-1342 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1432 ∷ []) ⟫ʷ
lem-box-perm-1324-at233442 c4 = run b0
  where
  b0 : Chain (Bx0-1342 ∷ []) (Bx0-1432 ∷ [])
  b0 = at 0 1 (Bx0-1432 ∷ []) (lem-sym-bc-at233442 c4) ▸ done


-- tP @2442: 7 steps
lem-tP-at2442 : Ws → ⟪ (Toff014 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ Toff014 ∷ []) ⟫ʷ
lem-tP-at2442 c4 = run b0
  where
  b0 : Chain (Toff014 ∷ Toff023 ∷ []) (Toff023 ∷ Toff014 ∷ [])
  b0 = at 0 1 (K0 ∷ CCZ014 ∷ K0⁻ ∷ []) (sym (wp0049 c4)) ▸
       at 3 1 (K0 ∷ CCZ023 ∷ K0⁻ ∷ []) (sym (wl0200 (lit c4))) ▸
       at 2 2 [] (wl0157 (lit c4)) ▸
       at 1 2 (CCZ023 ∷ CCZ014 ∷ []) (lem-cQ-at2442 c4) ▸
       at 2 0 (K0⁻ ∷ K0 ∷ []) (sym (wl0157 (lit c4))) ▸
       at 0 3 (Toff023 ∷ []) (wl0200 (lit c4)) ▸
       at 1 3 (Toff014 ∷ []) (wp0049 c4) ▸ done


-- VPQ @2442: 14 steps
lem-VPQ-at2442 : Ws → ⟪ (Toff014 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ []) ⟫ʷ
lem-VPQ-at2442 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff014 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ []) (CS23⁻ ∷ CS14⁻ ∷ S0 ∷ Toff023 ∷ Toff014 ∷ S0⁻ ∷ [])
  b0 = at 0 2 (CS14⁻ ∷ S0 ∷ Toff014 ∷ S0⁻ ∷ []) (sym (wp0050 c4)) ▸
       at 4 2 (CS23⁻ ∷ S0 ∷ Toff023 ∷ S0⁻ ∷ []) (sym (wl0201 (lit c4))) ▸
       at 3 2 (CS23⁻ ∷ S0⁻ ∷ []) (c₁ (S • S • S) ((CS • CS • CS) ↑)) ▸
       at 2 2 (CS23⁻ ∷ Toff014 ∷ []) (lem-comm-TOFF014-CSd23 (lit c4)) ▸
       at 1 2 (CS23⁻ ∷ S0 ∷ []) (c₁ (S) ((CS • CS • CS) ↑)) ▸
       at 0 2 (CS23⁻ ∷ CS14⁻ ∷ []) (wl0202 (lit c4)) ▸
       at 4 2 [] (wl0159 (lit c4)) ▸
       at 3 2 (Toff023 ∷ Toff014 ∷ []) (lem-tP-at2442 c4) ▸ done

  b1 : Chain (CS23⁻ ∷ CS14⁻ ∷ S0 ∷ Toff023 ∷ Toff014 ∷ S0⁻ ∷ []) (Toff023 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ [])
  b1 = at 4 0 (S0⁻ ∷ S0 ∷ []) (sym (wl0159 (lit c4))) ▸
       at 1 2 (S0 ∷ CS14⁻ ∷ []) (sym (c₁ (S) (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑))) ▸
       at 2 2 (Toff023 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-TOFF023 (lit c4)) ▸
       at 3 2 (S0⁻ ∷ CS14⁻ ∷ []) (sym (c₁ (S • S • S) (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑))) ▸
       at 0 4 (Toff023 ∷ CCZ023 ∷ []) (wl0201 (lit c4)) ▸
       at 2 4 (Toff014 ∷ CCZ014 ∷ []) (wp0050 c4) ▸ done


-- QVQ @2442: 3 steps
lem-QVQ-at2442 : Ws → ⟪ (CCZ023 ∷ Toff014 ∷ CCZ014 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ Toff014 ∷ CCZ014 ∷ Toff023 ∷ []) ⟫ʷ
lem-QVQ-at2442 c4 = run b0
  where
  b0 : Chain (CCZ023 ∷ Toff014 ∷ CCZ014 ∷ CCZ023 ∷ []) (Toff023 ∷ Toff014 ∷ CCZ014 ∷ Toff023 ∷ [])
  b0 = at 0 0 (Toff023 ∷ Toff023 ∷ []) (sym (wl0203 (lit c4))) ▸
       at 1 4 (Toff014 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ []) (sym (lem-VPQ-at2442 c4)) ▸
       at 4 2 [] (wl0204 (lit c4)) ▸ done


-- box-cP @2442: 12 steps
lem-box-cP-at2442 : Ws → ⟪ (Bx0-1432 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) ⟫ʷ
lem-box-cP-at2442 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-1432 ∷ []) (CCZ014 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ CCZ013 ∷ Toff103 ∷ CZ12 ∷ Toff103 ∷ CCZ013 ∷ CZ12 ∷ [])
  b0 = at 0 1 (CCZ014 ∷ Toff014 ∷ Bx1-032 ∷ Toff014 ∷ CCZ014 ∷ Bx1-032 ∷ []) (refl) ▸
       at 2 1 (CCZ013 ∷ Toff103 ∷ Bx0-12 ∷ Toff103 ∷ CCZ013 ∷ Bx0-12 ∷ []) (refl) ▸
       at 4 1 (CZ12 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 2 6 (CCZ023 ∷ []) (wl0344 (lit c4)) ▸
       at 5 1 (CCZ013 ∷ Toff103 ∷ Bx0-12 ∷ Toff103 ∷ CCZ013 ∷ Bx0-12 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 10 1 (CZ12 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ014 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ CCZ013 ∷ Toff103 ∷ CZ12 ∷ Toff103 ∷ CCZ013 ∷ CZ12 ∷ []) (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ [])
  b1 = at 5 6 (CCZ023 ∷ []) (wl0344 (lit c4)) ▸
       at 2 4 (Toff023 ∷ Toff014 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-QVQ-at2442 c4) ▸
       at 1 2 (Toff023 ∷ Toff014 ∷ []) (lem-tP-at2442 c4) ▸
       at 2 2 [] (wp0051 c4) ▸ done


-- Xb-box @2442: 18 steps
lem-Xb-box-at2442 : Ws → ⟪ (X4 ∷ Bx0-1432 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1432 ∷ CCZ123 ∷ []) ⟫ʷ
lem-Xb-box-at2442 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ Bx0-1432 ∷ X4 ∷ []) (CCZ014 ∷ Toff023 ∷ X4 ∷ CZ01 ∷ CS23 ∷ CX13 ∷ CCZ014 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ Toff023 ∷ X4 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at2442 c4) ▸
       at 0 2 (CCZ014 ∷ X4 ∷ CZ01 ∷ []) (sym (wp0052 c4)) ▸
       at 2 2 (Toff023 ∷ CZ01 ∷ CCZ123 ∷ []) (wl0206 (lit c4)) ▸
       at 1 2 (Toff023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) (X))) ▸
       at 4 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0242 (lit c4)) ▸
       at 8 2 (CCZ014 ∷ CS12 ∷ []) (sym (wp0067 c4)) ▸
       at 7 2 (CCZ014 ∷ CX13 ∷ []) (sym (wp0795 c4)) ▸
       at 6 2 (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 (lit c4)) ▸ done

  b1 : Chain (CCZ014 ∷ Toff023 ∷ X4 ∷ CZ01 ∷ CS23 ∷ CX13 ∷ CCZ014 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ Toff023 ∷ X4 ∷ []) (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ X4 ∷ CCZ123 ∷ X4 ∷ [])
  b1 = at 5 2 (CCZ014 ∷ CX13 ∷ []) (sym (wp0795 c4)) ▸
       at 4 2 (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 (lit c4)) ▸
       at 5 5 (CCZ123 ∷ []) (sym (wl0242 (lit c4))) ▸
       at 3 2 (CCZ014 ∷ CZ01 ∷ []) (sym (wp0055 c4)) ▸
       at 2 2 (CCZ014 ∷ X4 ∷ CZ01 ∷ []) (sym (wp0052 c4)) ▸
       at 3 3 (X4 ∷ []) (wl0208 (lit c4)) ▸
       at 4 2 (Toff023 ∷ CCZ123 ∷ []) (wl0209 (lit c4)) ▸
       at 3 2 (Toff023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) (X))) ▸ done

  b2 : Chain (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (Bx0-1432 ∷ CCZ123 ∷ [])
  b2 = at 0 4 (Bx0-1432 ∷ []) (sym (lem-box-cP-at2442 c4)) ▸
       at 1 3 (CCZ123 ∷ []) (sym (wl0210 (lit c4))) ▸ done


-- CXbc-box @2442: 17 steps
lem-CXbc-box-at2442 : Ws → ⟪ (CX43 ∷ Bx0-1432 ∷ CX43 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1432 ∷ CCZ124 ∷ []) ⟫ʷ
lem-CXbc-box-at2442 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX43 ∷ Bx0-1432 ∷ CX43 ∷ []) (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CX43 ∷ CCZ024 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CCZ023 ∷ CX14 ∷ CS12 ∷ CX43 ∷ [])
  b0 = at 1 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-box-tQ-at2442 c4) ▸
       at 0 2 (Toff014 ∷ CX43 ∷ []) (wp0960 c4) ▸
       at 1 2 (CCZ023 ∷ CX43 ∷ CCZ024 ∷ []) (sym (wp0920 c4)) ▸
       at 3 2 (Toff014 ∷ CCZ024 ∷ CCZ124 ∷ []) (wp0815 c4) ▸
       at 2 2 (Toff014 ∷ CX43 ∷ []) (wp0960 c4) ▸
       at 5 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 9 2 (CCZ023 ∷ CS12 ∷ []) (sym (wl0621 (lit c4))) ▸
       at 8 2 (CCZ023 ∷ CX14 ∷ []) (lem-comm-CX14-CCZ023 (lit c4)) ▸ done

  b1 : Chain (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CX43 ∷ CCZ024 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CCZ023 ∷ CX14 ∷ CS12 ∷ CX43 ∷ []) (Bx0-1432 ∷ CX43 ∷ CCZ124 ∷ CX43 ∷ [])
  b1 = at 7 2 (CCZ023 ∷ CS24⁻ ∷ []) (sym (wp0820 c4)) ▸
       at 6 2 (CCZ023 ∷ CX14 ∷ []) (lem-comm-CX14-CCZ023 (lit c4)) ▸
       at 5 2 (CCZ023 ∷ CS24 ∷ []) (sym (wp0513 c4)) ▸
       at 6 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 4 2 (CCZ023 ∷ CCZ024 ∷ []) (sym (wp0669 c4)) ▸
       at 3 2 (CCZ023 ∷ CX43 ∷ CCZ024 ∷ []) (sym (wp0920 c4)) ▸
       at 4 3 (CX43 ∷ []) (wp0922 c4) ▸
       at 0 4 (Bx0-1432 ∷ []) (sym (lem-box-tQ-at2442 c4)) ▸ done

  b2 : Chain (Bx0-1432 ∷ CX43 ∷ CCZ124 ∷ CX43 ∷ []) (Bx0-1432 ∷ CCZ124 ∷ [])
  b2 = at 1 3 (CCZ124 ∷ []) (sym (wl0646 (lit c4))) ▸ done


-- CXcb-box @2442: 18 steps
lem-CXcb-box-at2442 : Ws → ⟪ (CX34 ∷ Bx0-1432 ∷ CX34 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1432 ∷ CCZ123 ∷ []) ⟫ʷ
lem-CXcb-box-at2442 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX34 ∷ Bx0-1432 ∷ CX34 ∷ []) (Toff014 ∷ CCZ023 ∷ CX34 ∷ Toff013 ∷ CS23 ∷ CX13 ∷ Toff014 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ CCZ023 ∷ CX34 ∷ [])
  b0 = at 1 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-box-tQ-at2442 c4) ▸
       at 0 2 (Toff014 ∷ CX34 ∷ Toff013 ∷ []) (wp0961 c4) ▸
       at 2 2 (CCZ023 ∷ Toff013 ∷ CCZ123 ∷ []) (sym (wl1165 (lit c4))) ▸
       at 1 2 (CCZ023 ∷ CX34 ∷ []) (sym (wp0680 c4)) ▸
       at 4 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0242 (lit c4)) ▸
       at 8 2 (Toff014 ∷ CS12 ∷ []) (wp0962 c4) ▸
       at 7 2 (Toff014 ∷ CX13 ∷ []) (wp0963 c4) ▸
       at 6 2 (Toff014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-TOFF014 (lit c4)) ▸ done

  b1 : Chain (Toff014 ∷ CCZ023 ∷ CX34 ∷ Toff013 ∷ CS23 ∷ CX13 ∷ Toff014 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ CCZ023 ∷ CX34 ∷ []) (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ CX34 ∷ CCZ123 ∷ CX34 ∷ [])
  b1 = at 5 2 (Toff014 ∷ CX13 ∷ []) (wp0963 c4) ▸
       at 4 2 (Toff014 ∷ CS23 ∷ []) (lem-comm-CS23-TOFF014 (lit c4)) ▸
       at 5 5 (CCZ123 ∷ []) (sym (wl0242 (lit c4))) ▸
       at 3 2 (Toff014 ∷ Toff013 ∷ []) (wp0786 c4) ▸
       at 2 2 (Toff014 ∷ CX34 ∷ Toff013 ∷ []) (wp0961 c4) ▸
       at 3 3 (CX34 ∷ []) (wp0964 c4) ▸
       at 4 2 (CCZ023 ∷ CCZ123 ∷ []) (sym (wl0613 (lit c4))) ▸
       at 3 2 (CCZ023 ∷ CX34 ∷ []) (sym (wp0680 c4)) ▸ done

  b2 : Chain (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ CX34 ∷ CCZ123 ∷ CX34 ∷ []) (Bx0-1432 ∷ CCZ123 ∷ [])
  b2 = at 0 4 (Bx0-1432 ∷ []) (sym (lem-box-tQ-at2442 c4)) ▸
       at 1 3 (CCZ123 ∷ []) (sym (wl0648 (lit c4))) ▸ done


-- SWbc-box @2442: 11 steps
lem-SWbc-box-at2442 : Ws → ⟪ (Sw34 ∷ Bx0-1432 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1432 ∷ []) ⟫ʷ
lem-SWbc-box-at2442 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw34 ∷ Bx0-1432 ∷ Sw34 ∷ []) (CX43 ∷ Bx0-1432 ∷ CX43 ∷ CCZ124 ∷ CCZ123 ∷ CCZ124 ∷ CCZ123 ∷ CCZ124 ∷ [])
  b0 = at 0 1 (CX43 ∷ CX34 ∷ CX43 ∷ []) (sym (wl0649 (lit c4))) ▸
       at 4 1 (CX43 ∷ CX34 ∷ CX43 ∷ []) (sym (wl0649 (lit c4))) ▸
       at 2 3 (Bx0-1432 ∷ CCZ124 ∷ []) (lem-CXbc-box-at2442 c4) ▸
       at 3 2 (CX34 ∷ CCZ123 ∷ CCZ124 ∷ []) (wl0650 (lit c4)) ▸
       at 1 3 (Bx0-1432 ∷ CCZ123 ∷ []) (lem-CXcb-box-at2442 c4) ▸
       at 4 2 (CX43 ∷ CCZ124 ∷ []) (wl0651 (lit c4)) ▸
       at 3 2 (CX43 ∷ CCZ124 ∷ CCZ123 ∷ []) (wl0652 (lit c4)) ▸
       at 2 2 (CX43 ∷ CCZ124 ∷ CCZ123 ∷ []) (wl0652 (lit c4)) ▸ done

  b1 : Chain (CX43 ∷ Bx0-1432 ∷ CX43 ∷ CCZ124 ∷ CCZ123 ∷ CCZ124 ∷ CCZ123 ∷ CCZ124 ∷ []) (Bx0-1432 ∷ [])
  b1 = at 3 5 (CCZ124 ∷ []) (wl0653 (lit c4)) ▸
       at 0 3 (Bx0-1432 ∷ CCZ124 ∷ []) (lem-CXbc-box-at2442 c4) ▸
       at 1 2 [] (wl0263 (lit c4)) ▸ done


-- nat-SWbc @2442: 23 steps
lem-nat-SWbc-at2442 : Ws → ⟪ (Sw34 ∷ Bx0-1432 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1342 ∷ []) ⟫ʷ
lem-nat-SWbc-at2442 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw34 ∷ Bx0-1432 ∷ Sw34 ∷ []) (CCZ013 ∷ Toff013 ∷ CCZ014 ∷ Toff104 ∷ Bx0-12 ∷ Toff104 ∷ Sw34 ∷ CCZ013 ∷ Bx0-12 ∷ Toff014 ∷ CCZ014 ∷ Bx1-032 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff014 ∷ Bx1-032 ∷ Toff014 ∷ CCZ014 ∷ Bx1-032 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw34 ∷ []) (sym (wp0958 c4)) ▸
       at 1 2 (Toff013 ∷ Sw34 ∷ []) (wp0965 c4) ▸
       at 3 1 (CCZ013 ∷ Toff103 ∷ Bx0-12 ∷ Toff103 ∷ CCZ013 ∷ Bx0-12 ∷ []) (refl) ▸
       at 2 2 (CCZ014 ∷ Sw34 ∷ []) (sym (wp0398 c4)) ▸
       at 3 2 (Toff104 ∷ Sw34 ∷ []) (wp0966 c4) ▸
       at 4 2 (Bx0-12 ∷ Sw34 ∷ []) (sym (c₃ (CZ ↑) (Swap))) ▸
       at 5 2 (Toff104 ∷ Sw34 ∷ []) (wp0966 c4) ▸ done

  b1 : Chain (CCZ013 ∷ Toff013 ∷ CCZ014 ∷ Toff104 ∷ Bx0-12 ∷ Toff104 ∷ Sw34 ∷ CCZ013 ∷ Bx0-12 ∷ Toff014 ∷ CCZ014 ∷ Bx1-032 ∷ Sw34 ∷ []) (CCZ013 ∷ Toff013 ∷ CCZ014 ∷ Toff104 ∷ Bx0-12 ∷ Toff104 ∷ CCZ014 ∷ Bx0-12 ∷ Toff013 ∷ CCZ013 ∷ CCZ014 ∷ Toff104 ∷ Bx0-12 ∷ Sw34 ∷ Toff103 ∷ CCZ013 ∷ Bx0-12 ∷ Sw34 ∷ [])
  b1 = at 6 2 (CCZ014 ∷ Sw34 ∷ []) (sym (wp0398 c4)) ▸
       at 7 2 (Bx0-12 ∷ Sw34 ∷ []) (sym (c₃ (CZ ↑) (Swap))) ▸
       at 8 2 (Toff013 ∷ Sw34 ∷ []) (wp0965 c4) ▸
       at 9 2 (CCZ013 ∷ Sw34 ∷ []) (sym (wp0958 c4)) ▸
       at 11 1 (CCZ013 ∷ Toff103 ∷ Bx0-12 ∷ Toff103 ∷ CCZ013 ∷ Bx0-12 ∷ []) (refl) ▸
       at 10 2 (CCZ014 ∷ Sw34 ∷ []) (sym (wp0398 c4)) ▸
       at 11 2 (Toff104 ∷ Sw34 ∷ []) (wp0966 c4) ▸
       at 12 2 (Bx0-12 ∷ Sw34 ∷ []) (sym (c₃ (CZ ↑) (Swap))) ▸ done

  b2 : Chain (CCZ013 ∷ Toff013 ∷ CCZ014 ∷ Toff104 ∷ Bx0-12 ∷ Toff104 ∷ CCZ014 ∷ Bx0-12 ∷ Toff013 ∷ CCZ013 ∷ CCZ014 ∷ Toff104 ∷ Bx0-12 ∷ Sw34 ∷ Toff103 ∷ CCZ013 ∷ Bx0-12 ∷ Sw34 ∷ []) (Bx0-1342 ∷ [])
  b2 = at 13 2 (Toff104 ∷ Sw34 ∷ []) (wp0966 c4) ▸
       at 14 2 (CCZ014 ∷ Sw34 ∷ []) (sym (wp0398 c4)) ▸
       at 15 2 (Bx0-12 ∷ Sw34 ∷ []) (sym (c₃ (CZ ↑) (Swap))) ▸
       at 16 2 [] (wl0004 (lit c4)) ▸
       at 2 6 (Bx1-042 ∷ []) (refl) ▸
       at 5 6 (Bx1-042 ∷ []) (refl) ▸
       at 0 6 (Bx0-1342 ∷ []) (refl) ▸ done


-- sym-bc @2442: 2 steps
lem-sym-bc-at2442 : Ws → ⟪ (Bx0-1432 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1342 ∷ []) ⟫ʷ
lem-sym-bc-at2442 c4 = run b0
  where
  b0 : Chain (Bx0-1432 ∷ []) (Bx0-1342 ∷ [])
  b0 = at 0 1 (Sw34 ∷ Bx0-1432 ∷ Sw34 ∷ []) (sym (lem-SWbc-box-at2442 c4)) ▸
       at 0 3 (Bx0-1342 ∷ []) (lem-nat-SWbc-at2442 c4) ▸ done


-- box-perm-1324 @2442: 1 steps
lem-box-perm-1324-at2442 : Ws → ⟪ (Bx0-1432 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1342 ∷ []) ⟫ʷ
lem-box-perm-1324-at2442 c4 = run b0
  where
  b0 : Chain (Bx0-1432 ∷ []) (Bx0-1342 ∷ [])
  b0 = at 0 1 (Bx0-1342 ∷ []) (lem-sym-bc-at2442 c4) ▸ done


-- CKc-box @233442: 61 steps
lem-CKc-box-at233442 : Ws → ⟪ (Bx0-1342 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CK42 ∷ CCZ123 ∷ Bx0-1342 ∷ []) ⟫ʷ
lem-CKc-box-at233442 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (run b7)))))))
  where
  b0 : Chain (Bx0-1342 ∷ CK42 ∷ []) (X4 ∷ Bx0-1342 ∷ CCZ123 ∷ K2 ∷ CK42 ∷ S4 ∷ CCZ123 ∷ X4 ∷ CCZ123 ∷ [])
  b0 = at 1 0 (CCZ123 ∷ CCZ123 ∷ []) (sym (wl0181 (lit c4))) ▸
       at 0 1 (Bx0-1432 ∷ []) (lem-box-perm-1324-at233442 c4) ▸
       at 0 2 (X4 ∷ Bx0-1432 ∷ X4 ∷ []) (sym (lem-Xb-box-at2442 c4)) ▸
       at 3 2 (CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ123 ∷ []) (sym (wl1144 (lit c4))) ▸
       at 2 2 (CCZ123 ∷ X4 ∷ []) (sym (c₄ (CCZ ↑) (X))) ▸
       at 3 2 (K2 ∷ CK42 ∷ S4 ∷ X4 ∷ []) (sym (wl0725 (lit c4))) ▸
       at 6 2 (CCZ123 ∷ X4 ∷ []) (sym (c₄ (CCZ ↑) (X))) ▸
       at 1 1 (Bx0-1342 ∷ []) (lem-box-perm-1324-at2442 c4) ▸ done

  b1 : Chain (X4 ∷ Bx0-1342 ∷ CCZ123 ∷ K2 ∷ CK42 ∷ S4 ∷ CCZ123 ∷ X4 ∷ CCZ123 ∷ []) (X4 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ123 ∷ CCZ024 ∷ K2 ∷ CK42 ∷ S4 ∷ CCZ123 ∷ X4 ∷ CCZ123 ∷ [])
  b1 = at 1 1 (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) (lem-box-tQ-at233442 c4) ▸
       at 5 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0242 (lit c4)) ▸
       at 4 2 (CS23 ∷ CCZ024 ∷ []) (wp0092 c4) ▸
       at 5 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 6 2 (CS23⁻ ∷ CCZ024 ∷ []) (wp0091 c4) ▸
       at 7 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 8 2 (CS12 ∷ CCZ024 ∷ []) (wp0081 c4) ▸
       at 4 5 (CCZ123 ∷ []) (sym (wl0242 (lit c4))) ▸ done

  b2 : Chain (X4 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ123 ∷ CCZ024 ∷ K2 ∷ CK42 ∷ S4 ∷ CCZ123 ∷ X4 ∷ CCZ123 ∷ []) (X4 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ123 ∷ K2 ∷ Toff204 ∷ CCZ024 ∷ CZ02 ∷ CK42 ∷ CZ02 ∷ S4 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CCZ024 ∷ CS12 ∷ X4 ∷ CCZ123 ∷ [])
  b2 = at 5 2 (K2 ∷ Toff204 ∷ CCZ024 ∷ CCZ024 ∷ []) (wp0936 c4) ▸
       at 8 2 (CZ02 ∷ CK42 ∷ CZ02 ∷ CCZ024 ∷ []) (wp0937 c4) ▸
       at 11 2 (S4 ∷ CCZ024 ∷ []) (wp0617 c4) ▸
       at 13 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0242 (lit c4)) ▸
       at 12 2 (CS23 ∷ CCZ024 ∷ []) (wp0092 c4) ▸
       at 13 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 14 2 (CS23⁻ ∷ CCZ024 ∷ []) (wp0091 c4) ▸
       at 15 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸ done

  b3 : Chain (X4 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ123 ∷ K2 ∷ Toff204 ∷ CCZ024 ∷ CZ02 ∷ CK42 ∷ CZ02 ∷ S4 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CCZ024 ∷ CS12 ∷ X4 ∷ CCZ123 ∷ []) (X4 ∷ Toff013 ∷ CCZ024 ∷ CCZ123 ∷ K2 ∷ CK42 ∷ S4 ∷ CCZ123 ∷ Toff013 ∷ CCZ024 ∷ X4 ∷ CCZ123 ∷ [])
  b3 = at 16 2 (CS12 ∷ CCZ024 ∷ []) (wp0081 c4) ▸
       at 12 5 (CCZ123 ∷ []) (sym (wl0242 (lit c4))) ▸
       at 5 7 (K2 ∷ CK42 ∷ S4 ∷ []) (sym (wp0938 c4)) ▸
       at 3 2 (CCZ123 ∷ Toff013 ∷ []) (sym (wl0234 (lit c4))) ▸
       at 4 2 (K2 ∷ Toff013 ∷ []) (sym (wl0743 (lit c4))) ▸
       at 5 2 (CK42 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CK42 (lit c4)) ▸
       at 6 2 (S4 ∷ Toff013 ∷ []) (c₄ (Swap ↑ ↑ • Toff • Swap ↑ ↑) (S)) ▸
       at 7 2 (CCZ123 ∷ Toff013 ∷ []) (sym (wl0234 (lit c4))) ▸ done

  b4 : Chain (X4 ∷ Toff013 ∷ CCZ024 ∷ CCZ123 ∷ K2 ∷ CK42 ∷ S4 ∷ CCZ123 ∷ Toff013 ∷ CCZ024 ∷ X4 ∷ CCZ123 ∷ []) (X4 ∷ Toff013 ∷ CCZ123 ∷ K2 ∷ Toff204 ∷ CCZ024 ∷ CCZ024 ∷ CK42 ∷ S4 ∷ CCZ123 ∷ Toff013 ∷ CCZ024 ∷ X4 ∷ CCZ123 ∷ [])
  b4 = at 3 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0242 (lit c4)) ▸
       at 2 2 (CS23 ∷ CCZ024 ∷ []) (wp0092 c4) ▸
       at 3 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 4 2 (CS23⁻ ∷ CCZ024 ∷ []) (wp0091 c4) ▸
       at 5 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 6 2 (CS12 ∷ CCZ024 ∷ []) (wp0081 c4) ▸
       at 2 5 (CCZ123 ∷ []) (sym (wl0242 (lit c4))) ▸
       at 3 2 (K2 ∷ Toff204 ∷ CCZ024 ∷ CCZ024 ∷ []) (wp0936 c4) ▸ done

  b5 : Chain (X4 ∷ Toff013 ∷ CCZ123 ∷ K2 ∷ Toff204 ∷ CCZ024 ∷ CCZ024 ∷ CK42 ∷ S4 ∷ CCZ123 ∷ Toff013 ∷ CCZ024 ∷ X4 ∷ CCZ123 ∷ []) (X4 ∷ Toff013 ∷ CCZ123 ∷ K2 ∷ Toff204 ∷ CCZ024 ∷ CZ02 ∷ CK42 ∷ CZ02 ∷ S4 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ X4 ∷ CCZ123 ∷ [])
  b5 = at 6 2 (CZ02 ∷ CK42 ∷ CZ02 ∷ CCZ024 ∷ []) (wp0937 c4) ▸
       at 9 2 (S4 ∷ CCZ024 ∷ []) (wp0617 c4) ▸
       at 11 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0242 (lit c4)) ▸
       at 10 2 (CS23 ∷ CCZ024 ∷ []) (wp0092 c4) ▸
       at 11 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 12 2 (CS23⁻ ∷ CCZ024 ∷ []) (wp0091 c4) ▸
       at 13 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 14 2 (CS12 ∷ CCZ024 ∷ []) (wp0081 c4) ▸ done

  b6 : Chain (X4 ∷ Toff013 ∷ CCZ123 ∷ K2 ∷ Toff204 ∷ CCZ024 ∷ CZ02 ∷ CK42 ∷ CZ02 ∷ S4 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ X4 ∷ CCZ123 ∷ []) (X4 ∷ CCZ123 ∷ K2 ∷ CK42 ∷ S4 ∷ CCZ123 ∷ Bx0-1342 ∷ X4 ∷ CCZ123 ∷ [])
  b6 = at 10 5 (CCZ123 ∷ []) (sym (wl0242 (lit c4))) ▸
       at 3 7 (K2 ∷ CK42 ∷ S4 ∷ []) (sym (wp0938 c4)) ▸
       at 1 2 (CCZ123 ∷ Toff013 ∷ []) (sym (wl0234 (lit c4))) ▸
       at 2 2 (K2 ∷ Toff013 ∷ []) (sym (wl0743 (lit c4))) ▸
       at 3 2 (CK42 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CK42 (lit c4)) ▸
       at 4 2 (S4 ∷ Toff013 ∷ []) (c₄ (Swap ↑ ↑ • Toff • Swap ↑ ↑) (S)) ▸
       at 5 2 (CCZ123 ∷ Toff013 ∷ []) (sym (wl0234 (lit c4))) ▸
       at 6 4 (Bx0-1342 ∷ []) (sym (lem-box-tQ-at233442 c4)) ▸ done

  b7 : Chain (X4 ∷ CCZ123 ∷ K2 ∷ CK42 ∷ S4 ∷ CCZ123 ∷ Bx0-1342 ∷ X4 ∷ CCZ123 ∷ []) (CCZ123 ∷ CK42 ∷ CCZ123 ∷ Bx0-1342 ∷ [])
  b7 = at 6 1 (Bx0-1432 ∷ []) (sym (lem-box-perm-1324-at2442 c4)) ▸
       at 0 6 (CCZ123 ∷ CK42 ∷ CCZ123 ∷ X4 ∷ []) (sym (wl1145 (lit c4))) ▸
       at 3 3 (Bx0-1432 ∷ CCZ123 ∷ []) (lem-Xb-box-at2442 c4) ▸
       at 4 2 [] (wl0181 (lit c4)) ▸
       at 3 1 (Bx0-1342 ∷ []) (lem-box-perm-1324-at2442 c4) ▸ done


-- P-box @233442: 8 steps
lem-P-box-at233442 : Ws → ⟪ (Toff024 ∷ Bx0-1342 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1342 ∷ []) ⟫ʷ
lem-P-box-at233442 c4 = run b0
  where
  b0 : Chain (Toff024 ∷ Bx0-1342 ∷ Toff024 ∷ []) (Bx0-1342 ∷ [])
  b0 = at 1 1 (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) (lem-box-tQ-at233442 c4) ▸
       at 0 2 (Toff013 ∷ Toff024 ∷ []) (sym (lem-tP-at233442 c4)) ▸
       at 1 2 (CCZ024 ∷ CZ24 ∷ Toff024 ∷ []) (sym (wp0132 c4)) ▸
       at 3 2 (Toff013 ∷ Toff024 ∷ []) (sym (lem-tP-at233442 c4)) ▸
       at 4 3 (CCZ024 ∷ CZ24 ∷ []) (sym (wp0133 c4)) ▸
       at 2 2 (Toff013 ∷ CZ24 ∷ []) (lem-comm-CZ24-TOFF013 (lit c4)) ▸
       at 3 3 (CCZ024 ∷ []) (sym (wp0134 c4)) ▸
       at 0 4 (Bx0-1342 ∷ []) (sym (lem-box-tQ-at233442 c4)) ▸ done


-- pairs @233442: 4 steps
lem-pairs-at233442 : Ws → ⟪ (Bx0-1342 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4213 ∷ []) ⟫ʷ
lem-pairs-at233442 c4 = run b0
  where
  b0 : Chain (Bx0-1342 ∷ []) (Bx0-4213 ∷ [])
  b0 = at 0 1 (Toff024 ∷ Bx0-1342 ∷ Toff024 ∷ []) (sym (lem-P-box-at233442 c4)) ▸
       at 1 1 (CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ []) (lem-box-cP-at233442 c4) ▸
       at 4 2 [] (wp0080 c4) ▸
       at 0 4 (Bx0-4213 ∷ []) (sym (lem-box-tQ-at143143 c4)) ▸ done


-- CXbc-box @143143: 17 steps
lem-CXbc-box-at143143 : Ws → ⟪ (CX21 ∷ Bx0-4213 ∷ CX21 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4213 ∷ CCZ234 ∷ []) ⟫ʷ
lem-CXbc-box-at143143 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX21 ∷ Bx0-4213 ∷ CX21 ∷ []) (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CX21 ∷ CCZ023 ∷ CS23 ∷ CX42 ∷ CS23⁻ ∷ CCZ013 ∷ CX42 ∷ CS34 ∷ CX21 ∷ [])
  b0 = at 1 1 (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-box-tQ-at143143 c4) ▸
       at 0 2 (Toff024 ∷ CX21 ∷ []) (wp0191 c4) ▸
       at 1 2 (CCZ013 ∷ CX21 ∷ CCZ023 ∷ []) (sym (wl1166 (lit c4))) ▸
       at 3 2 (Toff024 ∷ CCZ023 ∷ CCZ234 ∷ []) (wp0967 c4) ▸
       at 2 2 (Toff024 ∷ CX21 ∷ []) (wp0191 c4) ▸
       at 5 1 (CS23 ∷ CX42 ∷ CS23⁻ ∷ CX42 ∷ CS34 ∷ []) (wl0675 (lit c4)) ▸
       at 9 2 (CCZ013 ∷ CS34 ∷ []) (sym (wp0185 c4)) ▸
       at 8 2 (CCZ013 ∷ CX42 ∷ []) (lem-comm-CX42-CCZ013 (lit c4)) ▸ done

  b1 : Chain (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CX21 ∷ CCZ023 ∷ CS23 ∷ CX42 ∷ CS23⁻ ∷ CCZ013 ∷ CX42 ∷ CS34 ∷ CX21 ∷ []) (Bx0-4213 ∷ CX21 ∷ CCZ234 ∷ CX21 ∷ [])
  b1 = at 7 2 (CCZ013 ∷ CS23⁻ ∷ []) (sym (wl1167 (lit c4))) ▸
       at 6 2 (CCZ013 ∷ CX42 ∷ []) (lem-comm-CX42-CCZ013 (lit c4)) ▸
       at 5 2 (CCZ013 ∷ CS23 ∷ []) (sym (wl0324 (lit c4))) ▸
       at 6 5 (CCZ234 ∷ []) (sym (wl0675 (lit c4))) ▸
       at 4 2 (CCZ013 ∷ CCZ023 ∷ []) (sym (wl0671 (lit c4))) ▸
       at 3 2 (CCZ013 ∷ CX21 ∷ CCZ023 ∷ []) (sym (wl1166 (lit c4))) ▸
       at 4 3 (CX21 ∷ []) (wl1168 (lit c4)) ▸
       at 0 4 (Bx0-4213 ∷ []) (sym (lem-box-tQ-at143143 c4)) ▸ done

  b2 : Chain (Bx0-4213 ∷ CX21 ∷ CCZ234 ∷ CX21 ∷ []) (Bx0-4213 ∷ CCZ234 ∷ [])
  b2 = at 1 3 (CCZ234 ∷ []) (sym (wl0676 (lit c4))) ▸ done


-- CXcb-box @143143: 18 steps
lem-CXcb-box-at143143 : Ws → ⟪ (CX12 ∷ Bx0-4213 ∷ CX12 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4213 ∷ CCZ134 ∷ []) ⟫ʷ
lem-CXcb-box-at143143 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX12 ∷ Bx0-4213 ∷ CX12 ∷ []) (Toff024 ∷ CCZ013 ∷ CX12 ∷ Toff014 ∷ CS13 ∷ CX41 ∷ Toff024 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ CCZ013 ∷ CX12 ∷ [])
  b0 = at 1 1 (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-box-tQ-at143143 c4) ▸
       at 0 2 (Toff024 ∷ CX12 ∷ Toff014 ∷ []) (wp0968 c4) ▸
       at 2 2 (CCZ013 ∷ Toff014 ∷ CCZ134 ∷ []) (sym (wp0969 c4)) ▸
       at 1 2 (CCZ013 ∷ CX12 ∷ []) (sym (wl0448 (lit c4))) ▸
       at 4 1 (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ []) (wl0617 (lit c4)) ▸
       at 8 2 (Toff024 ∷ CS34 ∷ []) (wp0970 c4) ▸
       at 7 2 (Toff024 ∷ CX41 ∷ []) (wp0181 c4) ▸
       at 6 2 (Toff024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-TOFF024 (lit c4)) ▸ done

  b1 : Chain (Toff024 ∷ CCZ013 ∷ CX12 ∷ Toff014 ∷ CS13 ∷ CX41 ∷ Toff024 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ CCZ013 ∷ CX12 ∷ []) (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ CX12 ∷ CCZ134 ∷ CX12 ∷ [])
  b1 = at 5 2 (Toff024 ∷ CX41 ∷ []) (wp0181 c4) ▸
       at 4 2 (Toff024 ∷ CS13 ∷ []) (lem-comm-CS13-TOFF024 (lit c4)) ▸
       at 5 5 (CCZ134 ∷ []) (sym (wl0617 (lit c4))) ▸
       at 3 2 (Toff024 ∷ Toff014 ∷ []) (wp0548 c4) ▸
       at 2 2 (Toff024 ∷ CX12 ∷ Toff014 ∷ []) (wp0968 c4) ▸
       at 3 3 (CX12 ∷ []) (wp0971 c4) ▸
       at 4 2 (CCZ013 ∷ CCZ134 ∷ []) (sym (wp0593 c4)) ▸
       at 3 2 (CCZ013 ∷ CX12 ∷ []) (sym (wl0448 (lit c4))) ▸ done

  b2 : Chain (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ CX12 ∷ CCZ134 ∷ CX12 ∷ []) (Bx0-4213 ∷ CCZ134 ∷ [])
  b2 = at 0 4 (Bx0-4213 ∷ []) (sym (lem-box-tQ-at143143 c4)) ▸
       at 1 3 (CCZ134 ∷ []) (sym (wl0673 (lit c4))) ▸ done


-- SWbc-box @143143: 11 steps
lem-SWbc-box-at143143 : Ws → ⟪ (Sw12 ∷ Bx0-4213 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4213 ∷ []) ⟫ʷ
lem-SWbc-box-at143143 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw12 ∷ Bx0-4213 ∷ Sw12 ∷ []) (CX21 ∷ Bx0-4213 ∷ CX21 ∷ CCZ234 ∷ CCZ134 ∷ CCZ234 ∷ CCZ134 ∷ CCZ234 ∷ [])
  b0 = at 0 1 (CX21 ∷ CX12 ∷ CX21 ∷ []) (sym (wl0835 (lit c4))) ▸
       at 4 1 (CX21 ∷ CX12 ∷ CX21 ∷ []) (sym (wl0835 (lit c4))) ▸
       at 2 3 (Bx0-4213 ∷ CCZ234 ∷ []) (lem-CXbc-box-at143143 c4) ▸
       at 3 2 (CX12 ∷ CCZ134 ∷ CCZ234 ∷ []) (wl0680 (lit c4)) ▸
       at 1 3 (Bx0-4213 ∷ CCZ134 ∷ []) (lem-CXcb-box-at143143 c4) ▸
       at 4 2 (CX21 ∷ CCZ234 ∷ []) (wl0836 (lit c4)) ▸
       at 3 2 (CX21 ∷ CCZ234 ∷ CCZ134 ∷ []) (wl0678 (lit c4)) ▸
       at 2 2 (CX21 ∷ CCZ234 ∷ CCZ134 ∷ []) (wl0678 (lit c4)) ▸ done

  b1 : Chain (CX21 ∷ Bx0-4213 ∷ CX21 ∷ CCZ234 ∷ CCZ134 ∷ CCZ234 ∷ CCZ134 ∷ CCZ234 ∷ []) (Bx0-4213 ∷ [])
  b1 = at 3 5 (CCZ234 ∷ []) (wl0837 (lit c4)) ▸
       at 0 3 (Bx0-4213 ∷ CCZ234 ∷ []) (lem-CXbc-box-at143143 c4) ▸
       at 1 2 [] (wl0305 (lit c4)) ▸ done


-- nat-SWbc @143143: 23 steps
lem-nat-SWbc-at143143 : Ws → ⟪ (Sw12 ∷ Bx0-4213 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4123 ∷ []) ⟫ʷ
lem-nat-SWbc-at143143 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw12 ∷ Bx0-4213 ∷ Sw12 ∷ []) (CCZ014 ∷ Toff014 ∷ CCZ024 ∷ Toff402 ∷ Bx0-43 ∷ Toff402 ∷ Sw12 ∷ CCZ014 ∷ Bx0-43 ∷ Toff024 ∷ CCZ024 ∷ Bx4-013 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff024 ∷ Bx4-013 ∷ Toff024 ∷ CCZ024 ∷ Bx4-013 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw12 ∷ []) (sym (wp0553 c4)) ▸
       at 1 2 (Toff014 ∷ Sw12 ∷ []) (wp0972 c4) ▸
       at 3 1 (CCZ014 ∷ Toff401 ∷ Bx0-43 ∷ Toff401 ∷ CCZ014 ∷ Bx0-43 ∷ []) (refl) ▸
       at 2 2 (CCZ024 ∷ Sw12 ∷ []) (sym (wp0551 c4)) ▸
       at 3 2 (Toff402 ∷ Sw12 ∷ []) (wp0973 c4) ▸
       at 4 2 (Bx0-43 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CZ)) ▸
       at 5 2 (Toff402 ∷ Sw12 ∷ []) (wp0973 c4) ▸ done

  b1 : Chain (CCZ014 ∷ Toff014 ∷ CCZ024 ∷ Toff402 ∷ Bx0-43 ∷ Toff402 ∷ Sw12 ∷ CCZ014 ∷ Bx0-43 ∷ Toff024 ∷ CCZ024 ∷ Bx4-013 ∷ Sw12 ∷ []) (CCZ014 ∷ Toff014 ∷ CCZ024 ∷ Toff402 ∷ Bx0-43 ∷ Toff402 ∷ CCZ024 ∷ Bx0-43 ∷ Toff014 ∷ CCZ014 ∷ CCZ024 ∷ Toff402 ∷ Bx0-43 ∷ Sw12 ∷ Toff401 ∷ CCZ014 ∷ Bx0-43 ∷ Sw12 ∷ [])
  b1 = at 6 2 (CCZ024 ∷ Sw12 ∷ []) (sym (wp0551 c4)) ▸
       at 7 2 (Bx0-43 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CZ)) ▸
       at 8 2 (Toff014 ∷ Sw12 ∷ []) (wp0972 c4) ▸
       at 9 2 (CCZ014 ∷ Sw12 ∷ []) (sym (wp0553 c4)) ▸
       at 11 1 (CCZ014 ∷ Toff401 ∷ Bx0-43 ∷ Toff401 ∷ CCZ014 ∷ Bx0-43 ∷ []) (refl) ▸
       at 10 2 (CCZ024 ∷ Sw12 ∷ []) (sym (wp0551 c4)) ▸
       at 11 2 (Toff402 ∷ Sw12 ∷ []) (wp0973 c4) ▸
       at 12 2 (Bx0-43 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CZ)) ▸ done

  b2 : Chain (CCZ014 ∷ Toff014 ∷ CCZ024 ∷ Toff402 ∷ Bx0-43 ∷ Toff402 ∷ CCZ024 ∷ Bx0-43 ∷ Toff014 ∷ CCZ014 ∷ CCZ024 ∷ Toff402 ∷ Bx0-43 ∷ Sw12 ∷ Toff401 ∷ CCZ014 ∷ Bx0-43 ∷ Sw12 ∷ []) (Bx0-4123 ∷ [])
  b2 = at 13 2 (Toff402 ∷ Sw12 ∷ []) (wp0973 c4) ▸
       at 14 2 (CCZ024 ∷ Sw12 ∷ []) (sym (wp0551 c4)) ▸
       at 15 2 (Bx0-43 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CZ)) ▸
       at 16 2 [] (wl0006 (lit c4)) ▸
       at 2 6 (Bx4-023 ∷ []) (refl) ▸
       at 5 6 (Bx4-023 ∷ []) (refl) ▸
       at 0 6 (Bx0-4123 ∷ []) (refl) ▸ done


-- sym-bc @143143: 2 steps
lem-sym-bc-at143143 : Ws → ⟪ (Bx0-4213 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4123 ∷ []) ⟫ʷ
lem-sym-bc-at143143 c4 = run b0
  where
  b0 : Chain (Bx0-4213 ∷ []) (Bx0-4123 ∷ [])
  b0 = at 0 1 (Sw12 ∷ Bx0-4213 ∷ Sw12 ∷ []) (sym (lem-SWbc-box-at143143 c4)) ▸
       at 0 3 (Bx0-4123 ∷ []) (lem-nat-SWbc-at143143 c4) ▸ done


-- box-perm-1342 @233442: 3 steps
lem-box-perm-1342-at233442 : Ws → ⟪ (Bx0-1342 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ []) ⟫ʷ
lem-box-perm-1342-at233442 c4 = run b0
  where
  b0 : Chain (Bx0-1342 ∷ []) (Bx0-1423 ∷ [])
  b0 = at 0 1 (Bx0-4213 ∷ []) (lem-pairs-at233442 c4) ▸
       at 0 1 (Bx0-4123 ∷ []) (lem-sym-bc-at143143 c4) ▸
       at 0 1 (Bx0-1423 ∷ []) (lem-sym-ab-at14213243 c4) ▸ done


-- nf-X-CS1@1: 115 steps
lem-nf-X-CS1at1 : Ws → ⟪ (Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CS14 ∷ Bx0-1423 ∷ []) ⟫ʷ
lem-nf-X-CS1at1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (run b14))))))))))))))
  where
  b0 : Chain (Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS14 ∷ []) (CCZ124 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ124 ∷ CCZ014 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS14 ∷ [])
  b0 = at 0 2 (CCZ124 ∷ []) (lem-S2-SBOX⟨0·1·42·3⟩ c4) ▸
       at 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 3 1 (CS13 ∷ []) (refl) ▸
       at 5 1 (CS13⁻ ∷ []) (refl) ▸
       at 1 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 4 2 (Toff024 ∷ Toff324 ∷ Toff023 ∷ []) (wp0805 c4) ▸
       at 3 2 (Toff024 ∷ CCZ124 ∷ CCZ014 ∷ []) (wp0806 c4) ▸
       at 6 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸ done

  b1 : Chain (CCZ124 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ124 ∷ CCZ014 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS14 ∷ []) (CCZ124 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS14 ∷ [])
  b1 = at 5 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸
       at 6 2 (CS34 ∷ CCZ014 ∷ []) (wp0064 c4) ▸
       at 7 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 8 2 (CS34⁻ ∷ CCZ014 ∷ []) (wp0063 c4) ▸
       at 9 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 10 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸
       at 11 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸
       at 5 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸ done

  b2 : Chain (CCZ124 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS14 ∷ []) (CCZ124 ∷ CCZ014 ∷ Toff024 ∷ CCZ124 ∷ Toff023 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS14 ∷ [])
  b2 = at 2 2 (Toff024 ∷ Toff023 ∷ []) (wp0072 c4) ▸
       at 4 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 3 2 (CS24 ∷ Toff023 ∷ []) (sym (wp0070 c4)) ▸
       at 4 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 5 2 (CS24⁻ ∷ Toff023 ∷ []) (sym (wp0069 c4)) ▸
       at 6 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 7 2 (CS12 ∷ Toff023 ∷ []) (sym (wl0221 (lit c4))) ▸
       at 3 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸ done

  b3 : Chain (CCZ124 ∷ CCZ014 ∷ Toff024 ∷ CCZ124 ∷ Toff023 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS14 ∷ []) (CCZ124 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CCZ014 ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS14 ∷ [])
  b3 = at 4 2 (Toff024 ∷ Toff324 ∷ Toff023 ∷ []) (wp0805 c4) ▸
       at 2 3 (CCZ124 ∷ []) (sym (wp0074 c4)) ▸
       at 1 2 (CCZ124 ∷ CCZ014 ∷ []) (wp0066 c4) ▸
       at 3 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 2 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸
       at 3 2 (CS34 ∷ CCZ014 ∷ []) (wp0064 c4) ▸
       at 4 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 5 2 (CS34⁻ ∷ CCZ014 ∷ []) (wp0063 c4) ▸ done

  b4 : Chain (CCZ124 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CCZ014 ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS14 ∷ []) (CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13⁻ ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS14 ∷ [])
  b4 = at 6 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 7 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸
       at 8 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸
       at 2 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 3 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 3 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 6 2 (CS13 ∷ Toff023 ∷ []) (sym (wl0222 (lit c4))) ▸
       at 5 2 (CS13 ∷ CCZ014 ∷ []) (wp0053 c4) ▸ done

  b5 : Chain (CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13⁻ ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS14 ∷ []) (CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ124 ∷ K3 ∷ CCZ014 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CS13⁻ ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS14 ∷ [])
  b5 = at 4 2 (CS13 ∷ Toff023 ∷ []) (sym (wl0222 (lit c4))) ▸
       at 3 2 (CS13 ∷ CCZ014 ∷ []) (wp0053 c4) ▸
       at 4 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 4 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 7 2 (Toff024 ∷ Toff324 ∷ Toff023 ∷ []) (wp0805 c4) ▸
       at 6 2 (Toff024 ∷ CCZ124 ∷ CCZ014 ∷ []) (wp0806 c4) ▸
       at 9 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 8 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸ done

  b6 : Chain (CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ124 ∷ K3 ∷ CCZ014 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CS13⁻ ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS14 ∷ []) (CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff024 ∷ Toff023 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS14 ∷ [])
  b6 = at 9 2 (CS34 ∷ CCZ014 ∷ []) (wp0064 c4) ▸
       at 10 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 11 2 (CS34⁻ ∷ CCZ014 ∷ []) (wp0063 c4) ▸
       at 12 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 13 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸
       at 14 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸
       at 8 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 5 2 (Toff024 ∷ Toff023 ∷ []) (wp0072 c4) ▸ done

  b7 : Chain (CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff024 ∷ Toff023 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS14 ∷ []) (CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff024 ∷ CCZ124 ∷ Toff024 ∷ Toff324 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS14 ∷ [])
  b7 = at 7 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 6 2 (CS24 ∷ Toff023 ∷ []) (sym (wp0070 c4)) ▸
       at 7 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 8 2 (CS24⁻ ∷ Toff023 ∷ []) (sym (wp0069 c4)) ▸
       at 9 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 10 2 (CS12 ∷ Toff023 ∷ []) (sym (wl0221 (lit c4))) ▸
       at 6 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 7 2 (Toff024 ∷ Toff324 ∷ Toff023 ∷ []) (wp0805 c4) ▸ done

  b8 : Chain (CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff024 ∷ CCZ124 ∷ Toff024 ∷ Toff324 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS14 ∷ []) (CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CCZ014 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS14 ∷ [])
  b8 = at 5 3 (CCZ124 ∷ []) (sym (wp0074 c4)) ▸
       at 4 2 (CCZ124 ∷ CCZ014 ∷ []) (wp0066 c4) ▸
       at 6 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 5 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸
       at 6 2 (CS34 ∷ CCZ014 ∷ []) (wp0064 c4) ▸
       at 7 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 8 2 (CS34⁻ ∷ CCZ014 ∷ []) (wp0063 c4) ▸
       at 9 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸ done

  b9 : Chain (CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CCZ014 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS14 ∷ []) (CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ CS13⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS14 ∷ [])
  b9 = at 10 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸
       at 11 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸
       at 5 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 6 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 6 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 9 2 (CS13⁻ ∷ Toff023 ∷ []) (sym (wl0219 (lit c4))) ▸
       at 8 2 (CS13⁻ ∷ CCZ014 ∷ []) (wp0060 c4) ▸
       at 7 2 (CS13⁻ ∷ Toff023 ∷ []) (sym (wl0219 (lit c4))) ▸ done

  b10 : Chain (CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ CS13⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS14 ∷ []) (CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ014 ∷ Toff023 ∷ CS24 ∷ CCZ014 ∷ Toff023 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS14 ∷ [])
  b10 = at 6 2 (CS13⁻ ∷ CCZ014 ∷ []) (wp0060 c4) ▸
       at 7 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 7 1 (Bx0-1342 ∷ []) (lem-box-perm-1423-at243243 c4) ▸
       at 7 2 (CCZ123 ∷ CK42 ∷ CCZ123 ∷ Bx0-1342 ∷ []) (lem-CKc-box-at233442 c4) ▸
       at 10 1 (Bx0-1423 ∷ []) (lem-box-perm-1342-at233442 c4) ▸
       at 10 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 13 2 (CS24 ∷ Toff023 ∷ []) (sym (wp0070 c4)) ▸
       at 12 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸ done

  b11 : Chain (CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ014 ∷ Toff023 ∷ CS24 ∷ CCZ014 ∷ Toff023 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS14 ∷ []) (CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CS24 ∷ CS24 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CK42 ∷ S4 ∷ CS14 ∷ [])
  b11 = at 11 2 (CS24 ∷ Toff023 ∷ []) (sym (wp0070 c4)) ▸
       at 10 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸
       at 11 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 11 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 14 2 (CS24 ∷ Toff023 ∷ []) (sym (wp0070 c4)) ▸
       at 13 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸
       at 12 2 (CS24 ∷ Toff023 ∷ []) (sym (wp0070 c4)) ▸
       at 11 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸ done

  b12 : Chain (CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CS24 ∷ CS24 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CK42 ∷ S4 ∷ CS14 ∷ []) (CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CS24 ∷ CS24 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ014 ∷ S4 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS14 ∷ [])
  b12 = at 12 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 12 1 (Bx0-1342 ∷ []) (lem-box-perm-1423-at243243 c4) ▸
       at 12 2 (CCZ123 ∷ CK42 ∷ CCZ123 ∷ Bx0-1342 ∷ []) (lem-CKc-box-at233442 c4) ▸
       at 15 1 (Bx0-1423 ∷ []) (lem-box-perm-1342-at233442 c4) ▸
       at 15 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 18 2 (S4 ∷ Toff023 ∷ []) (sym (wp0632 c4)) ▸
       at 17 2 (S4 ∷ CCZ014 ∷ []) (wp0633 c4) ▸
       at 16 2 (S4 ∷ Toff023 ∷ []) (sym (wp0632 c4)) ▸ done

  b13 : Chain (CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CS24 ∷ CS24 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ014 ∷ S4 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS14 ∷ []) (CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CS24 ∷ CS24 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CS14 ∷ Bx0-1423 ∷ [])
  b13 = at 15 2 (S4 ∷ CCZ014 ∷ []) (wp0633 c4) ▸
       at 16 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 16 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 19 2 (CS14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CS14 (lit c4)) ▸
       at 18 2 (CS14 ∷ CCZ014 ∷ []) (wp0908 c4) ▸
       at 17 2 (CS14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CS14 (lit c4)) ▸
       at 16 2 (CS14 ∷ CCZ014 ∷ []) (wp0908 c4) ▸
       at 17 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸ done

  b14 : Chain (CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CS24 ∷ CS24 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CS14 ∷ Bx0-1423 ∷ []) (Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CS14 ∷ Bx0-1423 ∷ [])
  b14 = at 0 2 [] (wl0263 (lit c4)) ▸
       at 7 3 (CS24 ∷ CS24 ∷ CCZ123 ∷ []) (wl1146 (lit c4)) ▸
       at 9 2 [] (wl0181 (lit c4)) ▸ done


-- F1-X-CS1@1: 86 steps
lem-F1-X-CS1at1 : Ws → ⟪ (CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS14 ∷ []) ⟫ʷ
lem-F1-X-CS1at1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (run b10))))))))))
  where
  b0 : Chain (CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ Sb0-1-42-3 ∷ []) (CX42 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ124 ∷ CCZ014 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b0 = at 5 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 7 1 (CS13 ∷ []) (refl) ▸
       at 9 1 (CS13⁻ ∷ []) (refl) ▸
       at 0 5 (CX42 ∷ []) (wl1147 (lit c4)) ▸
       at 1 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 4 2 (Toff024 ∷ Toff324 ∷ Toff023 ∷ []) (wp0805 c4) ▸
       at 3 2 (Toff024 ∷ CCZ124 ∷ CCZ014 ∷ []) (wp0806 c4) ▸
       at 6 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸ done

  b1 : Chain (CX42 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ124 ∷ CCZ014 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (CX42 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b1 = at 5 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸
       at 6 2 (CS34 ∷ CCZ014 ∷ []) (wp0064 c4) ▸
       at 7 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 8 2 (CS34⁻ ∷ CCZ014 ∷ []) (wp0063 c4) ▸
       at 9 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 10 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸
       at 11 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸
       at 5 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸ done

  b2 : Chain (CX42 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (CX42 ∷ CCZ014 ∷ Toff024 ∷ CCZ124 ∷ Toff023 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b2 = at 2 2 (Toff024 ∷ Toff023 ∷ []) (wp0072 c4) ▸
       at 4 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 3 2 (CS24 ∷ Toff023 ∷ []) (sym (wp0070 c4)) ▸
       at 4 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 5 2 (CS24⁻ ∷ Toff023 ∷ []) (sym (wp0069 c4)) ▸
       at 6 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 7 2 (CS12 ∷ Toff023 ∷ []) (sym (wl0221 (lit c4))) ▸
       at 3 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸ done

  b3 : Chain (CX42 ∷ CCZ014 ∷ Toff024 ∷ CCZ124 ∷ Toff023 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (CX42 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CCZ014 ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b3 = at 4 2 (Toff024 ∷ Toff324 ∷ Toff023 ∷ []) (wp0805 c4) ▸
       at 2 3 (CCZ124 ∷ []) (sym (wp0074 c4)) ▸
       at 1 2 (CCZ124 ∷ CCZ014 ∷ []) (wp0066 c4) ▸
       at 3 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 2 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸
       at 3 2 (CS34 ∷ CCZ014 ∷ []) (wp0064 c4) ▸
       at 4 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 5 2 (CS34⁻ ∷ CCZ014 ∷ []) (wp0063 c4) ▸ done

  b4 : Chain (CX42 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CCZ014 ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (CX42 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b4 = at 6 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 7 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸
       at 8 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸
       at 2 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 3 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 3 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 6 2 (CS13 ∷ Toff023 ∷ []) (sym (wl0222 (lit c4))) ▸
       at 5 2 (CS13 ∷ CCZ014 ∷ []) (wp0053 c4) ▸ done

  b5 : Chain (CX42 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13⁻ ∷ []) (CX42 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ124 ∷ K3 ∷ CCZ014 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CS13⁻ ∷ [])
  b5 = at 4 2 (CS13 ∷ Toff023 ∷ []) (sym (wl0222 (lit c4))) ▸
       at 3 2 (CS13 ∷ CCZ014 ∷ []) (wp0053 c4) ▸
       at 4 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 4 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 7 2 (Toff024 ∷ Toff324 ∷ Toff023 ∷ []) (wp0805 c4) ▸
       at 6 2 (Toff024 ∷ CCZ124 ∷ CCZ014 ∷ []) (wp0806 c4) ▸
       at 9 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 8 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸ done

  b6 : Chain (CX42 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ124 ∷ K3 ∷ CCZ014 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CS13⁻ ∷ []) (CX42 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff024 ∷ Toff023 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ [])
  b6 = at 9 2 (CS34 ∷ CCZ014 ∷ []) (wp0064 c4) ▸
       at 10 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 11 2 (CS34⁻ ∷ CCZ014 ∷ []) (wp0063 c4) ▸
       at 12 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 13 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸
       at 14 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸
       at 8 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 5 2 (Toff024 ∷ Toff023 ∷ []) (wp0072 c4) ▸ done

  b7 : Chain (CX42 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff024 ∷ Toff023 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ []) (CX42 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff024 ∷ CCZ124 ∷ Toff024 ∷ Toff324 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ [])
  b7 = at 7 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 6 2 (CS24 ∷ Toff023 ∷ []) (sym (wp0070 c4)) ▸
       at 7 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 8 2 (CS24⁻ ∷ Toff023 ∷ []) (sym (wp0069 c4)) ▸
       at 9 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 10 2 (CS12 ∷ Toff023 ∷ []) (sym (wl0221 (lit c4))) ▸
       at 6 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 7 2 (Toff024 ∷ Toff324 ∷ Toff023 ∷ []) (wp0805 c4) ▸ done

  b8 : Chain (CX42 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff024 ∷ CCZ124 ∷ Toff024 ∷ Toff324 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ []) (CX42 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CCZ014 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ [])
  b8 = at 5 3 (CCZ124 ∷ []) (sym (wp0074 c4)) ▸
       at 4 2 (CCZ124 ∷ CCZ014 ∷ []) (wp0066 c4) ▸
       at 6 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 5 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸
       at 6 2 (CS34 ∷ CCZ014 ∷ []) (wp0064 c4) ▸
       at 7 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 8 2 (CS34⁻ ∷ CCZ014 ∷ []) (wp0063 c4) ▸
       at 9 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸ done

  b9 : Chain (CX42 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CCZ014 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ []) (CX42 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ CS13⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ [])
  b9 = at 10 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸
       at 11 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸
       at 5 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 6 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 6 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 9 2 (CS13⁻ ∷ Toff023 ∷ []) (sym (wl0219 (lit c4))) ▸
       at 8 2 (CS13⁻ ∷ CCZ014 ∷ []) (wp0060 c4) ▸
       at 7 2 (CS13⁻ ∷ Toff023 ∷ []) (sym (wl0219 (lit c4))) ▸ done

  b10 : Chain (CX42 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ CS13⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS14 ∷ [])
  b10 = at 6 2 (CS13⁻ ∷ CCZ014 ∷ []) (wp0060 c4) ▸
       at 7 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 1 3 (Toff324 ∷ CS13 ∷ CCZ124 ∷ []) (wl1000 (lit c4)) ▸
       at 3 2 [] (wl0263 (lit c4)) ▸
       at 0 5 (Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CS14 ∷ []) (wl1169 (lit c4)) ▸
       at 0 14 (Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS14 ∷ []) (sym (lem-nf-X-CS1at1 c4)) ▸ done


-- CXbc-box @12213443: 17 steps
lem-CXbc-box-at12213443 : Ws → ⟪ (CX14 ∷ Bx0-2143 ∷ CX14 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2143 ∷ CCZ123 ∷ []) ⟫ʷ
lem-CXbc-box-at12213443 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX14 ∷ Bx0-2143 ∷ CX14 ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CX14 ∷ CCZ013 ∷ CS13 ∷ CX21 ∷ CS13⁻ ∷ CCZ034 ∷ CX21 ∷ CS23 ∷ CX14 ∷ [])
  b0 = at 1 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-box-tQ-at12213443 c4) ▸
       at 0 2 (Toff012 ∷ CX14 ∷ []) (wp0974 c4) ▸
       at 1 2 (CCZ034 ∷ CX14 ∷ CCZ013 ∷ []) (sym (wp0735 c4)) ▸
       at 3 2 (Toff012 ∷ CCZ013 ∷ CCZ123 ∷ []) (wl1170 (lit c4)) ▸
       at 2 2 (Toff012 ∷ CX14 ∷ []) (wp0974 c4) ▸
       at 5 1 (CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ []) (wl0326 (lit c4)) ▸
       at 9 2 (CCZ034 ∷ CS23 ∷ []) (sym (wp0314 c4)) ▸
       at 8 2 (CCZ034 ∷ CX21 ∷ []) (lem-comm-CX21-CCZ034 (lit c4)) ▸ done

  b1 : Chain (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CX14 ∷ CCZ013 ∷ CS13 ∷ CX21 ∷ CS13⁻ ∷ CCZ034 ∷ CX21 ∷ CS23 ∷ CX14 ∷ []) (Bx0-2143 ∷ CX14 ∷ CCZ123 ∷ CX14 ∷ [])
  b1 = at 7 2 (CCZ034 ∷ CS13⁻ ∷ []) (sym (wp0734 c4)) ▸
       at 6 2 (CCZ034 ∷ CX21 ∷ []) (lem-comm-CX21-CCZ034 (lit c4)) ▸
       at 5 2 (CCZ034 ∷ CS13 ∷ []) (sym (wp0312 c4)) ▸
       at 6 5 (CCZ123 ∷ []) (sym (wl0326 (lit c4))) ▸
       at 4 2 (CCZ034 ∷ CCZ013 ∷ []) (wp0186 c4) ▸
       at 3 2 (CCZ034 ∷ CX14 ∷ CCZ013 ∷ []) (sym (wp0735 c4)) ▸
       at 4 3 (CX14 ∷ []) (wp0736 c4) ▸
       at 0 4 (Bx0-2143 ∷ []) (sym (lem-box-tQ-at12213443 c4)) ▸ done

  b2 : Chain (Bx0-2143 ∷ CX14 ∷ CCZ123 ∷ CX14 ∷ []) (Bx0-2143 ∷ CCZ123 ∷ [])
  b2 = at 1 3 (CCZ123 ∷ []) (sym (wl0299 (lit c4))) ▸ done


-- CXcb-box @12213443: 18 steps
lem-CXcb-box-at12213443 : Ws → ⟪ (CX41 ∷ Bx0-2143 ∷ CX41 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2143 ∷ CCZ234 ∷ []) ⟫ʷ
lem-CXcb-box-at12213443 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX41 ∷ Bx0-2143 ∷ CX41 ∷ []) (Toff012 ∷ CCZ034 ∷ CX41 ∷ Toff024 ∷ CS34 ∷ CX24 ∷ Toff012 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ CCZ034 ∷ CX41 ∷ [])
  b0 = at 1 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-box-tQ-at12213443 c4) ▸
       at 0 2 (Toff012 ∷ CX41 ∷ Toff024 ∷ []) (wp0975 c4) ▸
       at 2 2 (CCZ034 ∷ Toff024 ∷ CCZ234 ∷ []) (sym (wp0976 c4)) ▸
       at 1 2 (CCZ034 ∷ CX41 ∷ []) (sym (wp0357 c4)) ▸
       at 4 1 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (wl0245 (lit c4)) ▸
       at 8 2 (Toff012 ∷ CS23 ∷ []) (wl1171 (lit c4)) ▸
       at 7 2 (Toff012 ∷ CX24 ∷ []) (wp0977 c4) ▸
       at 6 2 (Toff012 ∷ CS34⁻ ∷ []) (sym (c₃ (Toff) (CS • CS • CS))) ▸ done

  b1 : Chain (Toff012 ∷ CCZ034 ∷ CX41 ∷ Toff024 ∷ CS34 ∷ CX24 ∷ Toff012 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ CCZ034 ∷ CX41 ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ CX41 ∷ CCZ234 ∷ CX41 ∷ [])
  b1 = at 5 2 (Toff012 ∷ CX24 ∷ []) (wp0977 c4) ▸
       at 4 2 (Toff012 ∷ CS34 ∷ []) (sym (c₃ (Toff) (CS))) ▸
       at 5 5 (CCZ234 ∷ []) (sym (wl0245 (lit c4))) ▸
       at 3 2 (Toff012 ∷ Toff024 ∷ []) (sym (wp0192 c4)) ▸
       at 2 2 (Toff012 ∷ CX41 ∷ Toff024 ∷ []) (wp0975 c4) ▸
       at 3 3 (CX41 ∷ []) (wp0978 c4) ▸
       at 4 2 (CCZ034 ∷ CCZ234 ∷ []) (sym (wp0129 c4)) ▸
       at 3 2 (CCZ034 ∷ CX41 ∷ []) (sym (wp0357 c4)) ▸ done

  b2 : Chain (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ CX41 ∷ CCZ234 ∷ CX41 ∷ []) (Bx0-2143 ∷ CCZ234 ∷ [])
  b2 = at 0 4 (Bx0-2143 ∷ []) (sym (lem-box-tQ-at12213443 c4)) ▸
       at 1 3 (CCZ234 ∷ []) (sym (wl0295 (lit c4))) ▸ done


-- SWbc-box @12213443: 11 steps
lem-SWbc-box-at12213443 : Ws → ⟪ (Sw14 ∷ Bx0-2143 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2143 ∷ []) ⟫ʷ
lem-SWbc-box-at12213443 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw14 ∷ Bx0-2143 ∷ Sw14 ∷ []) (CX14 ∷ Bx0-2143 ∷ CX14 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ [])
  b0 = at 0 1 (CX14 ∷ CX41 ∷ CX14 ∷ []) (sym (wl0423 (lit c4))) ▸
       at 4 1 (CX14 ∷ CX41 ∷ CX14 ∷ []) (sym (wl0423 (lit c4))) ▸
       at 2 3 (Bx0-2143 ∷ CCZ123 ∷ []) (lem-CXbc-box-at12213443 c4) ▸
       at 3 2 (CX41 ∷ CCZ234 ∷ CCZ123 ∷ []) (wl0303 (lit c4)) ▸
       at 1 3 (Bx0-2143 ∷ CCZ234 ∷ []) (lem-CXcb-box-at12213443 c4) ▸
       at 4 2 (CX14 ∷ CCZ123 ∷ []) (wl0424 (lit c4)) ▸
       at 3 2 (CX14 ∷ CCZ123 ∷ CCZ234 ∷ []) (wl0301 (lit c4)) ▸
       at 2 2 (CX14 ∷ CCZ123 ∷ CCZ234 ∷ []) (wl0301 (lit c4)) ▸ done

  b1 : Chain (CX14 ∷ Bx0-2143 ∷ CX14 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ []) (Bx0-2143 ∷ [])
  b1 = at 3 5 (CCZ123 ∷ []) (wl0425 (lit c4)) ▸
       at 0 3 (Bx0-2143 ∷ CCZ123 ∷ []) (lem-CXbc-box-at12213443 c4) ▸
       at 1 2 [] (wl0181 (lit c4)) ▸ done


-- nat-SWbc @12213443: 23 steps
lem-nat-SWbc-at12213443 : Ws → ⟪ (Sw14 ∷ Bx0-2143 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2413 ∷ []) ⟫ʷ
lem-nat-SWbc-at12213443 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw14 ∷ Bx0-2143 ∷ Sw14 ∷ []) (CCZ024 ∷ Toff024 ∷ CCZ012 ∷ Toff201 ∷ Bx0-23 ∷ Toff201 ∷ Sw14 ∷ CCZ024 ∷ Bx0-23 ∷ Toff012 ∷ CCZ012 ∷ Bx2-043 ∷ Sw14 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff012 ∷ Bx2-043 ∷ Toff012 ∷ CCZ012 ∷ Bx2-043 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw14 ∷ []) (sym (wp0196 c4)) ▸
       at 1 2 (Toff024 ∷ Sw14 ∷ []) (wp0570 c4) ▸
       at 3 1 (CCZ024 ∷ Toff204 ∷ Bx0-23 ∷ Toff204 ∷ CCZ024 ∷ Bx0-23 ∷ []) (refl) ▸
       at 2 2 (CCZ012 ∷ Sw14 ∷ []) (sym (wp0194 c4)) ▸
       at 3 2 (Toff201 ∷ Sw14 ∷ []) (wp0569 c4) ▸
       at 4 2 (Bx0-23 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨0·23⟩ (lit c4)) ▸
       at 5 2 (Toff201 ∷ Sw14 ∷ []) (wp0569 c4) ▸ done

  b1 : Chain (CCZ024 ∷ Toff024 ∷ CCZ012 ∷ Toff201 ∷ Bx0-23 ∷ Toff201 ∷ Sw14 ∷ CCZ024 ∷ Bx0-23 ∷ Toff012 ∷ CCZ012 ∷ Bx2-043 ∷ Sw14 ∷ []) (CCZ024 ∷ Toff024 ∷ CCZ012 ∷ Toff201 ∷ Bx0-23 ∷ Toff201 ∷ CCZ012 ∷ Bx0-23 ∷ Toff024 ∷ CCZ024 ∷ CCZ012 ∷ Toff201 ∷ Bx0-23 ∷ Sw14 ∷ Toff204 ∷ CCZ024 ∷ Bx0-23 ∷ Sw14 ∷ [])
  b1 = at 6 2 (CCZ012 ∷ Sw14 ∷ []) (sym (wp0194 c4)) ▸
       at 7 2 (Bx0-23 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨0·23⟩ (lit c4)) ▸
       at 8 2 (Toff024 ∷ Sw14 ∷ []) (wp0570 c4) ▸
       at 9 2 (CCZ024 ∷ Sw14 ∷ []) (sym (wp0196 c4)) ▸
       at 11 1 (CCZ024 ∷ Toff204 ∷ Bx0-23 ∷ Toff204 ∷ CCZ024 ∷ Bx0-23 ∷ []) (refl) ▸
       at 10 2 (CCZ012 ∷ Sw14 ∷ []) (sym (wp0194 c4)) ▸
       at 11 2 (Toff201 ∷ Sw14 ∷ []) (wp0569 c4) ▸
       at 12 2 (Bx0-23 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨0·23⟩ (lit c4)) ▸ done

  b2 : Chain (CCZ024 ∷ Toff024 ∷ CCZ012 ∷ Toff201 ∷ Bx0-23 ∷ Toff201 ∷ CCZ012 ∷ Bx0-23 ∷ Toff024 ∷ CCZ024 ∷ CCZ012 ∷ Toff201 ∷ Bx0-23 ∷ Sw14 ∷ Toff204 ∷ CCZ024 ∷ Bx0-23 ∷ Sw14 ∷ []) (Bx0-2413 ∷ [])
  b2 = at 13 2 (Toff201 ∷ Sw14 ∷ []) (wp0569 c4) ▸
       at 14 2 (CCZ012 ∷ Sw14 ∷ []) (sym (wp0194 c4)) ▸
       at 15 2 (Bx0-23 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨0·23⟩ (lit c4)) ▸
       at 16 2 [] (wl0306 (lit c4)) ▸
       at 2 6 (Bx2-013 ∷ []) (refl) ▸
       at 5 6 (Bx2-013 ∷ []) (refl) ▸
       at 0 6 (Bx0-2413 ∷ []) (refl) ▸ done

