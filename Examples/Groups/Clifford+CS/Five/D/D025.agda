{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D025 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0166 ; wl0167 ; wl0184 ; wl0187 ; wl0188 ; wl0189 ; wl0190 ; wl0191 ; wl0192 ; wl0193 ; wl0194 ; wl0195 ; wl0196 ; wl0197 ; wl0198 ; wl0206 ; wl0207 ; wl0211 ; wl0212 ; wl0213 ; wl0214 ; wl0215 ; wl0216 ; wl0217 ; wl0218 ; wl0219 ; wl0220 ; wl0221 ; wl0222 ; wl0223 ; wl0224 ; wl0235 ; wl0236 ; wl0237 ; wl0238 ; wl0239 ; wl0240 ; wl0241 ; wl0242 ; wl0243 ; wl0244 ; wl0245 ; wl0246 ; wl0247 ; wl0248 ; wl0249 ; wl0274 ; wp0011 ; wp0012 ; wp0021 ; wp0022 ; wp0029 ; wp0030 ; wp0031 ; wp0032 ; wp0033 ; wp0034 ; wp0035 ; wp0036 ; wp0037 ; wp0038 ; wp0039 ; wp0040 ; wp0041 ; wp0042 ; wp0043 ; wp0044 ; wp0045 ; wp0053 ; wp0054 ; wp0055 ; wp0060 ; wp0061 ; wp0062 ; wp0063 ; wp0064 ; wp0065 ; wp0066 ; wp0067 ; wp0068 ; wp0069 ; wp0070 ; wp0071 ; wp0072 ; wp0073 ; wp0074 ; wp0081 ; wp0087 ; wp0088 ; wp0089 ; wp0090 ; wp0091 ; wp0092 ; wp0093 ; wp0094 ; wp0095 ; wp0096 ; wp0097 ; wp0098 ; wp0099 ; wl0321 ; wp0139 ; wp0141 ; wp0142 ; wp0146 ; wp0171 ; wl0362 ; wl0363 ; wl0375 ; wl0376 ; wl0385 ; wl0386 ; wl0387 ; wl0388 ; wl0411 ; wp0255 ; wp0256 ; wp0257 ; wp0258 ; wl0470 ; wl0472 ; wp0325 ; wp0326 ; wp0327 ; wp0328 ; wp0329 ; wl0654 ; wl0664 ; wp0531 ; wl0697 ; wl0700 ; wl0704 ; wl0708 ; wl0720 ; wl0722 ; wl0723 ; wl0724 ; wl0729 ; wl0730 ; wl0731 ; wl0738 ; wp0571 ; wp0586 ; wp0618 ; wp0636 ; wl0741 ; wl0744 ; wp0648 ; wl0788 ; wl0794 ; wl0795 ; wl0796 ; wl0797 ; wl0798 ; wl0799 ; wl0810 ; wl0811 ; wl0812 ; wl0813 ; wl0940 ; wp0751 ; wp0752 ; wl0952 ; wl0953 ; wl0954 ; wp0770 ; wp0771 ; wp0772 ; wl1065 ; wl1066 ; wp0876 ; wp0877)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-sym-ab ; lem-sym-ab-at0210233441 ; lem-sym-ab-at0210243143 ; lem-sym-ab-at0213203441 ; lem-sym-ab-at03102132 ; lem-sym-ab-at0310243142 ; lem-sym-ab-at0314203142 ; lem-sym-ab-at032032 ; lem-sym-ab-at033440 ; lem-sym-ab-at1221 ; lem-sym-ab-at122331 ; lem-sym-ab-at12243143 ; lem-sym-ab-at13213442 ; lem-sym-ab-at13243142 ; lem-sym-ab-at13243241 ; lem-sym-ab-at133441 ; lem-sym-ab-at14233142 ; lem-sym-ab-at2332 ; lem-sym-ab-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-sym-ab-at021021 ; lem-sym-ab-at0220 ; lem-sym-ab-at132132 ; lem-sym-ab-at1331 ; lem-sym-ab-at14213243)
open import Examples.Groups.Clifford+CS.Five.D.D006 using (lem-box-tQ-at0314213042 ; lem-box-tQ-at043043 ; lem-box-tQ-at12233441)
open import Examples.Groups.Clifford+CS.Five.D.D007 using (lem-box-tQ-at02233440)
open import Examples.Groups.Clifford+CS.Five.D.D009 using (lem-CSdu-box-1 ; lem-CSdu-box-2 ; lem-CSdu-box-2-at0210243143 ; lem-CSdu-box-2-at122441 ; lem-CSdu-box-2-at243243 ; lem-CSu-box-1 ; lem-CSu-box-2 ; lem-CSu-box-2-at122441 ; lem-CSu-box-2-at243243 ; lem-Sdu-box ; lem-Su-box)
open import Examples.Groups.Clifford+CS.Five.D.D010 using (lem-CSu-box-2-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D014 using (lem-box-cP-at0210213443 ; lem-sym-bc-at0220 ; lem-sym-bc-at032032 ; lem-sym-bc-at13243142 ; lem-sym-bc-at13243241 ; lem-sym-bc-at14233142)
open import Examples.Groups.Clifford+CS.Five.D.D016 using (lem-box-cP-at0210243143 ; lem-box-cP-at1221 ; lem-box-cP-at12213443 ; lem-box-cP-at12233441 ; lem-box-cP-at122441 ; lem-box-cP-at243243 ; lem-box-cP-at3443 ; lem-pairs-at13243142 ; lem-pairs-at14233142 ; lem-sym-bc ; lem-sym-bc-at0214203143 ; lem-sym-bc-at022330 ; lem-sym-bc-at0312213440 ; lem-sym-bc-at0330 ; lem-sym-bc-at1221 ; lem-sym-bc-at122331 ; lem-sym-bc-at12233441 ; lem-sym-bc-at12243143 ; lem-sym-bc-at122441 ; lem-sym-bc-at132132 ; lem-sym-bc-at1331 ; lem-sym-bc-at14213243 ; lem-sym-bc-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D018 using (lem-CSdu-box-3 ; lem-CSdu-box-3-at043043 ; lem-CSdu-box-4 ; lem-CSu-box-3 ; lem-CSu-box-4 ; lem-Kdu-box ; lem-Kdu-box-at0210243143 ; lem-Kdu-box-at122441 ; lem-Kdu-box-at243243 ; lem-Ku-box ; lem-Ku-box-at0210243143 ; lem-Ku-box-at122441 ; lem-Ku-box-at243243 ; lem-Xb-box-at0210243143 ; lem-Xb-box-at122441 ; lem-Xb-box-at243243 ; lem-box-perm-1324-at0210243143 ; lem-box-perm-1324-at122441 ; lem-box-perm-1324-at243243 ; lem-box-perm-1423-at122441 ; lem-box2-at0210243143 ; lem-box2-at122441 ; lem-box2-at243243 ; lem-pairs ; lem-pairs-at0214213043 ; lem-pairs-at0310243142 ; lem-pairs-at0330 ; lem-pairs-at1221 ; lem-pairs-at122331 ; lem-pairs-at132132 ; lem-pairs-at13213442 ; lem-pairs-at1331 ; lem-pairs-at143143 ; lem-pairs-at2332 ; lem-pairs-at3443)
open import Examples.Groups.Clifford+CS.Five.D.D019 using (lem-CSdu-box-3-at0314213042 ; lem-CXu-box-4-at0210243143 ; lem-box-perm-2341-at021021 ; lem-box-perm-4123-at02233440 ; lem-pairs-at0210233441 ; lem-pairs-at0210243143 ; lem-pairs-at022330 ; lem-pairs-at0312243140 ; lem-pairs-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D020 using (lem-pairs-at12233441 ; lem-pairs-at122441 ; lem-pairs-at14213243)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CS03-TOFF412 ; lem-comm-CS13-CCZ024 ; lem-comm-CS23-CCZ014 ; lem-comm-CSd13-CCZ024 ; lem-comm-CSd23-CCZ014 ; lem-comm-CX04-TOFF213 ; lem-comm-CX13-CCZ024 ; lem-comm-CX14-TOFF023 ; lem-comm-CX23-CCZ014 ; lem-comm-CX24-TOFF013)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-CK41-CCZ023 ; lem-comm-CK41-TOFF023 ; lem-comm-CS02-TOFF314 ; lem-comm-CX21-TOFF034 ; lem-comm-TOFF214-CS03)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-comm-CCZ023-CK41)

-- F5-01: 112 steps
lem-F5-01 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ []) ⟫ʷ
lem-F5-01 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (run b13)))))))))))))
  where
  b0 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (X4 ∷ Bx2-0413 ∷ Toff314 ∷ X4 ∷ CX13 ∷ CS01 ∷ CCZ013 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b0 = at 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 5 2 (X4 ∷ Sb⁻2-0-3-1 ∷ []) (c₄ (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑) (X)) ▸
       at 4 2 (X4 ∷ CX13 ∷ Toff314 ∷ []) (wl0187 (lit c4)) ▸
       at 3 2 (X4 ∷ Sb2-0-3-1 ∷ []) (c₄ (Swap ↑ ↑ • (Swap ↑ • CS • Swap ↑) • Swap ↑ ↑) (X)) ▸
       at 4 1 (CS03 ∷ []) (refl) ▸
       at 4 2 (CX13 ∷ CS01 ∷ CCZ013 ∷ CS03 ∷ []) (wl0188 (lit c4)) ▸
       at 7 1 (Sb2-0-3-1 ∷ []) (refl) ▸ done

  b1 : Chain (X4 ∷ Bx2-0413 ∷ Toff314 ∷ X4 ∷ CX13 ∷ CS01 ∷ CCZ013 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ CCZ013 ∷ CS01 ∷ CCZ013 ∷ CCZ014 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ CS03⁻ ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b1 = at 2 2 (X4 ∷ CX13 ∷ Toff314 ∷ []) (wl0187 (lit c4)) ▸
       at 4 2 (CX13 ∷ Toff314 ∷ []) (sym (wl0189 (lit c4))) ▸
       at 5 2 (CS01 ∷ Toff314 ∷ []) (sym (wp0029 c4)) ▸
       at 6 2 (CCZ013 ∷ CCZ014 ∷ Toff314 ∷ []) (sym (wp0030 c4)) ▸
       at 2 6 (X4 ∷ CS01 ∷ CCZ013 ∷ CCZ014 ∷ []) (sym (wp0031 c4)) ▸
       at 0 3 (Bx2-0413 ∷ CCZ013 ∷ []) (lem-Xb-box-at0210243143 c4) ▸
       at 9 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 8 1 (CS03⁻ ∷ []) (refl) ▸ done

  b2 : Chain (Bx2-0413 ∷ CCZ013 ∷ CS01 ∷ CCZ013 ∷ CCZ014 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ CS03⁻ ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ CCZ013 ∷ CS01 ∷ CCZ013 ∷ CCZ014 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CCZ024 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ CS03⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b2 = at 8 2 (CCZ024 ∷ CS03⁻ ∷ []) (sym (wp0032 c4)) ▸
       at 7 1 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (sym (wl0190 (lit c4))) ▸
       at 13 2 (CCZ024 ∷ K3⁻ ∷ []) (sym (wp0033 c4)) ▸
       at 12 2 (CCZ024 ∷ CS14 ∷ []) (sym (wp0034 c4)) ▸
       at 11 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 10 2 (CCZ024 ∷ CS34⁻ ∷ []) (sym (wp0035 c4)) ▸
       at 9 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 8 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸ done

  b3 : Chain (Bx2-0413 ∷ CCZ013 ∷ CS01 ∷ CCZ013 ∷ CCZ014 ∷ Toff314 ∷ Sb2-0-3-1 ∷ K3 ∷ CCZ024 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ CS03⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ CCZ013 ∷ CS01 ∷ CCZ013 ∷ CCZ014 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CCZ024 ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b3 = at 7 2 (CCZ024 ∷ K3 ∷ []) (sym (wp0037 c4)) ▸
       at 8 7 (Toff314 ∷ []) (wl0190 (lit c4)) ▸
       at 6 1 (CS03 ∷ []) (refl) ▸
       at 6 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸
       at 5 1 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (sym (wl0190 (lit c4))) ▸
       at 11 2 (CCZ024 ∷ K3⁻ ∷ []) (sym (wp0033 c4)) ▸
       at 10 2 (CCZ024 ∷ CS14 ∷ []) (sym (wp0034 c4)) ▸
       at 9 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸ done

  b4 : Chain (Bx2-0413 ∷ CCZ013 ∷ CS01 ∷ CCZ013 ∷ CCZ014 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CCZ024 ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ CCZ013 ∷ CS01 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CCZ024 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b4 = at 8 2 (CCZ024 ∷ CS34⁻ ∷ []) (sym (wp0035 c4)) ▸
       at 7 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 6 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 5 2 (CCZ024 ∷ K3 ∷ []) (sym (wp0037 c4)) ▸
       at 6 7 (Toff314 ∷ []) (wl0190 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ CCZ014 ∷ []) (wp0038 c4) ▸
       at 3 1 (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ []) (wl0184 (lit c4)) ▸
       at 7 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸ done

  b5 : Chain (Bx2-0413 ∷ CCZ013 ∷ CS01 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CCZ024 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CCZ024 ∷ CS03 ∷ CS01 ∷ CCZ013 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b5 = at 6 2 (CCZ024 ∷ CX01 ∷ []) (sym (wp0022 c4)) ▸
       at 5 2 (CCZ024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-CCZ024 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ CX01 ∷ []) (sym (wp0022 c4)) ▸
       at 3 2 (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 (lit c4)) ▸
       at 4 5 (CCZ013 ∷ []) (sym (wl0184 (lit c4))) ▸
       at 2 2 (CCZ024 ∷ CS01 ∷ []) (sym (wp0039 c4)) ▸
       at 1 1 (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ []) (wl0184 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸ done

  b6 : Chain (Bx2-0413 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CCZ024 ∷ CS03 ∷ CS01 ∷ CCZ013 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ CCZ024 ∷ Toff314 ∷ CS01 ∷ CS03 ∷ CCZ014 ∷ Toff213 ∷ Toff214 ∷ Toff314 ∷ CS03⁻ ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b6 = at 4 2 (CCZ024 ∷ CX01 ∷ []) (sym (wp0022 c4)) ▸
       at 3 2 (CCZ024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-CCZ024 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ CX01 ∷ []) (sym (wp0022 c4)) ▸
       at 1 2 (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 (lit c4)) ▸
       at 2 5 (CCZ013 ∷ []) (sym (wl0184 (lit c4))) ▸
       at 2 6 (Toff314 ∷ CS01 ∷ CS03 ∷ CCZ014 ∷ []) (wp0040 c4) ▸
       at 7 2 (Toff213 ∷ CS03⁻ ∷ []) (wl0191 (lit c4)) ▸
       at 6 2 (Toff213 ∷ Toff214 ∷ Toff314 ∷ []) (sym (wl0192 (lit c4))) ▸ done

  b7 : Chain (Bx2-0413 ∷ CCZ024 ∷ Toff314 ∷ CS01 ∷ CS03 ∷ CCZ014 ∷ Toff213 ∷ Toff214 ∷ Toff314 ∷ CS03⁻ ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ CCZ024 ∷ Toff314 ∷ CS01 ∷ Toff213 ∷ CS03 ∷ CCZ014 ∷ Toff214 ∷ Toff314 ∷ CS03⁻ ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b7 = at 5 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4) ▸
       at 9 2 (Toff213 ∷ CS01 ∷ []) (wl0193 (lit c4)) ▸
       at 8 2 (Toff213 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF213 (lit c4)) ▸
       at 7 2 (Toff213 ∷ CS14⁻ ∷ []) (wl0194 (lit c4)) ▸
       at 6 2 (Toff213 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF213 (lit c4)) ▸
       at 5 2 (Toff213 ∷ CS14 ∷ []) (wl0195 (lit c4)) ▸
       at 6 5 (CCZ014 ∷ []) (sym (wp0041 c4)) ▸
       at 4 2 (Toff213 ∷ CS03 ∷ []) (wl0196 (lit c4)) ▸ done

  b8 : Chain (Bx2-0413 ∷ CCZ024 ∷ Toff314 ∷ CS01 ∷ Toff213 ∷ CS03 ∷ CCZ014 ∷ Toff214 ∷ Toff314 ∷ CS03⁻ ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ Toff314 ∷ CS01 ∷ CS03 ∷ CCZ014 ∷ Toff214 ∷ K3 ∷ CS34 ∷ CX13 ∷ CCZ024 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ CS03⁻ ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b8 = at 3 2 (Toff213 ∷ CS01 ∷ []) (wl0193 (lit c4)) ▸
       at 2 2 (Toff213 ∷ Toff214 ∷ Toff314 ∷ []) (sym (wl0192 (lit c4))) ▸
       at 10 2 (CCZ024 ∷ CS03⁻ ∷ []) (sym (wp0032 c4)) ▸
       at 9 1 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (sym (wl0190 (lit c4))) ▸
       at 15 2 (CCZ024 ∷ K3⁻ ∷ []) (sym (wp0033 c4)) ▸
       at 14 2 (CCZ024 ∷ CS14 ∷ []) (sym (wp0034 c4)) ▸
       at 13 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 12 2 (CCZ024 ∷ CS34⁻ ∷ []) (sym (wp0035 c4)) ▸ done

  b9 : Chain (Bx2-0413 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ Toff314 ∷ CS01 ∷ CS03 ∷ CCZ014 ∷ Toff214 ∷ K3 ∷ CS34 ∷ CX13 ∷ CCZ024 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ CS03⁻ ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ Toff314 ∷ CCZ024 ∷ CS01 ∷ CS03 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b9 = at 11 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 10 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 9 2 (CCZ024 ∷ K3 ∷ []) (sym (wp0037 c4)) ▸
       at 10 7 (Toff314 ∷ []) (wl0190 (lit c4)) ▸
       at 8 2 (CCZ024 ∷ Toff214 ∷ CCZ014 ∷ []) (sym (wp0042 c4)) ▸
       at 7 2 (CCZ024 ∷ CCZ014 ∷ []) (wp0038 c4) ▸
       at 6 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸
       at 5 2 (CCZ024 ∷ CS01 ∷ []) (sym (wp0039 c4)) ▸ done

  b10 : Chain (Bx2-0413 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ Toff314 ∷ CCZ024 ∷ CS01 ∷ CS03 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ CCZ024 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ CS01 ∷ CS03 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b10 = at 4 1 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (sym (wl0190 (lit c4))) ▸
       at 10 2 (CCZ024 ∷ K3⁻ ∷ []) (sym (wp0033 c4)) ▸
       at 9 2 (CCZ024 ∷ CS14 ∷ []) (sym (wp0034 c4)) ▸
       at 8 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 7 2 (CCZ024 ∷ CS34⁻ ∷ []) (sym (wp0035 c4)) ▸
       at 6 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 4 2 (CCZ024 ∷ K3 ∷ []) (sym (wp0037 c4)) ▸ done

  b11 : Chain (Bx2-0413 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ CCZ024 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ CS01 ∷ CS03 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ Toff213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff214 ∷ Toff314 ∷ CS01 ∷ CS03 ∷ Toff214 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ Toff213 ∷ CX04 ∷ CS01 ∷ Toff214 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b11 = at 5 7 (Toff314 ∷ []) (wl0190 (lit c4)) ▸
       at 3 2 (CCZ024 ∷ Toff214 ∷ CCZ014 ∷ []) (sym (wp0042 c4)) ▸
       at 5 5 (Toff314 ∷ CS01 ∷ CS03 ∷ []) (wp0043 c4) ▸
       at 11 2 (Toff213 ∷ CS03⁻ ∷ []) (wl0191 (lit c4)) ▸
       at 10 2 (Toff213 ∷ Toff214 ∷ Toff314 ∷ []) (sym (wl0192 (lit c4))) ▸
       at 9 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4) ▸
       at 13 2 (Toff213 ∷ CS01 ∷ []) (wl0193 (lit c4)) ▸
       at 12 2 (Toff213 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF213 (lit c4)) ▸ done

  b12 : Chain (Bx2-0413 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff214 ∷ Toff314 ∷ CS01 ∷ CS03 ∷ Toff214 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ Toff213 ∷ CX04 ∷ CS01 ∷ Toff214 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Bx2-0413 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff214 ∷ Toff213 ∷ Toff214 ∷ Toff314 ∷ CS01 ∷ CS03 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b12 = at 11 2 (Toff213 ∷ CS14⁻ ∷ []) (wl0194 (lit c4)) ▸
       at 10 2 (Toff213 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF213 (lit c4)) ▸
       at 9 2 (Toff213 ∷ CS14 ∷ []) (wl0195 (lit c4)) ▸
       at 10 5 (CCZ014 ∷ []) (sym (wp0041 c4)) ▸
       at 8 2 (Toff213 ∷ Toff214 ∷ []) (sym (wl0197 (lit c4))) ▸
       at 7 2 (Toff213 ∷ CS03 ∷ []) (wl0196 (lit c4)) ▸
       at 6 2 (Toff213 ∷ CS01 ∷ []) (wl0193 (lit c4)) ▸
       at 5 2 (Toff213 ∷ Toff214 ∷ Toff314 ∷ []) (sym (wl0192 (lit c4))) ▸ done

  b13 : Chain (Bx2-0413 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff214 ∷ Toff213 ∷ Toff214 ∷ Toff314 ∷ CS01 ∷ CS03 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (CS01 ∷ [])
  b13 = at 4 2 (Toff213 ∷ Toff214 ∷ []) (sym (wl0197 (lit c4))) ▸
       at 5 3 (Toff314 ∷ []) (wl0198 (lit c4)) ▸
       at 8 3 (CCZ014 ∷ []) (sym (wp0044 c4)) ▸
       at 1 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 0 2 [] (lem-box2-at0210243143 c4) ▸
       at 7 1 (CS03 ∷ []) (refl) ▸
       at 9 1 (CS03⁻ ∷ []) (refl) ▸
       at 0 10 (CS01 ∷ []) (sym (wp0045 c4)) ▸ done

-- F5-12: 112 steps
lem-F5-12 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ []) ⟫ʷ
lem-F5-12 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (run b13)))))))))))))
  where
  b0 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (X4 ∷ Bx0-1423 ∷ Toff324 ∷ X4 ∷ CX23 ∷ CS12 ∷ CCZ123 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b0 = at 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 5 2 (X4 ∷ Sb⁻0-1-3-2 ∷ []) (c₄ (Swap ↑ ↑ • ((CS • CS • CS) ↑) • Swap ↑ ↑) (X)) ▸
       at 4 2 (X4 ∷ CX23 ∷ Toff324 ∷ []) (wl0211 (lit c4)) ▸
       at 3 2 (X4 ∷ Sb0-1-3-2 ∷ []) (c₄ (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) (X)) ▸
       at 4 1 (CS13 ∷ []) (refl) ▸
       at 4 2 (CX23 ∷ CS12 ∷ CCZ123 ∷ CS13 ∷ []) (wl0212 (lit c4)) ▸
       at 7 1 (Sb0-1-3-2 ∷ []) (refl) ▸ done

  b1 : Chain (X4 ∷ Bx0-1423 ∷ Toff324 ∷ X4 ∷ CX23 ∷ CS12 ∷ CCZ123 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ CCZ123 ∷ CS12 ∷ CCZ123 ∷ CCZ124 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ CS13⁻ ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b1 = at 2 2 (X4 ∷ CX23 ∷ Toff324 ∷ []) (wl0211 (lit c4)) ▸
       at 4 2 (CX23 ∷ Toff324 ∷ []) (sym (wl0213 (lit c4))) ▸
       at 5 2 (CS12 ∷ Toff324 ∷ []) (sym (wl0214 (lit c4))) ▸
       at 6 2 (CCZ123 ∷ CCZ124 ∷ Toff324 ∷ []) (sym (wl0215 (lit c4))) ▸
       at 2 6 (X4 ∷ CS12 ∷ CCZ123 ∷ CCZ124 ∷ []) (sym (wl0216 (lit c4))) ▸
       at 0 3 (Bx0-1423 ∷ CCZ123 ∷ []) (lem-Xb-box-at243243 c4) ▸
       at 9 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 8 1 (CS13⁻ ∷ []) (refl) ▸ done

  b2 : Chain (Bx0-1423 ∷ CCZ123 ∷ CS12 ∷ CCZ123 ∷ CCZ124 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ CS13⁻ ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ CCZ123 ∷ CS12 ∷ CCZ123 ∷ CCZ124 ∷ Toff324 ∷ Sb0-1-3-2 ∷ K3 ∷ CCZ014 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ CS13⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b2 = at 8 2 (CCZ014 ∷ CS13⁻ ∷ []) (sym (wp0060 c4)) ▸
       at 7 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 13 2 (CCZ014 ∷ K3⁻ ∷ []) (sym (wp0061 c4)) ▸
       at 12 2 (CCZ014 ∷ CS24 ∷ []) (sym (wp0062 c4)) ▸
       at 11 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸
       at 10 2 (CCZ014 ∷ CS34⁻ ∷ []) (sym (wp0063 c4)) ▸
       at 9 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸
       at 8 2 (CCZ014 ∷ CS34 ∷ []) (sym (wp0064 c4)) ▸ done

  b3 : Chain (Bx0-1423 ∷ CCZ123 ∷ CS12 ∷ CCZ123 ∷ CCZ124 ∷ Toff324 ∷ Sb0-1-3-2 ∷ K3 ∷ CCZ014 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ CS13⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ CCZ123 ∷ CS12 ∷ CCZ123 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CCZ014 ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b3 = at 7 2 (CCZ014 ∷ K3 ∷ []) (sym (wp0065 c4)) ▸
       at 8 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 6 1 (CS13 ∷ []) (refl) ▸
       at 6 2 (CCZ014 ∷ CS13 ∷ []) (sym (wp0053 c4)) ▸
       at 5 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 11 2 (CCZ014 ∷ K3⁻ ∷ []) (sym (wp0061 c4)) ▸
       at 10 2 (CCZ014 ∷ CS24 ∷ []) (sym (wp0062 c4)) ▸
       at 9 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸ done

  b4 : Chain (Bx0-1423 ∷ CCZ123 ∷ CS12 ∷ CCZ123 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CCZ014 ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ CCZ123 ∷ CS12 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CCZ014 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b4 = at 8 2 (CCZ014 ∷ CS34⁻ ∷ []) (sym (wp0063 c4)) ▸
       at 7 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸
       at 6 2 (CCZ014 ∷ CS34 ∷ []) (sym (wp0064 c4)) ▸
       at 5 2 (CCZ014 ∷ K3 ∷ []) (sym (wp0065 c4)) ▸
       at 6 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 4 2 (CCZ014 ∷ CCZ124 ∷ []) (sym (wp0066 c4)) ▸
       at 3 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0207 (lit c4)) ▸
       at 7 2 (CCZ014 ∷ CS13 ∷ []) (sym (wp0053 c4)) ▸ done

  b5 : Chain (Bx0-1423 ∷ CCZ123 ∷ CS12 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CCZ014 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CCZ014 ∷ CS13 ∷ CS12 ∷ CCZ123 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b5 = at 6 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸
       at 5 2 (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 (lit c4)) ▸
       at 4 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸
       at 3 2 (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 (lit c4)) ▸
       at 4 5 (CCZ123 ∷ []) (sym (wl0207 (lit c4))) ▸
       at 2 2 (CCZ014 ∷ CS12 ∷ []) (sym (wp0067 c4)) ▸
       at 1 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0207 (lit c4)) ▸
       at 5 2 (CCZ014 ∷ CS13 ∷ []) (sym (wp0053 c4)) ▸ done

  b6 : Chain (Bx0-1423 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CCZ014 ∷ CS13 ∷ CS12 ∷ CCZ123 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ CCZ014 ∷ Toff324 ∷ CS12 ∷ CS13 ∷ CCZ124 ∷ Toff023 ∷ Toff024 ∷ Toff324 ∷ CS13⁻ ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b6 = at 4 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸
       at 3 2 (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 (lit c4)) ▸
       at 2 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸
       at 1 2 (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 (lit c4)) ▸
       at 2 5 (CCZ123 ∷ []) (sym (wl0207 (lit c4))) ▸
       at 2 6 (Toff324 ∷ CS12 ∷ CS13 ∷ CCZ124 ∷ []) (wl0218 (lit c4)) ▸
       at 7 2 (Toff023 ∷ CS13⁻ ∷ []) (wl0219 (lit c4)) ▸
       at 6 2 (Toff023 ∷ Toff024 ∷ Toff324 ∷ []) (sym (wp0068 c4)) ▸ done

  b7 : Chain (Bx0-1423 ∷ CCZ014 ∷ Toff324 ∷ CS12 ∷ CS13 ∷ CCZ124 ∷ Toff023 ∷ Toff024 ∷ Toff324 ∷ CS13⁻ ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ CCZ014 ∷ Toff324 ∷ CS12 ∷ Toff023 ∷ CS13 ∷ CCZ124 ∷ Toff024 ∷ Toff324 ∷ CS13⁻ ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b7 = at 5 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 9 2 (Toff023 ∷ CS12 ∷ []) (wl0221 (lit c4)) ▸
       at 8 2 (Toff023 ∷ CX14 ∷ []) (lem-comm-CX14-TOFF023 (lit c4)) ▸
       at 7 2 (Toff023 ∷ CS24⁻ ∷ []) (wp0069 c4) ▸
       at 6 2 (Toff023 ∷ CX14 ∷ []) (lem-comm-CX14-TOFF023 (lit c4)) ▸
       at 5 2 (Toff023 ∷ CS24 ∷ []) (wp0070 c4) ▸
       at 6 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 4 2 (Toff023 ∷ CS13 ∷ []) (wl0222 (lit c4)) ▸ done

  b8 : Chain (Bx0-1423 ∷ CCZ014 ∷ Toff324 ∷ CS12 ∷ Toff023 ∷ CS13 ∷ CCZ124 ∷ Toff024 ∷ Toff324 ∷ CS13⁻ ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ Toff324 ∷ CS12 ∷ CS13 ∷ CCZ124 ∷ Toff024 ∷ K3 ∷ CS34 ∷ CX23 ∷ CCZ014 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ CS13⁻ ∷ Toff023 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b8 = at 3 2 (Toff023 ∷ CS12 ∷ []) (wl0221 (lit c4)) ▸
       at 2 2 (Toff023 ∷ Toff024 ∷ Toff324 ∷ []) (sym (wp0068 c4)) ▸
       at 10 2 (CCZ014 ∷ CS13⁻ ∷ []) (sym (wp0060 c4)) ▸
       at 9 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 15 2 (CCZ014 ∷ K3⁻ ∷ []) (sym (wp0061 c4)) ▸
       at 14 2 (CCZ014 ∷ CS24 ∷ []) (sym (wp0062 c4)) ▸
       at 13 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸
       at 12 2 (CCZ014 ∷ CS34⁻ ∷ []) (sym (wp0063 c4)) ▸ done

  b9 : Chain (Bx0-1423 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ Toff324 ∷ CS12 ∷ CS13 ∷ CCZ124 ∷ Toff024 ∷ K3 ∷ CS34 ∷ CX23 ∷ CCZ014 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ CS13⁻ ∷ Toff023 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ Toff324 ∷ CCZ014 ∷ CS12 ∷ CS13 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ Toff023 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b9 = at 11 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸
       at 10 2 (CCZ014 ∷ CS34 ∷ []) (sym (wp0064 c4)) ▸
       at 9 2 (CCZ014 ∷ K3 ∷ []) (sym (wp0065 c4)) ▸
       at 10 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 8 2 (CCZ014 ∷ Toff024 ∷ CCZ124 ∷ []) (sym (wp0071 c4)) ▸
       at 7 2 (CCZ014 ∷ CCZ124 ∷ []) (sym (wp0066 c4)) ▸
       at 6 2 (CCZ014 ∷ CS13 ∷ []) (sym (wp0053 c4)) ▸
       at 5 2 (CCZ014 ∷ CS12 ∷ []) (sym (wp0067 c4)) ▸ done

  b10 : Chain (Bx0-1423 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ Toff324 ∷ CCZ014 ∷ CS12 ∷ CS13 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ Toff023 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ014 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ CS12 ∷ CS13 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ Toff023 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b10 = at 4 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 10 2 (CCZ014 ∷ K3⁻ ∷ []) (sym (wp0061 c4)) ▸
       at 9 2 (CCZ014 ∷ CS24 ∷ []) (sym (wp0062 c4)) ▸
       at 8 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸
       at 7 2 (CCZ014 ∷ CS34⁻ ∷ []) (sym (wp0063 c4)) ▸
       at 6 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸
       at 5 2 (CCZ014 ∷ CS34 ∷ []) (sym (wp0064 c4)) ▸
       at 4 2 (CCZ014 ∷ K3 ∷ []) (sym (wp0065 c4)) ▸ done

  b11 : Chain (Bx0-1423 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ014 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ CS12 ∷ CS13 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ Toff023 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff024 ∷ Toff324 ∷ CS12 ∷ CS13 ∷ Toff024 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ Toff023 ∷ CX14 ∷ CS12 ∷ Toff024 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b11 = at 5 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 3 2 (CCZ014 ∷ Toff024 ∷ CCZ124 ∷ []) (sym (wp0071 c4)) ▸
       at 5 5 (Toff324 ∷ CS12 ∷ CS13 ∷ []) (wl0223 (lit c4)) ▸
       at 11 2 (Toff023 ∷ CS13⁻ ∷ []) (wl0219 (lit c4)) ▸
       at 10 2 (Toff023 ∷ Toff024 ∷ Toff324 ∷ []) (sym (wp0068 c4)) ▸
       at 9 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 13 2 (Toff023 ∷ CS12 ∷ []) (wl0221 (lit c4)) ▸
       at 12 2 (Toff023 ∷ CX14 ∷ []) (lem-comm-CX14-TOFF023 (lit c4)) ▸ done

  b12 : Chain (Bx0-1423 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff024 ∷ Toff324 ∷ CS12 ∷ CS13 ∷ Toff024 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ Toff023 ∷ CX14 ∷ CS12 ∷ Toff024 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (Bx0-1423 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff024 ∷ Toff023 ∷ Toff024 ∷ Toff324 ∷ CS12 ∷ CS13 ∷ Toff024 ∷ CCZ124 ∷ Toff024 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ [])
  b12 = at 11 2 (Toff023 ∷ CS24⁻ ∷ []) (wp0069 c4) ▸
       at 10 2 (Toff023 ∷ CX14 ∷ []) (lem-comm-CX14-TOFF023 (lit c4)) ▸
       at 9 2 (Toff023 ∷ CS24 ∷ []) (wp0070 c4) ▸
       at 10 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 8 2 (Toff023 ∷ Toff024 ∷ []) (sym (wp0072 c4)) ▸
       at 7 2 (Toff023 ∷ CS13 ∷ []) (wl0222 (lit c4)) ▸
       at 6 2 (Toff023 ∷ CS12 ∷ []) (wl0221 (lit c4)) ▸
       at 5 2 (Toff023 ∷ Toff024 ∷ Toff324 ∷ []) (sym (wp0068 c4)) ▸ done

  b13 : Chain (Bx0-1423 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff024 ∷ Toff023 ∷ Toff024 ∷ Toff324 ∷ CS12 ∷ CS13 ∷ Toff024 ∷ CCZ124 ∷ Toff024 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (CS12 ∷ [])
  b13 = at 4 2 (Toff023 ∷ Toff024 ∷ []) (sym (wp0072 c4)) ▸
       at 5 3 (Toff324 ∷ []) (wp0073 c4) ▸
       at 8 3 (CCZ124 ∷ []) (sym (wp0074 c4)) ▸
       at 1 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 0 2 [] (lem-box2-at243243 c4) ▸
       at 7 1 (CS13 ∷ []) (refl) ▸
       at 9 1 (CS13⁻ ∷ []) (refl) ▸
       at 0 10 (CS12 ∷ []) (sym (wl0224 (lit c4))) ▸ done

-- F5-23: 112 steps
lem-F5-23 : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ []) ⟫ʷ
lem-F5-23 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (run b13)))))))))))))
  where
  b0 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (X4 ∷ Bx0-2431 ∷ Toff134 ∷ X4 ∷ CX31 ∷ CS23 ∷ CCZ123 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b0 = at 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 5 2 (X4 ∷ Sb⁻0-2-1-3 ∷ []) (c₃ ((CS • CS • CS) ↑) (X ↑)) ▸
       at 4 2 (X4 ∷ CX31 ∷ Toff134 ∷ []) (wl0235 (lit c4)) ▸
       at 3 2 (X4 ∷ Sb0-2-1-3 ∷ []) (c₃ (CS ↑) (X ↑)) ▸
       at 4 1 (CS12 ∷ []) (refl) ▸
       at 4 2 (CX31 ∷ CS23 ∷ CCZ123 ∷ CS12 ∷ []) (wl0236 (lit c4)) ▸
       at 7 1 (Sb0-2-1-3 ∷ []) (refl) ▸ done

  b1 : Chain (X4 ∷ Bx0-2431 ∷ Toff134 ∷ X4 ∷ CX31 ∷ CS23 ∷ CCZ123 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ CCZ123 ∷ CS23 ∷ CCZ123 ∷ CCZ234 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ CS12⁻ ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b1 = at 2 2 (X4 ∷ CX31 ∷ Toff134 ∷ []) (wl0235 (lit c4)) ▸
       at 4 2 (CX31 ∷ Toff134 ∷ []) (sym (wl0237 (lit c4))) ▸
       at 5 2 (CS23 ∷ Toff134 ∷ []) (sym (wl0238 (lit c4))) ▸
       at 6 2 (CCZ123 ∷ CCZ234 ∷ Toff134 ∷ []) (sym (wl0239 (lit c4))) ▸
       at 2 6 (X4 ∷ CS23 ∷ CCZ123 ∷ CCZ234 ∷ []) (sym (wl0240 (lit c4))) ▸
       at 0 3 (Bx0-2431 ∷ CCZ123 ∷ []) (lem-Xb-box-at122441 c4) ▸
       at 9 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 8 1 (CS12⁻ ∷ []) (refl) ▸ done

  b2 : Chain (Bx0-2431 ∷ CCZ123 ∷ CS23 ∷ CCZ123 ∷ CCZ234 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ CS12⁻ ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ CCZ123 ∷ CS23 ∷ CCZ123 ∷ CCZ234 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CCZ024 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ CS12⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b2 = at 8 2 (CCZ024 ∷ CS12⁻ ∷ []) (sym (wp0087 c4)) ▸
       at 7 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 13 2 (CCZ024 ∷ K1⁻ ∷ []) (sym (wp0088 c4)) ▸
       at 12 2 (CCZ024 ∷ CS14 ∷ []) (sym (wp0034 c4)) ▸
       at 11 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 10 2 (CCZ024 ∷ CS34⁻ ∷ []) (sym (wp0035 c4)) ▸
       at 9 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 8 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸ done

  b3 : Chain (Bx0-2431 ∷ CCZ123 ∷ CS23 ∷ CCZ123 ∷ CCZ234 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CCZ024 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ CS12⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ CCZ123 ∷ CS23 ∷ CCZ123 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CCZ024 ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b3 = at 7 2 (CCZ024 ∷ K1 ∷ []) (sym (wp0089 c4)) ▸
       at 8 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 6 1 (CS12 ∷ []) (refl) ▸
       at 6 2 (CCZ024 ∷ CS12 ∷ []) (sym (wp0081 c4)) ▸
       at 5 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 11 2 (CCZ024 ∷ K1⁻ ∷ []) (sym (wp0088 c4)) ▸
       at 10 2 (CCZ024 ∷ CS14 ∷ []) (sym (wp0034 c4)) ▸
       at 9 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸ done

  b4 : Chain (Bx0-2431 ∷ CCZ123 ∷ CS23 ∷ CCZ123 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CCZ024 ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ CCZ123 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CCZ024 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b4 = at 8 2 (CCZ024 ∷ CS34⁻ ∷ []) (sym (wp0035 c4)) ▸
       at 7 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 6 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 5 2 (CCZ024 ∷ K1 ∷ []) (sym (wp0089 c4)) ▸
       at 6 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ CCZ234 ∷ []) (sym (wp0090 c4)) ▸
       at 3 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0242 (lit c4)) ▸
       at 7 2 (CCZ024 ∷ CS12 ∷ []) (sym (wp0081 c4)) ▸ done

  b5 : Chain (Bx0-2431 ∷ CCZ123 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CCZ024 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CCZ024 ∷ CS12 ∷ CS23 ∷ CCZ123 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b5 = at 6 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ CS23⁻ ∷ []) (sym (wp0091 c4)) ▸
       at 4 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 3 2 (CCZ024 ∷ CS23 ∷ []) (sym (wp0092 c4)) ▸
       at 4 5 (CCZ123 ∷ []) (sym (wl0242 (lit c4))) ▸
       at 2 2 (CCZ024 ∷ CS23 ∷ []) (sym (wp0092 c4)) ▸
       at 1 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0242 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ CS12 ∷ []) (sym (wp0081 c4)) ▸ done

  b6 : Chain (Bx0-2431 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CCZ024 ∷ CS12 ∷ CS23 ∷ CCZ123 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ CCZ024 ∷ Toff134 ∷ CS12 ∷ CS23 ∷ CCZ234 ∷ Toff013 ∷ Toff034 ∷ Toff134 ∷ CS12⁻ ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b6 = at 4 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 3 2 (CCZ024 ∷ CS23⁻ ∷ []) (sym (wp0091 c4)) ▸
       at 2 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 1 2 (CCZ024 ∷ CS23 ∷ []) (sym (wp0092 c4)) ▸
       at 2 5 (CCZ123 ∷ []) (sym (wl0242 (lit c4))) ▸
       at 2 6 (Toff134 ∷ CS12 ∷ CS23 ∷ CCZ234 ∷ []) (wl0243 (lit c4)) ▸
       at 7 2 (Toff013 ∷ CS12⁻ ∷ []) (wl0244 (lit c4)) ▸
       at 6 2 (Toff013 ∷ Toff034 ∷ Toff134 ∷ []) (sym (wp0093 c4)) ▸ done

  b7 : Chain (Bx0-2431 ∷ CCZ024 ∷ Toff134 ∷ CS12 ∷ CS23 ∷ CCZ234 ∷ Toff013 ∷ Toff034 ∷ Toff134 ∷ CS12⁻ ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ CCZ024 ∷ Toff134 ∷ CS12 ∷ Toff013 ∷ CS23 ∷ CCZ234 ∷ Toff034 ∷ Toff134 ∷ CS12⁻ ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b7 = at 5 1 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (wl0245 (lit c4)) ▸
       at 9 2 (Toff013 ∷ CS23 ∷ []) (wl0246 (lit c4)) ▸
       at 8 2 (Toff013 ∷ CX24 ∷ []) (lem-comm-CX24-TOFF013 (lit c4)) ▸
       at 7 2 (Toff013 ∷ CS34⁻ ∷ []) (wp0094 c4) ▸
       at 6 2 (Toff013 ∷ CX24 ∷ []) (lem-comm-CX24-TOFF013 (lit c4)) ▸
       at 5 2 (Toff013 ∷ CS34 ∷ []) (wp0095 c4) ▸
       at 6 5 (CCZ234 ∷ []) (sym (wl0245 (lit c4))) ▸
       at 4 2 (Toff013 ∷ CS23 ∷ []) (wl0246 (lit c4)) ▸ done

  b8 : Chain (Bx0-2431 ∷ CCZ024 ∷ Toff134 ∷ CS12 ∷ Toff013 ∷ CS23 ∷ CCZ234 ∷ Toff034 ∷ Toff134 ∷ CS12⁻ ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ Toff134 ∷ CS12 ∷ CS23 ∷ CCZ234 ∷ Toff034 ∷ K1 ∷ CS34 ∷ CX13 ∷ CCZ024 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ CS12⁻ ∷ Toff013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b8 = at 3 2 (Toff013 ∷ CS12 ∷ []) (wl0247 (lit c4)) ▸
       at 2 2 (Toff013 ∷ Toff034 ∷ Toff134 ∷ []) (sym (wp0093 c4)) ▸
       at 10 2 (CCZ024 ∷ CS12⁻ ∷ []) (sym (wp0087 c4)) ▸
       at 9 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 15 2 (CCZ024 ∷ K1⁻ ∷ []) (sym (wp0088 c4)) ▸
       at 14 2 (CCZ024 ∷ CS14 ∷ []) (sym (wp0034 c4)) ▸
       at 13 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 12 2 (CCZ024 ∷ CS34⁻ ∷ []) (sym (wp0035 c4)) ▸ done

  b9 : Chain (Bx0-2431 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ Toff134 ∷ CS12 ∷ CS23 ∷ CCZ234 ∷ Toff034 ∷ K1 ∷ CS34 ∷ CX13 ∷ CCZ024 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ CS12⁻ ∷ Toff013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ Toff134 ∷ CCZ024 ∷ CS12 ∷ CS23 ∷ CCZ234 ∷ Toff034 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b9 = at 11 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 10 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 9 2 (CCZ024 ∷ K1 ∷ []) (sym (wp0089 c4)) ▸
       at 10 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 8 2 (CCZ024 ∷ Toff034 ∷ CCZ234 ∷ []) (sym (wp0096 c4)) ▸
       at 7 2 (CCZ024 ∷ CCZ234 ∷ []) (sym (wp0090 c4)) ▸
       at 6 2 (CCZ024 ∷ CS23 ∷ []) (sym (wp0092 c4)) ▸
       at 5 2 (CCZ024 ∷ CS12 ∷ []) (sym (wp0081 c4)) ▸ done

  b10 : Chain (Bx0-2431 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ Toff134 ∷ CCZ024 ∷ CS12 ∷ CS23 ∷ CCZ234 ∷ Toff034 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ024 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ CS12 ∷ CS23 ∷ CCZ234 ∷ Toff034 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b10 = at 4 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 10 2 (CCZ024 ∷ K1⁻ ∷ []) (sym (wp0088 c4)) ▸
       at 9 2 (CCZ024 ∷ CS14 ∷ []) (sym (wp0034 c4)) ▸
       at 8 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 7 2 (CCZ024 ∷ CS34⁻ ∷ []) (sym (wp0035 c4)) ▸
       at 6 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 4 2 (CCZ024 ∷ K1 ∷ []) (sym (wp0089 c4)) ▸ done

  b11 : Chain (Bx0-2431 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ024 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ CS12 ∷ CS23 ∷ CCZ234 ∷ Toff034 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff013 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff034 ∷ Toff134 ∷ CS12 ∷ CS23 ∷ Toff034 ∷ CS34 ∷ CX24 ∷ CS34⁻ ∷ Toff013 ∷ CX24 ∷ CS23 ∷ Toff034 ∷ Toff134 ∷ CS12⁻ ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b11 = at 5 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 3 2 (CCZ024 ∷ Toff034 ∷ CCZ234 ∷ []) (sym (wp0096 c4)) ▸
       at 5 5 (Toff134 ∷ CS12 ∷ CS23 ∷ []) (wl0248 (lit c4)) ▸
       at 11 2 (Toff013 ∷ CS12⁻ ∷ []) (wl0244 (lit c4)) ▸
       at 10 2 (Toff013 ∷ Toff034 ∷ Toff134 ∷ []) (sym (wp0093 c4)) ▸
       at 9 1 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (wl0245 (lit c4)) ▸
       at 13 2 (Toff013 ∷ CS23 ∷ []) (wl0246 (lit c4)) ▸
       at 12 2 (Toff013 ∷ CX24 ∷ []) (lem-comm-CX24-TOFF013 (lit c4)) ▸ done

  b12 : Chain (Bx0-2431 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff034 ∷ Toff134 ∷ CS12 ∷ CS23 ∷ Toff034 ∷ CS34 ∷ CX24 ∷ CS34⁻ ∷ Toff013 ∷ CX24 ∷ CS23 ∷ Toff034 ∷ Toff134 ∷ CS12⁻ ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (Bx0-2431 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff034 ∷ Toff013 ∷ Toff034 ∷ Toff134 ∷ CS12 ∷ CS23 ∷ Toff034 ∷ CCZ234 ∷ Toff034 ∷ Toff134 ∷ CS12⁻ ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b12 = at 11 2 (Toff013 ∷ CS34⁻ ∷ []) (wp0094 c4) ▸
       at 10 2 (Toff013 ∷ CX24 ∷ []) (lem-comm-CX24-TOFF013 (lit c4)) ▸
       at 9 2 (Toff013 ∷ CS34 ∷ []) (wp0095 c4) ▸
       at 10 5 (CCZ234 ∷ []) (sym (wl0245 (lit c4))) ▸
       at 8 2 (Toff013 ∷ Toff034 ∷ []) (sym (wp0097 c4)) ▸
       at 7 2 (Toff013 ∷ CS23 ∷ []) (wl0246 (lit c4)) ▸
       at 6 2 (Toff013 ∷ CS12 ∷ []) (wl0247 (lit c4)) ▸
       at 5 2 (Toff013 ∷ Toff034 ∷ Toff134 ∷ []) (sym (wp0093 c4)) ▸ done

  b13 : Chain (Bx0-2431 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff034 ∷ Toff013 ∷ Toff034 ∷ Toff134 ∷ CS12 ∷ CS23 ∷ Toff034 ∷ CCZ234 ∷ Toff034 ∷ Toff134 ∷ CS12⁻ ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (CS23 ∷ [])
  b13 = at 4 2 (Toff013 ∷ Toff034 ∷ []) (sym (wp0097 c4)) ▸
       at 9 4 (CS23 ∷ CCZ234 ∷ []) (sym (wp0098 c4)) ▸
       at 5 3 (Toff134 ∷ []) (wp0099 c4) ▸
       at 1 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 0 2 [] (lem-box2-at122441 c4) ▸
       at 7 1 (CS12 ∷ []) (refl) ▸
       at 9 1 (CS12⁻ ∷ []) (refl) ▸
       at 0 10 (CS23 ∷ []) (sym (wl0249 (lit c4))) ▸ done

-- box-perm-3412: 1 steps
lem-box-perm-3412 : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3412 ∷ []) ⟫ʷ
lem-box-perm-3412 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ []) (Bx0-3412 ∷ [])
  b0 = at 0 1 (Bx0-3412 ∷ []) (lem-pairs c4) ▸ done

-- box-perm-3421: 2 steps
lem-box-perm-3421 : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3421 ∷ []) ⟫ʷ
lem-box-perm-3421 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ []) (Bx0-3421 ∷ [])
  b0 = at 0 1 (Bx0-2134 ∷ []) (lem-sym-ab c4) ▸
       at 0 1 (Bx0-3421 ∷ []) (lem-pairs-at1221 c4) ▸ done

-- box-perm-2413: 2 steps
lem-box-perm-2413 : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2413 ∷ []) ⟫ʷ
lem-box-perm-2413 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ []) (Bx0-2413 ∷ [])
  b0 = at 0 1 (Bx0-1324 ∷ []) (lem-sym-bc c4) ▸
       at 0 1 (Bx0-2413 ∷ []) (lem-pairs-at2332 c4) ▸ done

-- box-perm-4312: 2 steps
lem-box-perm-4312 : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4312 ∷ []) ⟫ʷ
lem-box-perm-4312 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ []) (Bx0-4312 ∷ [])
  b0 = at 0 1 (Bx0-3412 ∷ []) (lem-pairs c4) ▸
       at 0 1 (Bx0-4312 ∷ []) (lem-sym-ab-at13243142 c4) ▸ done

-- box-perm-3142: 2 steps
lem-box-perm-3142 : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3142 ∷ []) ⟫ʷ
lem-box-perm-3142 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ []) (Bx0-3142 ∷ [])
  b0 = at 0 1 (Bx0-3412 ∷ []) (lem-pairs c4) ▸
       at 0 1 (Bx0-3142 ∷ []) (lem-sym-bc-at13243142 c4) ▸ done

-- box-perm-1423: 3 steps
lem-box-perm-1423 : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ []) ⟫ʷ
lem-box-perm-1423 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ []) (Bx0-1423 ∷ [])
  b0 = at 0 1 (Bx0-2134 ∷ []) (lem-sym-ab c4) ▸
       at 0 1 (Bx0-2314 ∷ []) (lem-sym-bc-at1221 c4) ▸
       at 0 1 (Bx0-1423 ∷ []) (lem-pairs-at122331 c4) ▸ done

-- box-perm-4321: 3 steps
lem-box-perm-4321 : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4321 ∷ []) ⟫ʷ
lem-box-perm-4321 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ []) (Bx0-4321 ∷ [])
  b0 = at 0 1 (Bx0-2134 ∷ []) (lem-sym-ab c4) ▸
       at 0 1 (Bx0-3421 ∷ []) (lem-pairs-at1221 c4) ▸
       at 0 1 (Bx0-4321 ∷ []) (lem-sym-ab-at13243241 c4) ▸ done

-- box-perm-3241: 3 steps
lem-box-perm-3241 : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3241 ∷ []) ⟫ʷ
lem-box-perm-3241 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ []) (Bx0-3241 ∷ [])
  b0 = at 0 1 (Bx0-2134 ∷ []) (lem-sym-ab c4) ▸
       at 0 1 (Bx0-3421 ∷ []) (lem-pairs-at1221 c4) ▸
       at 0 1 (Bx0-3241 ∷ []) (lem-sym-bc-at13243241 c4) ▸ done

-- box-perm-2431: 3 steps
lem-box-perm-2431 : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ []) ⟫ʷ
lem-box-perm-2431 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ []) (Bx0-2431 ∷ [])
  b0 = at 0 1 (Bx0-1324 ∷ []) (lem-sym-bc c4) ▸
       at 0 1 (Bx0-3124 ∷ []) (lem-sym-ab-at2332 c4) ▸
       at 0 1 (Bx0-2431 ∷ []) (lem-pairs-at132132 c4) ▸ done

-- box-perm-4213: 3 steps
lem-box-perm-4213 : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4213 ∷ []) ⟫ʷ
lem-box-perm-4213 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ []) (Bx0-4213 ∷ [])
  b0 = at 0 1 (Bx0-1324 ∷ []) (lem-sym-bc c4) ▸
       at 0 1 (Bx0-2413 ∷ []) (lem-pairs-at2332 c4) ▸
       at 0 1 (Bx0-4213 ∷ []) (lem-sym-ab-at12243143 c4) ▸ done

-- box-perm-2143: 3 steps
lem-box-perm-2143 : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2143 ∷ []) ⟫ʷ
lem-box-perm-2143 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ []) (Bx0-2143 ∷ [])
  b0 = at 0 1 (Bx0-1324 ∷ []) (lem-sym-bc c4) ▸
       at 0 1 (Bx0-2413 ∷ []) (lem-pairs-at2332 c4) ▸
       at 0 1 (Bx0-2143 ∷ []) (lem-sym-bc-at12243143 c4) ▸ done

-- box-perm-4132: 3 steps
lem-box-perm-4132 : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4132 ∷ []) ⟫ʷ
lem-box-perm-4132 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ []) (Bx0-4132 ∷ [])
  b0 = at 0 1 (Bx0-3412 ∷ []) (lem-pairs c4) ▸
       at 0 1 (Bx0-4312 ∷ []) (lem-sym-ab-at13243142 c4) ▸
       at 0 1 (Bx0-4132 ∷ []) (lem-sym-bc-at14233142 c4) ▸ done

-- box-perm-1243: 3 steps
lem-box-perm-1243 : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1243 ∷ []) ⟫ʷ
lem-box-perm-1243 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ []) (Bx0-1243 ∷ [])
  b0 = at 0 1 (Bx0-3412 ∷ []) (lem-pairs c4) ▸
       at 0 1 (Bx0-4312 ∷ []) (lem-sym-ab-at13243142 c4) ▸
       at 0 1 (Bx0-1243 ∷ []) (lem-pairs-at14233142 c4) ▸ done

-- box-perm-1342: 3 steps
lem-box-perm-1342 : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1342 ∷ []) ⟫ʷ
lem-box-perm-1342 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ []) (Bx0-1342 ∷ [])
  b0 = at 0 1 (Bx0-3412 ∷ []) (lem-pairs c4) ▸
       at 0 1 (Bx0-3142 ∷ []) (lem-sym-bc-at13243142 c4) ▸
       at 0 1 (Bx0-1342 ∷ []) (lem-sym-ab-at13213442 c4) ▸ done

-- box-perm-4231: 3 steps
lem-box-perm-4231 : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4231 ∷ []) ⟫ʷ
lem-box-perm-4231 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ []) (Bx0-4231 ∷ [])
  b0 = at 0 1 (Bx0-3412 ∷ []) (lem-pairs c4) ▸
       at 0 1 (Bx0-3142 ∷ []) (lem-sym-bc-at13243142 c4) ▸
       at 0 1 (Bx0-4231 ∷ []) (lem-pairs-at13213442 c4) ▸ done

-- box-perm-1432: 4 steps
lem-box-perm-1432 : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1432 ∷ []) ⟫ʷ
lem-box-perm-1432 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ []) (Bx0-1432 ∷ [])
  b0 = at 0 1 (Bx0-2134 ∷ []) (lem-sym-ab c4) ▸
       at 0 1 (Bx0-2314 ∷ []) (lem-sym-bc-at1221 c4) ▸
       at 0 1 (Bx0-3214 ∷ []) (lem-sym-ab-at122331 c4) ▸
       at 0 1 (Bx0-1432 ∷ []) (lem-pairs-at1331 c4) ▸ done

-- box-perm-4123: 4 steps
lem-box-perm-4123 : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4123 ∷ []) ⟫ʷ
lem-box-perm-4123 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ []) (Bx0-4123 ∷ [])
  b0 = at 0 1 (Bx0-2134 ∷ []) (lem-sym-ab c4) ▸
       at 0 1 (Bx0-2314 ∷ []) (lem-sym-bc-at1221 c4) ▸
       at 0 1 (Bx0-1423 ∷ []) (lem-pairs-at122331 c4) ▸
       at 0 1 (Bx0-4123 ∷ []) (lem-sym-ab-at243243 c4) ▸ done

-- box-perm-2341: 4 steps
lem-box-perm-2341 : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2341 ∷ []) ⟫ʷ
lem-box-perm-2341 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ []) (Bx0-2341 ∷ [])
  b0 = at 0 1 (Bx0-2134 ∷ []) (lem-sym-ab c4) ▸
       at 0 1 (Bx0-3421 ∷ []) (lem-pairs-at1221 c4) ▸
       at 0 1 (Bx0-3241 ∷ []) (lem-sym-bc-at13243241 c4) ▸
       at 0 1 (Bx0-2341 ∷ []) (lem-sym-ab-at133441 c4) ▸ done

-- CKu-box-1: 7 steps
lem-CKu-box-1 : Ws → ⟪ (CK10 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CK10 ∷ []) ⟫ʷ
lem-CKu-box-1 c4 = run b0
  where
  b0 : Chain (CK10 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CK10 ∷ [])
  b0 = at 0 1 (CS01⁻ ∷ K0⁻ ∷ CS01⁻ ∷ K0 ∷ CS01⁻ ∷ []) (wl0362 (lit c4)) ▸
       at 4 2 (Bx0-1234 ∷ CS01⁻ ∷ []) (lem-CSdu-box-1 c4) ▸
       at 3 2 (Bx0-1234 ∷ K0 ∷ []) (lem-Ku-box c4) ▸
       at 2 2 (Bx0-1234 ∷ CS01⁻ ∷ []) (lem-CSdu-box-1 c4) ▸
       at 1 2 (Bx0-1234 ∷ K0⁻ ∷ []) (lem-Kdu-box c4) ▸
       at 0 2 (Bx0-1234 ∷ CS01⁻ ∷ []) (lem-CSdu-box-1 c4) ▸
       at 1 5 (CK10 ∷ []) (sym (wl0362 (lit c4))) ▸ done

-- CKdu-box-1: 7 steps
lem-CKdu-box-1 : Ws → ⟪ (CK10⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CK10⁻ ∷ []) ⟫ʷ
lem-CKdu-box-1 c4 = run b0
  where
  b0 : Chain (CK10⁻ ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CK10⁻ ∷ [])
  b0 = at 0 1 (CS01 ∷ K0⁻ ∷ CS01 ∷ K0 ∷ CS01 ∷ []) (wl0363 (lit c4)) ▸
       at 4 2 (Bx0-1234 ∷ CS01 ∷ []) (lem-CSu-box-1 c4) ▸
       at 3 2 (Bx0-1234 ∷ K0 ∷ []) (lem-Ku-box c4) ▸
       at 2 2 (Bx0-1234 ∷ CS01 ∷ []) (lem-CSu-box-1 c4) ▸
       at 1 2 (Bx0-1234 ∷ K0⁻ ∷ []) (lem-Kdu-box c4) ▸
       at 0 2 (Bx0-1234 ∷ CS01 ∷ []) (lem-CSu-box-1 c4) ▸
       at 1 5 (CK10⁻ ∷ []) (sym (wl0363 (lit c4))) ▸ done

-- CKu-box-2: 7 steps
lem-CKu-box-2 : Ws → ⟪ (CK20 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CK20 ∷ []) ⟫ʷ
lem-CKu-box-2 c4 = run b0
  where
  b0 : Chain (CK20 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CK20 ∷ [])
  b0 = at 0 1 (CS02⁻ ∷ K0⁻ ∷ CS02⁻ ∷ K0 ∷ CS02⁻ ∷ []) (wl0375 (lit c4)) ▸
       at 4 2 (Bx0-1234 ∷ CS02⁻ ∷ []) (lem-CSdu-box-2 c4) ▸
       at 3 2 (Bx0-1234 ∷ K0 ∷ []) (lem-Ku-box c4) ▸
       at 2 2 (Bx0-1234 ∷ CS02⁻ ∷ []) (lem-CSdu-box-2 c4) ▸
       at 1 2 (Bx0-1234 ∷ K0⁻ ∷ []) (lem-Kdu-box c4) ▸
       at 0 2 (Bx0-1234 ∷ CS02⁻ ∷ []) (lem-CSdu-box-2 c4) ▸
       at 1 5 (CK20 ∷ []) (sym (wl0375 (lit c4))) ▸ done

-- CKdu-box-2: 7 steps
lem-CKdu-box-2 : Ws → ⟪ (CK20⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CK20⁻ ∷ []) ⟫ʷ
lem-CKdu-box-2 c4 = run b0
  where
  b0 : Chain (CK20⁻ ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CK20⁻ ∷ [])
  b0 = at 0 1 (CS02 ∷ K0⁻ ∷ CS02 ∷ K0 ∷ CS02 ∷ []) (wl0376 (lit c4)) ▸
       at 4 2 (Bx0-1234 ∷ CS02 ∷ []) (lem-CSu-box-2 c4) ▸
       at 3 2 (Bx0-1234 ∷ K0 ∷ []) (lem-Ku-box c4) ▸
       at 2 2 (Bx0-1234 ∷ CS02 ∷ []) (lem-CSu-box-2 c4) ▸
       at 1 2 (Bx0-1234 ∷ K0⁻ ∷ []) (lem-Kdu-box c4) ▸
       at 0 2 (Bx0-1234 ∷ CS02 ∷ []) (lem-CSu-box-2 c4) ▸
       at 1 5 (CK20⁻ ∷ []) (sym (wl0376 (lit c4))) ▸ done

-- CKu-box-3: 7 steps
lem-CKu-box-3 : Ws → ⟪ (CK30 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CK30 ∷ []) ⟫ʷ
lem-CKu-box-3 c4 = run b0
  where
  b0 : Chain (CK30 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CK30 ∷ [])
  b0 = at 0 1 (CS03⁻ ∷ K0⁻ ∷ CS03⁻ ∷ K0 ∷ CS03⁻ ∷ []) (wl0385 (lit c4)) ▸
       at 4 2 (Bx0-1234 ∷ CS03⁻ ∷ []) (lem-CSdu-box-3 c4) ▸
       at 3 2 (Bx0-1234 ∷ K0 ∷ []) (lem-Ku-box c4) ▸
       at 2 2 (Bx0-1234 ∷ CS03⁻ ∷ []) (lem-CSdu-box-3 c4) ▸
       at 1 2 (Bx0-1234 ∷ K0⁻ ∷ []) (lem-Kdu-box c4) ▸
       at 0 2 (Bx0-1234 ∷ CS03⁻ ∷ []) (lem-CSdu-box-3 c4) ▸
       at 1 5 (CK30 ∷ []) (sym (wl0385 (lit c4))) ▸ done

-- CKdu-box-3: 7 steps
lem-CKdu-box-3 : Ws → ⟪ (CK30⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CK30⁻ ∷ []) ⟫ʷ
lem-CKdu-box-3 c4 = run b0
  where
  b0 : Chain (CK30⁻ ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CK30⁻ ∷ [])
  b0 = at 0 1 (CS03 ∷ K0⁻ ∷ CS03 ∷ K0 ∷ CS03 ∷ []) (wl0386 (lit c4)) ▸
       at 4 2 (Bx0-1234 ∷ CS03 ∷ []) (lem-CSu-box-3 c4) ▸
       at 3 2 (Bx0-1234 ∷ K0 ∷ []) (lem-Ku-box c4) ▸
       at 2 2 (Bx0-1234 ∷ CS03 ∷ []) (lem-CSu-box-3 c4) ▸
       at 1 2 (Bx0-1234 ∷ K0⁻ ∷ []) (lem-Kdu-box c4) ▸
       at 0 2 (Bx0-1234 ∷ CS03 ∷ []) (lem-CSu-box-3 c4) ▸
       at 1 5 (CK30⁻ ∷ []) (sym (wl0386 (lit c4))) ▸ done

-- XCSX-box-3: 4 steps
lem-XCSX-box-3 : Ws → ⟪ (X3 ∷ CS03 ∷ X3 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ X3 ∷ CS03 ∷ X3 ∷ []) ⟫ʷ
lem-XCSX-box-3 c4 = run b0
  where
  b0 : Chain (X3 ∷ CS03 ∷ X3 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ X3 ∷ CS03 ∷ X3 ∷ [])
  b0 = at 0 3 (S0 ∷ CS03⁻ ∷ []) (sym (wl0387 (lit c4))) ▸
       at 1 2 (Bx0-1234 ∷ CS03⁻ ∷ []) (lem-CSdu-box-3 c4) ▸
       at 0 2 (Bx0-1234 ∷ S0 ∷ []) (lem-Su-box c4) ▸
       at 1 2 (X3 ∷ CS03 ∷ X3 ∷ []) (wl0387 (lit c4)) ▸ done

-- XCSdX-box-3: 4 steps
lem-XCSdX-box-3 : Ws → ⟪ (X3 ∷ CS03⁻ ∷ X3 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) ⟫ʷ
lem-XCSdX-box-3 c4 = run b0
  where
  b0 : Chain (X3 ∷ CS03⁻ ∷ X3 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ [])
  b0 = at 0 3 (S0⁻ ∷ CS03 ∷ []) (sym (wl0388 (lit c4))) ▸
       at 1 2 (Bx0-1234 ∷ CS03 ∷ []) (lem-CSu-box-3 c4) ▸
       at 0 2 (Bx0-1234 ∷ S0⁻ ∷ []) (lem-Sdu-box c4) ▸
       at 1 2 (X3 ∷ CS03⁻ ∷ X3 ∷ []) (wl0388 (lit c4)) ▸ done

-- CKu-box-4: 7 steps
lem-CKu-box-4 : Ws → ⟪ (CK40 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CK40 ∷ []) ⟫ʷ
lem-CKu-box-4 c4 = run b0
  where
  b0 : Chain (CK40 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CK40 ∷ [])
  b0 = at 0 1 (CS04⁻ ∷ K0⁻ ∷ CS04⁻ ∷ K0 ∷ CS04⁻ ∷ []) (wp0255 c4) ▸
       at 4 2 (Bx0-1234 ∷ CS04⁻ ∷ []) (lem-CSdu-box-4 c4) ▸
       at 3 2 (Bx0-1234 ∷ K0 ∷ []) (lem-Ku-box c4) ▸
       at 2 2 (Bx0-1234 ∷ CS04⁻ ∷ []) (lem-CSdu-box-4 c4) ▸
       at 1 2 (Bx0-1234 ∷ K0⁻ ∷ []) (lem-Kdu-box c4) ▸
       at 0 2 (Bx0-1234 ∷ CS04⁻ ∷ []) (lem-CSdu-box-4 c4) ▸
       at 1 5 (CK40 ∷ []) (sym (wp0255 c4)) ▸ done

-- CKdu-box-4: 7 steps
lem-CKdu-box-4 : Ws → ⟪ (CK40⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CK40⁻ ∷ []) ⟫ʷ
lem-CKdu-box-4 c4 = run b0
  where
  b0 : Chain (CK40⁻ ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CK40⁻ ∷ [])
  b0 = at 0 1 (CS04 ∷ K0⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ []) (wp0256 c4) ▸
       at 4 2 (Bx0-1234 ∷ CS04 ∷ []) (lem-CSu-box-4 c4) ▸
       at 3 2 (Bx0-1234 ∷ K0 ∷ []) (lem-Ku-box c4) ▸
       at 2 2 (Bx0-1234 ∷ CS04 ∷ []) (lem-CSu-box-4 c4) ▸
       at 1 2 (Bx0-1234 ∷ K0⁻ ∷ []) (lem-Kdu-box c4) ▸
       at 0 2 (Bx0-1234 ∷ CS04 ∷ []) (lem-CSu-box-4 c4) ▸
       at 1 5 (CK40⁻ ∷ []) (sym (wp0256 c4)) ▸ done

-- XCSX-box-4: 4 steps
lem-XCSX-box-4 : Ws → ⟪ (X4 ∷ CS04 ∷ X4 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-XCSX-box-4 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS04 ∷ X4 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  b0 = at 0 3 (S0 ∷ CS04⁻ ∷ []) (sym (wp0257 c4)) ▸
       at 1 2 (Bx0-1234 ∷ CS04⁻ ∷ []) (lem-CSdu-box-4 c4) ▸
       at 0 2 (Bx0-1234 ∷ S0 ∷ []) (lem-Su-box c4) ▸
       at 1 2 (X4 ∷ CS04 ∷ X4 ∷ []) (wp0257 c4) ▸ done

-- XCSdX-box-4: 4 steps
lem-XCSdX-box-4 : Ws → ⟪ (X4 ∷ CS04⁻ ∷ X4 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ X4 ∷ CS04⁻ ∷ X4 ∷ []) ⟫ʷ
lem-XCSdX-box-4 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS04⁻ ∷ X4 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ X4 ∷ CS04⁻ ∷ X4 ∷ [])
  b0 = at 0 3 (S0⁻ ∷ CS04 ∷ []) (sym (wp0258 c4)) ▸
       at 1 2 (Bx0-1234 ∷ CS04 ∷ []) (lem-CSu-box-4 c4) ▸
       at 0 2 (Bx0-1234 ∷ S0⁻ ∷ []) (lem-Sdu-box c4) ▸
       at 1 2 (X4 ∷ CS04⁻ ∷ X4 ∷ []) (wp0258 c4) ▸ done

-- box-perm-1243 @3443: 3 steps
lem-box-perm-1243-at3443 : Ws → ⟪ (Bx0-1243 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-box-perm-1243-at3443 c4 = run b0
  where
  b0 : Chain (Bx0-1243 ∷ []) (Bx0-1234 ∷ [])
  b0 = at 0 1 (Bx0-4312 ∷ []) (lem-pairs-at3443 c4) ▸
       at 0 1 (Bx0-3412 ∷ []) (lem-sym-ab-at14233142 c4) ▸
       at 0 1 (Bx0-1234 ∷ []) (lem-pairs-at13243142 c4) ▸ done

-- F0-R: 11 steps
lem-F0-R : Ws → ⟪ (CX34 ∷ Toff412 ∷ CS04 ∷ Toff412 ∷ CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ CS04 ∷ Toff412 ∷ CS04⁻ ∷ Bx4-1203 ∷ CX34 ∷ []) ⟫ʷ
lem-F0-R c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CX34 ∷ Toff412 ∷ CS04 ∷ Toff412 ∷ CS04⁻ ∷ []) (Toff412 ∷ CS04 ∷ Toff412 ∷ Toff412 ∷ CCZ034 ∷ Toff412 ∷ CS04⁻ ∷ CCZ034 ∷ CX34 ∷ [])
  b0 = at 0 2 (Toff412 ∷ CX34 ∷ []) (wl0472 (lit c4)) ▸
       at 1 2 (CS04 ∷ CS03 ∷ CCZ034 ∷ CX34 ∷ []) (sym (wp0325 c4)) ▸
       at 4 2 (Toff412 ∷ CX34 ∷ []) (wl0472 (lit c4)) ▸
       at 5 2 (CS04⁻ ∷ CS03⁻ ∷ CCZ034 ∷ CX34 ∷ []) (sym (wp0326 c4)) ▸
       at 2 2 (CCZ034 ∷ CS03 ∷ []) (sym (wp0327 c4)) ▸
       at 3 2 (Toff412 ∷ CS03 ∷ []) (lem-comm-CS03-TOFF412 (lit c4)) ▸
       at 4 3 (CS04⁻ ∷ []) (wp0328 c4) ▸
       at 2 0 (Toff412 ∷ Toff412 ∷ []) (sym (wl0470 (lit c4))) ▸ done

  b1 : Chain (Toff412 ∷ CS04 ∷ Toff412 ∷ Toff412 ∷ CCZ034 ∷ Toff412 ∷ CS04⁻ ∷ CCZ034 ∷ CX34 ∷ []) (Toff412 ∷ CS04 ∷ Toff412 ∷ CS04⁻ ∷ Bx4-1203 ∷ CX34 ∷ [])
  b1 = at 6 2 (CCZ034 ∷ CS04⁻ ∷ []) (sym (wp0329 c4)) ▸
       at 3 4 (Bx4-1203 ∷ []) (sym (lem-box-tQ-at043043 c4)) ▸
       at 3 2 (CS04⁻ ∷ Bx4-1203 ∷ []) (sym (lem-CSdu-box-3-at043043 c4)) ▸ done

-- box-perm-4312 @0330: 2 steps
lem-box-perm-4312-at0330 : Ws → ⟪ (Bx3-1204 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4012 ∷ []) ⟫ʷ
lem-box-perm-4312-at0330 c4 = run b0
  where
  b0 : Chain (Bx3-1204 ∷ []) (Bx3-4012 ∷ [])
  b0 = at 0 1 (Bx3-0412 ∷ []) (lem-pairs-at0330 c4) ▸
       at 0 1 (Bx3-4012 ∷ []) (lem-sym-ab-at0310243142 c4) ▸ done

-- box-perm-3421 @0314203142: 2 steps
lem-box-perm-3421-at0314203142 : Ws → ⟪ (Bx3-4012 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1204 ∷ []) ⟫ʷ
lem-box-perm-3421-at0314203142 c4 = run b0
  where
  b0 : Chain (Bx3-4012 ∷ []) (Bx3-1204 ∷ [])
  b0 = at 0 1 (Bx3-0412 ∷ []) (lem-sym-ab-at0314203142 c4) ▸
       at 0 1 (Bx3-1204 ∷ []) (lem-pairs-at0310243142 c4) ▸ done

-- CKdu-box-2 @243243: 7 steps
lem-CKdu-box-2-at243243 : Ws → ⟪ (CK40⁻ ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ CK40⁻ ∷ []) ⟫ʷ
lem-CKdu-box-2-at243243 c4 = run b0
  where
  b0 : Chain (CK40⁻ ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ CK40⁻ ∷ [])
  b0 = at 0 1 (CS04 ∷ K0⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ []) (wp0256 c4) ▸
       at 4 2 (Bx0-1423 ∷ CS04 ∷ []) (lem-CSu-box-2-at243243 c4) ▸
       at 3 2 (Bx0-1423 ∷ K0 ∷ []) (lem-Ku-box-at243243 c4) ▸
       at 2 2 (Bx0-1423 ∷ CS04 ∷ []) (lem-CSu-box-2-at243243 c4) ▸
       at 1 2 (Bx0-1423 ∷ K0⁻ ∷ []) (lem-Kdu-box-at243243 c4) ▸
       at 0 2 (Bx0-1423 ∷ CS04 ∷ []) (lem-CSu-box-2-at243243 c4) ▸
       at 1 5 (CK40⁻ ∷ []) (sym (wp0256 c4)) ▸ done

-- CKdu-box-2 @122441: 7 steps
lem-CKdu-box-2-at122441 : Ws → ⟪ (CK40⁻ ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ CK40⁻ ∷ []) ⟫ʷ
lem-CKdu-box-2-at122441 c4 = run b0
  where
  b0 : Chain (CK40⁻ ∷ Bx0-2431 ∷ []) (Bx0-2431 ∷ CK40⁻ ∷ [])
  b0 = at 0 1 (CS04 ∷ K0⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ []) (wp0256 c4) ▸
       at 4 2 (Bx0-2431 ∷ CS04 ∷ []) (lem-CSu-box-2-at122441 c4) ▸
       at 3 2 (Bx0-2431 ∷ K0 ∷ []) (lem-Ku-box-at122441 c4) ▸
       at 2 2 (Bx0-2431 ∷ CS04 ∷ []) (lem-CSu-box-2-at122441 c4) ▸
       at 1 2 (Bx0-2431 ∷ K0⁻ ∷ []) (lem-Kdu-box-at122441 c4) ▸
       at 0 2 (Bx0-2431 ∷ CS04 ∷ []) (lem-CSu-box-2-at122441 c4) ▸
       at 1 5 (CK40⁻ ∷ []) (sym (wp0256 c4)) ▸ done

-- box-perm-1423 @0210243143: 3 steps
lem-box-perm-1423-at0210243143 : Ws → ⟪ (Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0341 ∷ []) ⟫ʷ
lem-box-perm-1423-at0210243143 c4 = run b0
  where
  b0 : Chain (Bx2-0413 ∷ []) (Bx2-0341 ∷ [])
  b0 = at 0 1 (Bx2-4013 ∷ []) (lem-sym-ab-at0210243143 c4) ▸
       at 0 1 (Bx2-4103 ∷ []) (lem-sym-bc-at0214203143 c4) ▸
       at 0 1 (Bx2-0341 ∷ []) (lem-pairs-at0214213043 c4) ▸ done

-- F4-K1-CS2: 19 steps
lem-F4-K1-CS2 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K1-CS2 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ CK41 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (CCZ023 ∷ X4 ∷ CK41 ∷ X4 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b0 = at 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 5 1 (CS12 ∷ []) (refl) ▸
       at 7 1 (CS12⁻ ∷ []) (refl) ▸
       at 3 1 (Bx0-2341 ∷ []) (lem-box-perm-1324-at122441 c4) ▸
       at 3 1 (CCZ023 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ []) (lem-box-cP-at12233441 c4) ▸
       at 2 2 (CCZ023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) (X))) ▸
       at 1 2 (CCZ023 ∷ CK41 ∷ []) (lem-comm-CK41-CCZ023 (lit c4)) ▸
       at 0 2 (CCZ023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) (X))) ▸ done

  b1 : Chain (CCZ023 ∷ X4 ∷ CK41 ∷ X4 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  b1 = at 1 4 (Toff014 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (sym (wp0531 c4)) ▸
       at 4 2 (CCZ023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) (X))) ▸
       at 3 2 (CCZ023 ∷ CK41 ∷ []) (lem-comm-CK41-CCZ023 (lit c4)) ▸
       at 2 2 (CCZ023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) (X))) ▸
       at 3 4 (Toff014 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (sym (wp0531 c4)) ▸
       at 0 4 (Bx0-2341 ∷ []) (sym (lem-box-cP-at12233441 c4)) ▸
       at 0 1 (Bx0-2431 ∷ []) (sym (lem-box-perm-1324-at122441 c4)) ▸
       at 1 7 (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CK41 ∷ X4 ∷ []) (sym (wl0654 (lit c4))) ▸ done

  b2 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CK41 ∷ X4 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  b2 = at 2 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 0 5 (Sb0-2-43-1 ∷ []) (refl) ▸ done

-- CKdu-box-2 @0210243143: 7 steps
lem-CKdu-box-2-at0210243143 : Ws → ⟪ (CK42⁻ ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ CK42⁻ ∷ []) ⟫ʷ
lem-CKdu-box-2-at0210243143 c4 = run b0
  where
  b0 : Chain (CK42⁻ ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ CK42⁻ ∷ [])
  b0 = at 0 1 (CS24 ∷ K2⁻ ∷ CS24 ∷ K2 ∷ CS24 ∷ []) (wl0664 (lit c4)) ▸
       at 4 2 (Bx2-0413 ∷ CS24 ∷ []) (lem-CSu-box-2-at0210243143 c4) ▸
       at 3 2 (Bx2-0413 ∷ K2 ∷ []) (lem-Ku-box-at0210243143 c4) ▸
       at 2 2 (Bx2-0413 ∷ CS24 ∷ []) (lem-CSu-box-2-at0210243143 c4) ▸
       at 1 2 (Bx2-0413 ∷ K2⁻ ∷ []) (lem-Kdu-box-at0210243143 c4) ▸
       at 0 2 (Bx2-0413 ∷ CS24 ∷ []) (lem-CSu-box-2-at0210243143 c4) ▸
       at 1 5 (CK42⁻ ∷ []) (sym (wl0664 (lit c4))) ▸ done

-- box-perm-1423 @243243: 3 steps
lem-box-perm-1423-at243243 : Ws → ⟪ (Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1342 ∷ []) ⟫ʷ
lem-box-perm-1423-at243243 c4 = run b0
  where
  b0 : Chain (Bx0-1423 ∷ []) (Bx0-1342 ∷ [])
  b0 = at 0 1 (Bx0-4123 ∷ []) (lem-sym-ab-at243243 c4) ▸
       at 0 1 (Bx0-4213 ∷ []) (lem-sym-bc-at14213243 c4) ▸
       at 0 1 (Bx0-1342 ∷ []) (lem-pairs-at143143 c4) ▸ done

-- F4-K3-CS0: 19 steps
lem-F4-K3-CS0 : Ws → ⟪ (X4 ∷ CK43 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K3-CS0 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ CK43 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (CCZ012 ∷ X4 ∷ CK43 ∷ X4 ∷ Toff234 ∷ CCZ012 ∷ Toff234 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b0 = at 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 5 1 (CS03 ∷ []) (refl) ▸
       at 7 1 (CS03⁻ ∷ []) (refl) ▸
       at 3 1 (Bx2-0143 ∷ []) (lem-box-perm-1324-at0210243143 c4) ▸
       at 3 1 (CCZ012 ∷ Toff234 ∷ CCZ012 ∷ Toff234 ∷ []) (lem-box-cP-at0210213443 c4) ▸
       at 2 2 (CCZ012 ∷ X4 ∷ []) (sym (c₃ (CCZ) (X ↑))) ▸
       at 1 2 (CCZ012 ∷ CK43 ∷ []) (sym (c₃ (CCZ) (CK₁₀))) ▸
       at 0 2 (CCZ012 ∷ X4 ∷ []) (sym (c₃ (CCZ) (X ↑))) ▸ done

  b1 : Chain (CCZ012 ∷ X4 ∷ CK43 ∷ X4 ∷ Toff234 ∷ CCZ012 ∷ Toff234 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  b1 = at 1 4 (Toff234 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (sym (wl0697 (lit c4))) ▸
       at 4 2 (CCZ012 ∷ X4 ∷ []) (sym (c₃ (CCZ) (X ↑))) ▸
       at 3 2 (CCZ012 ∷ CK43 ∷ []) (sym (c₃ (CCZ) (CK₁₀))) ▸
       at 2 2 (CCZ012 ∷ X4 ∷ []) (sym (c₃ (CCZ) (X ↑))) ▸
       at 3 4 (Toff234 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (sym (wl0697 (lit c4))) ▸
       at 0 4 (Bx2-0143 ∷ []) (sym (lem-box-cP-at0210213443 c4)) ▸
       at 0 1 (Bx2-0413 ∷ []) (sym (lem-box-perm-1324-at0210243143 c4)) ▸
       at 1 7 (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CK43 ∷ X4 ∷ []) (sym (wp0571 c4)) ▸ done

  b2 : Chain (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CK43 ∷ X4 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  b2 = at 2 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 4 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 0 5 (Sb2-0-41-3 ∷ []) (refl) ▸ done

-- F4-K3-CS1: 19 steps
lem-F4-K3-CS1 : Ws → ⟪ (X4 ∷ CK43 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K3-CS1 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ CK43 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (CCZ012 ∷ X4 ∷ CK43 ∷ X4 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b0 = at 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 5 1 (CS13 ∷ []) (refl) ▸
       at 7 1 (CS13⁻ ∷ []) (refl) ▸
       at 3 1 (Bx0-1243 ∷ []) (lem-box-perm-1324-at243243 c4) ▸
       at 3 1 (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ []) (lem-box-cP-at3443 c4) ▸
       at 2 2 (CCZ012 ∷ X4 ∷ []) (sym (c₃ (CCZ) (X ↑))) ▸
       at 1 2 (CCZ012 ∷ CK43 ∷ []) (sym (c₃ (CCZ) (CK₁₀))) ▸
       at 0 2 (CCZ012 ∷ X4 ∷ []) (sym (c₃ (CCZ) (X ↑))) ▸ done

  b1 : Chain (CCZ012 ∷ X4 ∷ CK43 ∷ X4 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  b1 = at 1 4 (Toff034 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (sym (wp0586 c4)) ▸
       at 4 2 (CCZ012 ∷ X4 ∷ []) (sym (c₃ (CCZ) (X ↑))) ▸
       at 3 2 (CCZ012 ∷ CK43 ∷ []) (sym (c₃ (CCZ) (CK₁₀))) ▸
       at 2 2 (CCZ012 ∷ X4 ∷ []) (sym (c₃ (CCZ) (X ↑))) ▸
       at 3 4 (Toff034 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (sym (wp0586 c4)) ▸
       at 0 4 (Bx0-1243 ∷ []) (sym (lem-box-cP-at3443 c4)) ▸
       at 0 1 (Bx0-1423 ∷ []) (sym (lem-box-perm-1324-at243243 c4)) ▸
       at 1 7 (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CK43 ∷ X4 ∷ []) (sym (wl0700 (lit c4))) ▸ done

  b2 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CK43 ∷ X4 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  b2 = at 2 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 0 5 (Sb0-1-42-3 ∷ []) (refl) ▸ done

-- F4-K3-CS2: 19 steps
lem-F4-K3-CS2 : Ws → ⟪ (X4 ∷ CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K3-CS2 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (CCZ012 ∷ X4 ∷ CK43 ∷ X4 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b0 = at 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 5 1 (CS12 ∷ []) (refl) ▸
       at 7 1 (CS12⁻ ∷ []) (refl) ▸
       at 3 1 (Bx0-2143 ∷ []) (lem-box-perm-1423-at122441 c4) ▸
       at 3 1 (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ []) (lem-box-cP-at12213443 c4) ▸
       at 2 2 (CCZ012 ∷ X4 ∷ []) (sym (c₃ (CCZ) (X ↑))) ▸
       at 1 2 (CCZ012 ∷ CK43 ∷ []) (sym (c₃ (CCZ) (CK₁₀))) ▸
       at 0 2 (CCZ012 ∷ X4 ∷ []) (sym (c₃ (CCZ) (X ↑))) ▸ done

  b1 : Chain (CCZ012 ∷ X4 ∷ CK43 ∷ X4 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  b1 = at 1 4 (Toff034 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (sym (wp0586 c4)) ▸
       at 4 2 (CCZ012 ∷ X4 ∷ []) (sym (c₃ (CCZ) (X ↑))) ▸
       at 3 2 (CCZ012 ∷ CK43 ∷ []) (sym (c₃ (CCZ) (CK₁₀))) ▸
       at 2 2 (CCZ012 ∷ X4 ∷ []) (sym (c₃ (CCZ) (X ↑))) ▸
       at 3 4 (Toff034 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (sym (wp0586 c4)) ▸
       at 0 4 (Bx0-2143 ∷ []) (sym (lem-box-cP-at12213443 c4)) ▸
       at 0 1 (Bx0-2431 ∷ []) (sym (lem-box-perm-1423-at122441 c4)) ▸
       at 1 7 (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CK43 ∷ X4 ∷ []) (sym (wl0708 (lit c4))) ▸ done

  b2 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CK43 ∷ X4 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  b2 = at 2 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 0 5 (Sb0-2-43-1 ∷ []) (refl) ▸ done

-- CKu-box-2 @0210243143: 7 steps
lem-CKu-box-2-at0210243143 : Ws → ⟪ (CK42 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ CK42 ∷ []) ⟫ʷ
lem-CKu-box-2-at0210243143 c4 = run b0
  where
  b0 : Chain (CK42 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ CK42 ∷ [])
  b0 = at 0 1 (CS24⁻ ∷ K2⁻ ∷ CS24⁻ ∷ K2 ∷ CS24⁻ ∷ []) (wl0724 (lit c4)) ▸
       at 4 2 (Bx2-0413 ∷ CS24⁻ ∷ []) (lem-CSdu-box-2-at0210243143 c4) ▸
       at 3 2 (Bx2-0413 ∷ K2 ∷ []) (lem-Ku-box-at0210243143 c4) ▸
       at 2 2 (Bx2-0413 ∷ CS24⁻ ∷ []) (lem-CSdu-box-2-at0210243143 c4) ▸
       at 1 2 (Bx2-0413 ∷ K2⁻ ∷ []) (lem-Kdu-box-at0210243143 c4) ▸
       at 0 2 (Bx2-0413 ∷ CS24⁻ ∷ []) (lem-CSdu-box-2-at0210243143 c4) ▸
       at 1 5 (CK42 ∷ []) (sym (wl0724 (lit c4))) ▸ done

-- F4-CS0-K3: 21 steps
lem-F4-CS0-K3 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS0-K3 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK43 ∷ []) (X4 ∷ CCZ012 ∷ Toff234 ∷ CCZ012 ∷ K3 ∷ CK43 ∷ S4 ∷ Toff234 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ [])
  b0 = at 2 2 (K3 ∷ CK43 ∷ S4 ∷ X4 ∷ []) (sym (wl0729 (lit c4))) ▸
       at 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 1 (CS03 ∷ []) (refl) ▸
       at 5 1 (CS03⁻ ∷ []) (refl) ▸
       at 2 7 (K3 ∷ CK43 ∷ S4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (sym (wp0618 c4)) ▸
       at 1 1 (Bx2-0143 ∷ []) (lem-box-perm-1324-at0210243143 c4) ▸
       at 1 1 (CCZ012 ∷ Toff234 ∷ CCZ012 ∷ Toff234 ∷ []) (lem-box-cP-at0210213443 c4) ▸
       at 4 4 (K3 ∷ CK43 ∷ S4 ∷ Toff234 ∷ []) (sym (wl0730 (lit c4))) ▸ done

  b1 : Chain (X4 ∷ CCZ012 ∷ Toff234 ∷ CCZ012 ∷ K3 ∷ CK43 ∷ S4 ∷ Toff234 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ []) (X4 ∷ K3 ∷ CK43 ∷ S4 ∷ Bx2-0143 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ [])
  b1 = at 3 2 (K3 ∷ CCZ012 ∷ []) (c₃ (CCZ) (K)) ▸
       at 4 2 (CK43 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CK₁₀)) ▸
       at 5 2 (S4 ∷ CCZ012 ∷ []) (c₃ (CCZ) (S ↑)) ▸
       at 2 4 (K3 ∷ CK43 ∷ S4 ∷ Toff234 ∷ []) (sym (wl0730 (lit c4))) ▸
       at 1 2 (K3 ∷ CCZ012 ∷ []) (c₃ (CCZ) (K)) ▸
       at 2 2 (CK43 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CK₁₀)) ▸
       at 3 2 (S4 ∷ CCZ012 ∷ []) (c₃ (CCZ) (S ↑)) ▸
       at 4 4 (Bx2-0143 ∷ []) (sym (lem-box-cP-at0210213443 c4)) ▸ done

  b2 : Chain (X4 ∷ K3 ∷ CK43 ∷ S4 ∷ Bx2-0143 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ []) (CK43 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  b2 = at 4 1 (Bx2-0413 ∷ []) (sym (lem-box-perm-1324-at0210243143 c4)) ▸
       at 6 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 8 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 4 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 0 4 (CK43 ∷ X4 ∷ []) (sym (wl0731 (lit c4))) ▸ done

-- CKu-box-2 @243243: 7 steps
lem-CKu-box-2-at243243 : Ws → ⟪ (CK40 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ CK40 ∷ []) ⟫ʷ
lem-CKu-box-2-at243243 c4 = run b0
  where
  b0 : Chain (CK40 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ CK40 ∷ [])
  b0 = at 0 1 (CS04⁻ ∷ K0⁻ ∷ CS04⁻ ∷ K0 ∷ CS04⁻ ∷ []) (wp0255 c4) ▸
       at 4 2 (Bx0-1423 ∷ CS04⁻ ∷ []) (lem-CSdu-box-2-at243243 c4) ▸
       at 3 2 (Bx0-1423 ∷ K0 ∷ []) (lem-Ku-box-at243243 c4) ▸
       at 2 2 (Bx0-1423 ∷ CS04⁻ ∷ []) (lem-CSdu-box-2-at243243 c4) ▸
       at 1 2 (Bx0-1423 ∷ K0⁻ ∷ []) (lem-Kdu-box-at243243 c4) ▸
       at 0 2 (Bx0-1423 ∷ CS04⁻ ∷ []) (lem-CSdu-box-2-at243243 c4) ▸
       at 1 5 (CK40 ∷ []) (sym (wp0255 c4)) ▸ done

-- F4-CS1-K3: 21 steps
lem-F4-CS1-K3 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS1-K3 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK43 ∷ []) (X4 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ K3 ∷ CK43 ∷ S4 ∷ Toff034 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ [])
  b0 = at 2 2 (K3 ∷ CK43 ∷ S4 ∷ X4 ∷ []) (sym (wl0729 (lit c4))) ▸
       at 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 3 1 (CS13 ∷ []) (refl) ▸
       at 5 1 (CS13⁻ ∷ []) (refl) ▸
       at 2 7 (K3 ∷ CK43 ∷ S4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (sym (wl0738 (lit c4))) ▸
       at 1 1 (Bx0-1243 ∷ []) (lem-box-perm-1324-at243243 c4) ▸
       at 1 1 (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ []) (lem-box-cP-at3443 c4) ▸
       at 4 4 (K3 ∷ CK43 ∷ S4 ∷ Toff034 ∷ []) (sym (wp0636 c4)) ▸ done

  b1 : Chain (X4 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ K3 ∷ CK43 ∷ S4 ∷ Toff034 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ []) (X4 ∷ K3 ∷ CK43 ∷ S4 ∷ Bx0-1243 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ [])
  b1 = at 3 2 (K3 ∷ CCZ012 ∷ []) (c₃ (CCZ) (K)) ▸
       at 4 2 (CK43 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CK₁₀)) ▸
       at 5 2 (S4 ∷ CCZ012 ∷ []) (c₃ (CCZ) (S ↑)) ▸
       at 2 4 (K3 ∷ CK43 ∷ S4 ∷ Toff034 ∷ []) (sym (wp0636 c4)) ▸
       at 1 2 (K3 ∷ CCZ012 ∷ []) (c₃ (CCZ) (K)) ▸
       at 2 2 (CK43 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CK₁₀)) ▸
       at 3 2 (S4 ∷ CCZ012 ∷ []) (c₃ (CCZ) (S ↑)) ▸
       at 4 4 (Bx0-1243 ∷ []) (sym (lem-box-cP-at3443 c4)) ▸ done

  b2 : Chain (X4 ∷ K3 ∷ CK43 ∷ S4 ∷ Bx0-1243 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ []) (CK43 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  b2 = at 4 1 (Bx0-1423 ∷ []) (sym (lem-box-perm-1324-at243243 c4)) ▸
       at 6 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 8 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 4 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 0 4 (CK43 ∷ X4 ∷ []) (sym (wl0731 (lit c4))) ▸ done

-- CKu-box-2 @122441: 7 steps
lem-CKu-box-2-at122441 : Ws → ⟪ (CK40 ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ CK40 ∷ []) ⟫ʷ
lem-CKu-box-2-at122441 c4 = run b0
  where
  b0 : Chain (CK40 ∷ Bx0-2431 ∷ []) (Bx0-2431 ∷ CK40 ∷ [])
  b0 = at 0 1 (CS04⁻ ∷ K0⁻ ∷ CS04⁻ ∷ K0 ∷ CS04⁻ ∷ []) (wp0255 c4) ▸
       at 4 2 (Bx0-2431 ∷ CS04⁻ ∷ []) (lem-CSdu-box-2-at122441 c4) ▸
       at 3 2 (Bx0-2431 ∷ K0 ∷ []) (lem-Ku-box-at122441 c4) ▸
       at 2 2 (Bx0-2431 ∷ CS04⁻ ∷ []) (lem-CSdu-box-2-at122441 c4) ▸
       at 1 2 (Bx0-2431 ∷ K0⁻ ∷ []) (lem-Kdu-box-at122441 c4) ▸
       at 0 2 (Bx0-2431 ∷ CS04⁻ ∷ []) (lem-CSdu-box-2-at122441 c4) ▸
       at 1 5 (CK40 ∷ []) (sym (wp0255 c4)) ▸ done

-- F4-CS2-K1: 21 steps
lem-F4-CS2-K1 : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS2-K1 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK41 ∷ []) (X4 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ K1 ∷ CK41 ∷ S4 ∷ Toff014 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ [])
  b0 = at 2 2 (K1 ∷ CK41 ∷ S4 ∷ X4 ∷ []) (sym (wl0720 (lit c4))) ▸
       at 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 3 1 (CS12 ∷ []) (refl) ▸
       at 5 1 (CS12⁻ ∷ []) (refl) ▸
       at 2 7 (K1 ∷ CK41 ∷ S4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (sym (wl0741 (lit c4))) ▸
       at 1 1 (Bx0-2341 ∷ []) (lem-box-perm-1324-at122441 c4) ▸
       at 1 1 (CCZ023 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ []) (lem-box-cP-at12233441 c4) ▸
       at 4 4 (K1 ∷ CK41 ∷ S4 ∷ Toff014 ∷ []) (sym (wp0648 c4)) ▸ done

  b1 : Chain (X4 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ K1 ∷ CK41 ∷ S4 ∷ Toff014 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ []) (X4 ∷ K1 ∷ CK41 ∷ S4 ∷ Bx0-2341 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ [])
  b1 = at 3 2 (K1 ∷ CCZ023 ∷ []) (wl0722 (lit c4)) ▸
       at 4 2 (CK41 ∷ CCZ023 ∷ []) (lem-comm-CCZ023-CK41 (lit c4)) ▸
       at 5 2 (S4 ∷ CCZ023 ∷ []) (c₄ (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) (S)) ▸
       at 2 4 (K1 ∷ CK41 ∷ S4 ∷ Toff014 ∷ []) (sym (wp0648 c4)) ▸
       at 1 2 (K1 ∷ CCZ023 ∷ []) (wl0722 (lit c4)) ▸
       at 2 2 (CK41 ∷ CCZ023 ∷ []) (lem-comm-CCZ023-CK41 (lit c4)) ▸
       at 3 2 (S4 ∷ CCZ023 ∷ []) (c₄ (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) (S)) ▸
       at 4 4 (Bx0-2341 ∷ []) (sym (lem-box-cP-at12233441 c4)) ▸ done

  b2 : Chain (X4 ∷ K1 ∷ CK41 ∷ S4 ∷ Bx0-2341 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ []) (CK41 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  b2 = at 4 1 (Bx0-2431 ∷ []) (sym (lem-box-perm-1324-at122441 c4)) ▸
       at 6 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 8 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 4 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 0 4 (CK41 ∷ X4 ∷ []) (sym (wl0723 (lit c4))) ▸ done

-- F4-CS2-K3: 21 steps
lem-F4-CS2-K3 : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS2-K3 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK43 ∷ []) (X4 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ K3 ∷ CK43 ∷ S4 ∷ Toff034 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ [])
  b0 = at 2 2 (K3 ∷ CK43 ∷ S4 ∷ X4 ∷ []) (sym (wl0729 (lit c4))) ▸
       at 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 3 1 (CS12 ∷ []) (refl) ▸
       at 5 1 (CS12⁻ ∷ []) (refl) ▸
       at 2 7 (K3 ∷ CK43 ∷ S4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (sym (wl0744 (lit c4))) ▸
       at 1 1 (Bx0-2143 ∷ []) (lem-box-perm-1423-at122441 c4) ▸
       at 1 1 (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ []) (lem-box-cP-at12213443 c4) ▸
       at 4 4 (K3 ∷ CK43 ∷ S4 ∷ Toff034 ∷ []) (sym (wp0636 c4)) ▸ done

  b1 : Chain (X4 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ K3 ∷ CK43 ∷ S4 ∷ Toff034 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ []) (X4 ∷ K3 ∷ CK43 ∷ S4 ∷ Bx0-2143 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ [])
  b1 = at 3 2 (K3 ∷ CCZ012 ∷ []) (c₃ (CCZ) (K)) ▸
       at 4 2 (CK43 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CK₁₀)) ▸
       at 5 2 (S4 ∷ CCZ012 ∷ []) (c₃ (CCZ) (S ↑)) ▸
       at 2 4 (K3 ∷ CK43 ∷ S4 ∷ Toff034 ∷ []) (sym (wp0636 c4)) ▸
       at 1 2 (K3 ∷ CCZ012 ∷ []) (c₃ (CCZ) (K)) ▸
       at 2 2 (CK43 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CK₁₀)) ▸
       at 3 2 (S4 ∷ CCZ012 ∷ []) (c₃ (CCZ) (S ↑)) ▸
       at 4 4 (Bx0-2143 ∷ []) (sym (lem-box-cP-at12213443 c4)) ▸ done

  b2 : Chain (X4 ∷ K3 ∷ CK43 ∷ S4 ∷ Bx0-2143 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ []) (CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  b2 = at 4 1 (Bx0-2431 ∷ []) (sym (lem-box-perm-1423-at122441 c4)) ▸
       at 6 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 8 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 4 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 0 4 (CK43 ∷ X4 ∷ []) (sym (wl0731 (lit c4))) ▸ done

-- box-perm-4312 @0214213043: 2 steps
lem-box-perm-4312-at0214213043 : Ws → ⟪ (Bx2-4103 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3041 ∷ []) ⟫ʷ
lem-box-perm-4312-at0214213043 c4 = run b0
  where
  b0 : Chain (Bx2-4103 ∷ []) (Bx2-3041 ∷ [])
  b0 = at 0 1 (Bx2-0341 ∷ []) (lem-pairs-at0214213043 c4) ▸
       at 0 1 (Bx2-3041 ∷ []) (lem-sym-ab-at0210233441 c4) ▸ done

-- box-perm-3421 @0213203441: 2 steps
lem-box-perm-3421-at0213203441 : Ws → ⟪ (Bx2-3041 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4103 ∷ []) ⟫ʷ
lem-box-perm-3421-at0213203441 c4 = run b0
  where
  b0 : Chain (Bx2-3041 ∷ []) (Bx2-4103 ∷ [])
  b0 = at 0 1 (Bx2-0341 ∷ []) (lem-sym-ab-at0213203441 c4) ▸
       at 0 1 (Bx2-4103 ∷ []) (lem-pairs-at0210233441 c4) ▸ done

-- F0-R @14213243: 11 steps
lem-F0-R-at14213243 : Ws → ⟪ (CX23 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Bx3-4102 ∷ CX23 ∷ []) ⟫ʷ
lem-F0-R-at14213243 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CX23 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Toff314 ∷ CS03 ∷ Toff314 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ CS03⁻ ∷ CCZ023 ∷ CX23 ∷ [])
  b0 = at 0 2 (Toff314 ∷ CX23 ∷ []) (wl0794 (lit c4)) ▸
       at 1 2 (CS03 ∷ CS02 ∷ CCZ023 ∷ CX23 ∷ []) (sym (wl0795 (lit c4))) ▸
       at 4 2 (Toff314 ∷ CX23 ∷ []) (wl0794 (lit c4)) ▸
       at 5 2 (CS03⁻ ∷ CS02⁻ ∷ CCZ023 ∷ CX23 ∷ []) (sym (wl0796 (lit c4))) ▸
       at 2 2 (CCZ023 ∷ CS02 ∷ []) (sym (wl0797 (lit c4))) ▸
       at 3 2 (Toff314 ∷ CS02 ∷ []) (lem-comm-CS02-TOFF314 (lit c4)) ▸
       at 4 3 (CS03⁻ ∷ []) (wl0798 (lit c4)) ▸
       at 2 0 (Toff314 ∷ Toff314 ∷ []) (sym (wl0788 (lit c4))) ▸ done

  b1 : Chain (Toff314 ∷ CS03 ∷ Toff314 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ CS03⁻ ∷ CCZ023 ∷ CX23 ∷ []) (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Bx3-4102 ∷ CX23 ∷ [])
  b1 = at 6 2 (CCZ023 ∷ CS03⁻ ∷ []) (sym (wl0799 (lit c4))) ▸
       at 3 4 (Bx3-4102 ∷ []) (sym (lem-box-tQ-at0314213042 c4)) ▸
       at 3 2 (CS03⁻ ∷ Bx3-4102 ∷ []) (sym (lem-CSdu-box-3-at0314213042 c4)) ▸ done

-- CXAu-S @14213243: 12 steps
lem-CXAu-S-at14213243 : Ws → ⟪ (CX32 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ CX32 ∷ []) ⟫ʷ
lem-CXAu-S-at14213243 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CX32 ∷ Sb2-0-41-3 ∷ []) (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CX32 ∷ CS03⁻ ∷ [])
  b0 = at 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 1 (CS03 ∷ []) (refl) ▸
       at 5 1 (CS03⁻ ∷ []) (refl) ▸
       at 0 2 (Bx2-0413 ∷ CX32 ∷ []) (lem-CXu-box-4-at0210243143 c4) ▸
       at 1 2 (Toff314 ∷ CX32 ∷ Toff214 ∷ []) (wl0810 (lit c4)) ▸
       at 3 2 (CS03 ∷ Toff214 ∷ []) (lem-comm-TOFF214-CS03 (lit c4)) ▸
       at 2 2 (CS03 ∷ CX32 ∷ []) (sym (wl0811 (lit c4))) ▸
       at 3 3 (Toff314 ∷ CX32 ∷ []) (wl0812 (lit c4)) ▸ done

  b1 : Chain (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CX32 ∷ CS03⁻ ∷ []) (Sb2-0-41-3 ∷ CX32 ∷ [])
  b1 = at 4 2 (CS03⁻ ∷ CX32 ∷ []) (sym (wl0813 (lit c4))) ▸
       at 2 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 4 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 0 5 (Sb2-0-41-3 ∷ []) (refl) ▸ done

-- box-perm-1342 @0310243142: 3 steps
lem-box-perm-1342-at0310243142 : Ws → ⟪ (Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ []) ⟫ʷ
lem-box-perm-1342-at0310243142 c4 = run b0
  where
  b0 : Chain (Bx3-0412 ∷ []) (Bx3-0124 ∷ [])
  b0 = at 0 1 (Bx3-1204 ∷ []) (lem-pairs-at0310243142 c4) ▸
       at 0 1 (Bx3-1024 ∷ []) (lem-sym-bc-at0330 c4) ▸
       at 0 1 (Bx3-0124 ∷ []) (lem-sym-ab-at032032 c4) ▸ done

-- box-perm-4132 @243243: 3 steps
lem-box-perm-4132-at243243 : Ws → ⟪ (Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3124 ∷ []) ⟫ʷ
lem-box-perm-4132-at243243 c4 = run b0
  where
  b0 : Chain (Bx0-1423 ∷ []) (Bx0-3124 ∷ [])
  b0 = at 0 1 (Bx0-2314 ∷ []) (lem-pairs-at243243 c4) ▸
       at 0 1 (Bx0-3214 ∷ []) (lem-sym-ab-at122331 c4) ▸
       at 0 1 (Bx0-3124 ∷ []) (lem-sym-bc-at1331 c4) ▸ done

-- box-perm-4123 @033440: 4 steps
lem-box-perm-4123-at033440 : Ws → ⟪ (Bx3-1240 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ []) ⟫ʷ
lem-box-perm-4123-at033440 c4 = run b0
  where
  b0 : Chain (Bx3-1240 ∷ []) (Bx3-0124 ∷ [])
  b0 = at 0 1 (Bx3-2140 ∷ []) (lem-sym-ab-at033440 c4) ▸
       at 0 1 (Bx3-2410 ∷ []) (lem-sym-bc-at0312213440 c4) ▸
       at 0 1 (Bx3-1024 ∷ []) (lem-pairs-at0312243140 c4) ▸
       at 0 1 (Bx3-0124 ∷ []) (lem-sym-ab-at032032 c4) ▸ done

-- box-perm-2431 @132132: 3 steps
lem-box-perm-2431-at132132 : Ws → ⟪ (Bx0-3124 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ []) ⟫ʷ
lem-box-perm-2431-at132132 c4 = run b0
  where
  b0 : Chain (Bx0-3124 ∷ []) (Bx0-1423 ∷ [])
  b0 = at 0 1 (Bx0-3214 ∷ []) (lem-sym-bc-at132132 c4) ▸
       at 0 1 (Bx0-2314 ∷ []) (lem-sym-ab-at1331 c4) ▸
       at 0 1 (Bx0-1423 ∷ []) (lem-pairs-at122331 c4) ▸ done

-- box-perm-1423 @03102132: 3 steps
lem-box-perm-1423-at03102132 : Ws → ⟪ (Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ []) ⟫ʷ
lem-box-perm-1423-at03102132 c4 = run b0
  where
  b0 : Chain (Bx3-0124 ∷ []) (Bx3-0412 ∷ [])
  b0 = at 0 1 (Bx3-1024 ∷ []) (lem-sym-ab-at03102132 c4) ▸
       at 0 1 (Bx3-1204 ∷ []) (lem-sym-bc-at032032 c4) ▸
       at 0 1 (Bx3-0412 ∷ []) (lem-pairs-at0330 c4) ▸ done

-- box-perm-1342 @0210243143: 3 steps
lem-box-perm-1342-at0210243143 : Ws → ⟪ (Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ []) ⟫ʷ
lem-box-perm-1342-at0210243143 c4 = run b0
  where
  b0 : Chain (Bx2-0413 ∷ []) (Bx2-0134 ∷ [])
  b0 = at 0 1 (Bx2-1304 ∷ []) (lem-pairs-at0210243143 c4) ▸
       at 0 1 (Bx2-1034 ∷ []) (lem-sym-bc-at022330 c4) ▸
       at 0 1 (Bx2-0134 ∷ []) (lem-sym-ab-at0220 c4) ▸ done

-- box-box-1 @021021: 105 steps
lem-box-box-1-at021021 : Ws → ⟪ (Bx2-0134 ∷ Bx0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ Bx2-0134 ∷ []) ⟫ʷ
lem-box-box-1-at021021 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (run b13)))))))))))))
  where
  b0 : Chain (Bx2-0134 ∷ Bx0-2134 ∷ []) (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ012 ∷ Toff034 ∷ CCZ024 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CCZ012 ∷ CX23 ∷ CS24 ∷ Toff034 ∷ [])
  b0 = at 0 1 (Bx2-1340 ∷ []) (lem-box-perm-2341-at021021 c4) ▸
       at 0 1 (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ []) (lem-box-tQ-at02233440 c4) ▸
       at 4 1 (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ []) (lem-box-cP-at1221 c4) ▸
       at 3 2 (CCZ012 ∷ CCZ024 ∷ []) (sym (wp0142 c4)) ▸
       at 4 2 (Toff034 ∷ CCZ024 ∷ CCZ234 ∷ []) (wp0139 c4) ▸
       at 6 1 (CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ []) (wl0274 (lit c4)) ▸
       at 10 2 (CCZ012 ∷ CS24 ∷ []) (sym (wp0141 c4)) ▸
       at 9 2 (CCZ012 ∷ CX23 ∷ []) (sym (wl0411 (lit c4))) ▸ done

  b1 : Chain (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ012 ∷ Toff034 ∷ CCZ024 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CCZ012 ∷ CX23 ∷ CS24 ∷ Toff034 ∷ []) (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ024 ∷ [])
  b1 = at 8 2 (CCZ012 ∷ CS34⁻ ∷ []) (sym (c₃ (CCZ) (CS • CS • CS))) ▸
       at 7 2 (CCZ012 ∷ CX23 ∷ []) (sym (wl0411 (lit c4))) ▸
       at 6 2 (CCZ012 ∷ CS34 ∷ []) (sym (c₃ (CCZ) (CS))) ▸
       at 7 5 (CCZ234 ∷ []) (sym (wl0274 (lit c4))) ▸
       at 5 2 (CCZ012 ∷ CCZ024 ∷ []) (sym (wp0142 c4)) ▸
       at 6 3 (Toff034 ∷ CCZ024 ∷ []) (wp0770 c4) ▸
       at 3 4 (Bx0-2134 ∷ []) (sym (lem-box-cP-at1221 c4)) ▸
       at 3 1 (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ []) (lem-box-cP-at1221 c4) ▸ done

  b2 : Chain (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ024 ∷ []) (Toff213 ∷ CCZ024 ∷ CCZ012 ∷ K2 ∷ CS13 ∷ Toff034 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ K2⁻ ∷ CCZ013 ∷ CCZ134 ∷ CCZ012 ∷ Toff034 ∷ CCZ024 ∷ [])
  b2 = at 2 2 (CCZ012 ∷ Toff213 ∷ CCZ013 ∷ []) (sym (wl0940 (lit c4))) ▸
       at 4 2 (Toff034 ∷ CCZ013 ∷ CCZ134 ∷ []) (wp0771 c4) ▸
       at 3 1 (K2 ∷ CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ K2⁻ ∷ []) (sym (wl0952 (lit c4))) ▸
       at 9 2 (Toff034 ∷ K2⁻ ∷ []) (wp0751 c4) ▸
       at 8 2 (Toff034 ∷ CS23 ∷ []) (wp0146 c4) ▸
       at 7 2 (Toff034 ∷ CX21 ∷ []) (lem-comm-CX21-TOFF034 (lit c4)) ▸
       at 6 2 (Toff034 ∷ CS13⁻ ∷ []) (wp0772 c4) ▸
       at 5 2 (Toff034 ∷ CX21 ∷ []) (lem-comm-CX21-TOFF034 (lit c4)) ▸ done

  b3 : Chain (Toff213 ∷ CCZ024 ∷ CCZ012 ∷ K2 ∷ CS13 ∷ Toff034 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ K2⁻ ∷ CCZ013 ∷ CCZ134 ∷ CCZ012 ∷ Toff034 ∷ CCZ024 ∷ []) (Toff213 ∷ CCZ024 ∷ CCZ012 ∷ Toff034 ∷ Toff213 ∷ CCZ013 ∷ CS34 ∷ CCZ012 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ Toff034 ∷ CCZ024 ∷ [])
  b3 = at 4 2 (Toff034 ∷ CS13 ∷ []) (wp0171 c4) ▸
       at 3 2 (Toff034 ∷ K2 ∷ []) (wp0752 c4) ▸
       at 4 7 (Toff213 ∷ []) (wl0952 (lit c4)) ▸
       at 6 1 (CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ []) (wl0166 (lit c4)) ▸
       at 10 2 (CCZ012 ∷ CS14 ∷ []) (sym (wp0011 c4)) ▸
       at 9 2 (CCZ012 ∷ CX13 ∷ []) (sym (wl0167 (lit c4))) ▸
       at 8 2 (CCZ012 ∷ CS34⁻ ∷ []) (sym (c₃ (CCZ) (CS • CS • CS))) ▸
       at 7 2 (CCZ012 ∷ CX13 ∷ []) (sym (wl0167 (lit c4))) ▸ done

  b4 : Chain (Toff213 ∷ CCZ024 ∷ CCZ012 ∷ Toff034 ∷ Toff213 ∷ CCZ013 ∷ CS34 ∷ CCZ012 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ Toff034 ∷ CCZ024 ∷ []) (Toff213 ∷ CCZ024 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ K2 ∷ CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ Toff034 ∷ K2⁻ ∷ CCZ134 ∷ CCZ024 ∷ [])
  b4 = at 6 2 (CCZ012 ∷ CS34 ∷ []) (sym (c₃ (CCZ) (CS))) ▸
       at 7 5 (CCZ134 ∷ []) (sym (wl0166 (lit c4))) ▸
       at 5 2 (CCZ012 ∷ CCZ013 ∷ []) (sym (wl0704 (lit c4))) ▸
       at 4 2 (CCZ012 ∷ Toff213 ∷ CCZ013 ∷ []) (sym (wl0940 (lit c4))) ▸
       at 5 3 (Toff213 ∷ []) (wl0953 (lit c4)) ▸
       at 6 2 (Toff034 ∷ CCZ134 ∷ []) (wp0012 c4) ▸
       at 5 1 (K2 ∷ CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ K2⁻ ∷ []) (sym (wl0952 (lit c4))) ▸
       at 11 2 (Toff034 ∷ K2⁻ ∷ []) (wp0751 c4) ▸ done

  b5 : Chain (Toff213 ∷ CCZ024 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ K2 ∷ CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ Toff034 ∷ K2⁻ ∷ CCZ134 ∷ CCZ024 ∷ []) (Toff213 ∷ CCZ024 ∷ Bx0-2134 ∷ Toff213 ∷ CCZ134 ∷ CCZ024 ∷ [])
  b5 = at 10 2 (Toff034 ∷ CS23 ∷ []) (wp0146 c4) ▸
       at 9 2 (Toff034 ∷ CX21 ∷ []) (lem-comm-CX21-TOFF034 (lit c4)) ▸
       at 8 2 (Toff034 ∷ CS13⁻ ∷ []) (wp0772 c4) ▸
       at 7 2 (Toff034 ∷ CX21 ∷ []) (lem-comm-CX21-TOFF034 (lit c4)) ▸
       at 6 2 (Toff034 ∷ CS13 ∷ []) (wp0171 c4) ▸
       at 5 2 (Toff034 ∷ K2 ∷ []) (wp0752 c4) ▸
       at 6 7 (Toff213 ∷ []) (wl0952 (lit c4)) ▸
       at 2 4 (Bx0-2134 ∷ []) (sym (lem-box-cP-at1221 c4)) ▸ done

  b6 : Chain (Toff213 ∷ CCZ024 ∷ Bx0-2134 ∷ Toff213 ∷ CCZ134 ∷ CCZ024 ∷ []) (Toff213 ∷ CCZ012 ∷ Toff034 ∷ CCZ024 ∷ CS34 ∷ CCZ012 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ Toff034 ∷ Toff213 ∷ CCZ134 ∷ CCZ024 ∷ [])
  b6 = at 2 1 (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ []) (lem-box-cP-at1221 c4) ▸
       at 1 2 (CCZ012 ∷ CCZ024 ∷ []) (sym (wp0142 c4)) ▸
       at 2 2 (Toff034 ∷ CCZ024 ∷ CCZ234 ∷ []) (wp0139 c4) ▸
       at 4 1 (CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ []) (wl0274 (lit c4)) ▸
       at 8 2 (CCZ012 ∷ CS24 ∷ []) (sym (wp0141 c4)) ▸
       at 7 2 (CCZ012 ∷ CX23 ∷ []) (sym (wl0411 (lit c4))) ▸
       at 6 2 (CCZ012 ∷ CS34⁻ ∷ []) (sym (c₃ (CCZ) (CS • CS • CS))) ▸
       at 5 2 (CCZ012 ∷ CX23 ∷ []) (sym (wl0411 (lit c4))) ▸ done

  b7 : Chain (Toff213 ∷ CCZ012 ∷ Toff034 ∷ CCZ024 ∷ CS34 ∷ CCZ012 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ Toff034 ∷ Toff213 ∷ CCZ134 ∷ CCZ024 ∷ []) (CCZ012 ∷ Toff213 ∷ Toff034 ∷ CCZ013 ∷ CCZ134 ∷ CCZ012 ∷ Toff034 ∷ CCZ024 ∷ Toff213 ∷ CCZ134 ∷ CCZ024 ∷ [])
  b7 = at 4 2 (CCZ012 ∷ CS34 ∷ []) (sym (c₃ (CCZ) (CS))) ▸
       at 5 5 (CCZ234 ∷ []) (sym (wl0274 (lit c4))) ▸
       at 3 2 (CCZ012 ∷ CCZ024 ∷ []) (sym (wp0142 c4)) ▸
       at 4 3 (Toff034 ∷ CCZ024 ∷ []) (wp0770 c4) ▸
       at 1 4 (Bx0-2134 ∷ []) (sym (lem-box-cP-at1221 c4)) ▸
       at 1 1 (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ []) (lem-box-cP-at1221 c4) ▸
       at 0 2 (CCZ012 ∷ Toff213 ∷ CCZ013 ∷ []) (sym (wl0940 (lit c4))) ▸
       at 2 2 (Toff034 ∷ CCZ013 ∷ CCZ134 ∷ []) (wp0771 c4) ▸ done

  b8 : Chain (CCZ012 ∷ Toff213 ∷ Toff034 ∷ CCZ013 ∷ CCZ134 ∷ CCZ012 ∷ Toff034 ∷ CCZ024 ∷ Toff213 ∷ CCZ134 ∷ CCZ024 ∷ []) (CCZ012 ∷ Toff034 ∷ K2 ∷ CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ K2⁻ ∷ CCZ013 ∷ CCZ134 ∷ CCZ012 ∷ Toff034 ∷ CCZ024 ∷ Toff213 ∷ CCZ134 ∷ CCZ024 ∷ [])
  b8 = at 1 1 (K2 ∷ CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ K2⁻ ∷ []) (sym (wl0952 (lit c4))) ▸
       at 7 2 (Toff034 ∷ K2⁻ ∷ []) (wp0751 c4) ▸
       at 6 2 (Toff034 ∷ CS23 ∷ []) (wp0146 c4) ▸
       at 5 2 (Toff034 ∷ CX21 ∷ []) (lem-comm-CX21-TOFF034 (lit c4)) ▸
       at 4 2 (Toff034 ∷ CS13⁻ ∷ []) (wp0772 c4) ▸
       at 3 2 (Toff034 ∷ CX21 ∷ []) (lem-comm-CX21-TOFF034 (lit c4)) ▸
       at 2 2 (Toff034 ∷ CS13 ∷ []) (wp0171 c4) ▸
       at 1 2 (Toff034 ∷ K2 ∷ []) (wp0752 c4) ▸ done

  b9 : Chain (CCZ012 ∷ Toff034 ∷ K2 ∷ CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ K2⁻ ∷ CCZ013 ∷ CCZ134 ∷ CCZ012 ∷ Toff034 ∷ CCZ024 ∷ Toff213 ∷ CCZ134 ∷ CCZ024 ∷ []) (CCZ012 ∷ Toff034 ∷ Toff213 ∷ CCZ013 ∷ CCZ012 ∷ CCZ134 ∷ Toff034 ∷ CCZ024 ∷ Toff213 ∷ CCZ134 ∷ CCZ024 ∷ [])
  b9 = at 2 7 (Toff213 ∷ []) (wl0952 (lit c4)) ▸
       at 4 1 (CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ []) (wl0166 (lit c4)) ▸
       at 8 2 (CCZ012 ∷ CS14 ∷ []) (sym (wp0011 c4)) ▸
       at 7 2 (CCZ012 ∷ CX13 ∷ []) (sym (wl0167 (lit c4))) ▸
       at 6 2 (CCZ012 ∷ CS34⁻ ∷ []) (sym (c₃ (CCZ) (CS • CS • CS))) ▸
       at 5 2 (CCZ012 ∷ CX13 ∷ []) (sym (wl0167 (lit c4))) ▸
       at 4 2 (CCZ012 ∷ CS34 ∷ []) (sym (c₃ (CCZ) (CS))) ▸
       at 5 5 (CCZ134 ∷ []) (sym (wl0166 (lit c4))) ▸ done

  b10 : Chain (CCZ012 ∷ Toff034 ∷ Toff213 ∷ CCZ013 ∷ CCZ012 ∷ CCZ134 ∷ Toff034 ∷ CCZ024 ∷ Toff213 ∷ CCZ134 ∷ CCZ024 ∷ []) (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ K2 ∷ CS13 ∷ CX21 ∷ CS13⁻ ∷ Toff034 ∷ CX21 ∷ CS23 ∷ K2⁻ ∷ CCZ134 ∷ CCZ024 ∷ Toff213 ∷ CCZ134 ∷ CCZ024 ∷ [])
  b10 = at 3 2 (CCZ012 ∷ CCZ013 ∷ []) (sym (wl0704 (lit c4))) ▸
       at 2 2 (CCZ012 ∷ Toff213 ∷ CCZ013 ∷ []) (sym (wl0940 (lit c4))) ▸
       at 3 3 (Toff213 ∷ []) (wl0953 (lit c4)) ▸
       at 4 2 (Toff034 ∷ CCZ134 ∷ []) (wp0012 c4) ▸
       at 3 1 (K2 ∷ CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ K2⁻ ∷ []) (sym (wl0952 (lit c4))) ▸
       at 9 2 (Toff034 ∷ K2⁻ ∷ []) (wp0751 c4) ▸
       at 8 2 (Toff034 ∷ CS23 ∷ []) (wp0146 c4) ▸
       at 7 2 (Toff034 ∷ CX21 ∷ []) (lem-comm-CX21-TOFF034 (lit c4)) ▸ done

  b11 : Chain (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ K2 ∷ CS13 ∷ CX21 ∷ CS13⁻ ∷ Toff034 ∷ CX21 ∷ CS23 ∷ K2⁻ ∷ CCZ134 ∷ CCZ024 ∷ Toff213 ∷ CCZ134 ∷ CCZ024 ∷ []) (Bx0-2134 ∷ Toff213 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ Toff213 ∷ CCZ134 ∷ CCZ024 ∷ [])
  b11 = at 6 2 (Toff034 ∷ CS13⁻ ∷ []) (wp0772 c4) ▸
       at 5 2 (Toff034 ∷ CX21 ∷ []) (lem-comm-CX21-TOFF034 (lit c4)) ▸
       at 4 2 (Toff034 ∷ CS13 ∷ []) (wp0171 c4) ▸
       at 3 2 (Toff034 ∷ K2 ∷ []) (wp0752 c4) ▸
       at 4 7 (Toff213 ∷ []) (wl0952 (lit c4)) ▸
       at 0 4 (Bx0-2134 ∷ []) (sym (lem-box-cP-at1221 c4)) ▸
       at 2 1 (CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ []) (wl0166 (lit c4)) ▸
       at 6 2 (CCZ024 ∷ CS14 ∷ []) (sym (wp0034 c4)) ▸ done

  b12 : Chain (Bx0-2134 ∷ Toff213 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ Toff213 ∷ CCZ134 ∷ CCZ024 ∷ []) (Bx0-2134 ∷ Bx2-1340 ∷ [])
  b12 = at 5 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ CS34⁻ ∷ []) (sym (wp0035 c4)) ▸
       at 3 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 3 5 (CCZ134 ∷ []) (sym (wl0166 (lit c4))) ▸
       at 3 2 (Toff213 ∷ CCZ134 ∷ []) (wl0954 (lit c4)) ▸
       at 4 2 [] (wl0321 (lit c4)) ▸
       at 1 4 (Bx2-1340 ∷ []) (sym (lem-box-tQ-at02233440 c4)) ▸ done

  b13 : Chain (Bx0-2134 ∷ Bx2-1340 ∷ []) (Bx0-2134 ∷ Bx2-0134 ∷ [])
  b13 = at 1 1 (Bx2-0134 ∷ []) (lem-box-perm-4123-at02233440 c4) ▸ done

-- box-perm-1432 @1221: 4 steps
lem-box-perm-1432-at1221 : Ws → ⟪ (Bx0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ []) ⟫ʷ
lem-box-perm-1432-at1221 c4 = run b0
  where
  b0 : Chain (Bx0-2134 ∷ []) (Bx0-2431 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ []) (lem-sym-ab-at1221 c4) ▸
       at 0 1 (Bx0-1324 ∷ []) (lem-sym-bc c4) ▸
       at 0 1 (Bx0-3124 ∷ []) (lem-sym-ab-at2332 c4) ▸
       at 0 1 (Bx0-2431 ∷ []) (lem-pairs-at132132 c4) ▸ done

-- box-perm-1423 @021021: 3 steps
lem-box-perm-1423-at021021 : Ws → ⟪ (Bx2-0134 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ []) ⟫ʷ
lem-box-perm-1423-at021021 c4 = run b0
  where
  b0 : Chain (Bx2-0134 ∷ []) (Bx2-0413 ∷ [])
  b0 = at 0 1 (Bx2-1034 ∷ []) (lem-sym-ab-at021021 c4) ▸
       at 0 1 (Bx2-1304 ∷ []) (lem-sym-bc-at0220 c4) ▸
       at 0 1 (Bx2-0413 ∷ []) (lem-pairs-at022330 c4) ▸ done

-- box-perm-1342 @243243: 3 steps
lem-box-perm-1342-at243243 : Ws → ⟪ (Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-box-perm-1342-at243243 c4 = run b0
  where
  b0 : Chain (Bx0-1423 ∷ []) (Bx0-1234 ∷ [])
  b0 = at 0 1 (Bx0-2314 ∷ []) (lem-pairs-at243243 c4) ▸
       at 0 1 (Bx0-2134 ∷ []) (lem-sym-bc-at122331 c4) ▸
       at 0 1 (Bx0-1234 ∷ []) (lem-sym-ab-at1221 c4) ▸ done

-- box-perm-3241 @243243: 3 steps
lem-box-perm-3241-at243243 : Ws → ⟪ (Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ []) ⟫ʷ
lem-box-perm-3241-at243243 c4 = run b0
  where
  b0 : Chain (Bx0-1423 ∷ []) (Bx0-2431 ∷ [])
  b0 = at 0 1 (Bx0-4123 ∷ []) (lem-sym-ab-at243243 c4) ▸
       at 0 1 (Bx0-2341 ∷ []) (lem-pairs-at14213243 c4) ▸
       at 0 1 (Bx0-2431 ∷ []) (lem-sym-bc-at12233441 c4) ▸ done

-- box-perm-4213 @122441: 3 steps
lem-box-perm-4213-at122441 : Ws → ⟪ (Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ []) ⟫ʷ
lem-box-perm-4213-at122441 c4 = run b0
  where
  b0 : Chain (Bx0-2431 ∷ []) (Bx0-1423 ∷ [])
  b0 = at 0 1 (Bx0-2341 ∷ []) (lem-sym-bc-at122441 c4) ▸
       at 0 1 (Bx0-4123 ∷ []) (lem-pairs-at12233441 c4) ▸
       at 0 1 (Bx0-1423 ∷ []) (lem-sym-ab-at14213243 c4) ▸ done

-- box-perm-4132 @122441: 3 steps
lem-box-perm-4132-at122441 : Ws → ⟪ (Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-box-perm-4132-at122441 c4 = run b0
  where
  b0 : Chain (Bx0-2431 ∷ []) (Bx0-1234 ∷ [])
  b0 = at 0 1 (Bx0-3124 ∷ []) (lem-pairs-at122441 c4) ▸
       at 0 1 (Bx0-1324 ∷ []) (lem-sym-ab-at132132 c4) ▸
       at 0 1 (Bx0-1234 ∷ []) (lem-sym-bc-at2332 c4) ▸ done

-- F2-K1-CS2: 35 steps
lem-F2-K1-CS2 : Ws → ⟪ (CK41 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ CK41 ∷ []) ⟫ʷ
lem-F2-K1-CS2 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (run b4))))
  where
  b0 : Chain (CK41 ∷ Sb0-2-43-1 ∷ []) (Toff023 ∷ CCZ014 ∷ CZ01 ∷ CK41 ∷ Toff023 ∷ CZ01 ∷ CCZ123 ∷ CCZ014 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b0 = at 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 3 1 (CS12 ∷ []) (refl) ▸
       at 5 1 (CS12⁻ ∷ []) (refl) ▸
       at 1 1 (Bx0-2341 ∷ []) (lem-box-perm-1324-at122441 c4) ▸
       at 1 1 (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ []) (lem-box-tQ-at12233441 c4) ▸
       at 0 2 (Toff023 ∷ CK41 ∷ []) (lem-comm-CK41-TOFF023 (lit c4)) ▸
       at 1 2 (CCZ014 ∷ CZ01 ∷ CK41 ∷ CZ01 ∷ []) (sym (wp0876 c4)) ▸
       at 4 2 (Toff023 ∷ CZ01 ∷ CCZ123 ∷ []) (wl0206 (lit c4)) ▸ done

  b1 : Chain (Toff023 ∷ CCZ014 ∷ CZ01 ∷ CK41 ∷ Toff023 ∷ CZ01 ∷ CCZ123 ∷ CCZ014 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CZ01 ∷ CCZ123 ∷ CK41 ∷ CZ01 ∷ CCZ014 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b1 = at 3 2 (Toff023 ∷ CK41 ∷ []) (lem-comm-CK41-TOFF023 (lit c4)) ▸
       at 2 2 (Toff023 ∷ CZ01 ∷ CCZ123 ∷ []) (wl0206 (lit c4)) ▸
       at 7 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0207 (lit c4)) ▸
       at 11 2 (CCZ014 ∷ CS13 ∷ []) (sym (wp0053 c4)) ▸
       at 10 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸
       at 9 2 (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 (lit c4)) ▸
       at 8 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸
       at 7 2 (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 (lit c4)) ▸ done

  b2 : Chain (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CZ01 ∷ CCZ123 ∷ CK41 ∷ CZ01 ∷ CCZ014 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CZ01 ∷ CS23 ∷ CCZ014 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CZ01 ∷ CK41 ∷ CZ01 ∷ CZ01 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b2 = at 8 5 (CCZ123 ∷ []) (sym (wl0207 (lit c4))) ▸
       at 6 2 (CCZ014 ∷ CZ01 ∷ []) (sym (wp0055 c4)) ▸
       at 5 2 (CCZ014 ∷ CZ01 ∷ CK41 ∷ CZ01 ∷ []) (sym (wp0876 c4)) ▸
       at 4 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0207 (lit c4)) ▸
       at 8 2 (CCZ014 ∷ CS13 ∷ []) (sym (wp0053 c4)) ▸
       at 7 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸
       at 6 2 (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 (lit c4)) ▸
       at 5 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸ done

  b3 : Chain (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CZ01 ∷ CS23 ∷ CCZ014 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CZ01 ∷ CK41 ∷ CZ01 ∷ CZ01 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK41 ∷ [])
  b3 = at 4 2 (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 (lit c4)) ▸
       at 5 5 (CCZ123 ∷ []) (sym (wl0207 (lit c4))) ▸
       at 3 2 (CCZ014 ∷ CZ01 ∷ []) (sym (wp0055 c4)) ▸
       at 6 4 (CZ01 ∷ CK41 ∷ []) (wp0877 c4) ▸
       at 4 3 (CCZ123 ∷ []) (sym (wl1065 (lit c4))) ▸
       at 0 4 (Bx0-2341 ∷ []) (sym (lem-box-tQ-at12233441 c4)) ▸
       at 0 1 (Bx0-2431 ∷ []) (sym (lem-box-perm-1324-at122441 c4)) ▸
       at 1 7 (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK41 ∷ []) (wl1066 (lit c4)) ▸ done

  b4 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK41 ∷ []) (Sb0-2-43-1 ∷ CK41 ∷ [])
  b4 = at 2 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 0 5 (Sb0-2-43-1 ∷ []) (refl) ▸ done
