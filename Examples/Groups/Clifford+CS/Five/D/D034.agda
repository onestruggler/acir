{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D034 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0171 ; wl0173 ; wl0175 ; wl0179 ; wl0180 ; wl0181 ; wl0184 ; wl0230 ; wl0231 ; wl0263 ; wl0288 ; wl0294 ; wl0297 ; wl0298 ; wl0302 ; wl0306 ; wl0311 ; wl0321 ; wl0324 ; wl0327 ; wl0330 ; wl0331 ; wl0341 ; wl0381 ; wl0383 ; wl0384 ; wl0415 ; wl0416 ; wl0417 ; wl0418 ; wl0419 ; wl0420 ; wl0421 ; wl0423 ; wl0426 ; wl0432 ; wl0433 ; wl0436 ; wl0441 ; wl0442 ; wl0443 ; wl0444 ; wl0445 ; wl0452 ; wl0480 ; wl0482 ; wl0485 ; wl0490 ; wl0492 ; wl0495 ; wl0508 ; wl0509 ; wl0543 ; wl0611 ; wl0618 ; wl0645 ; wl0675 ; wl0702 ; wl0703 ; wl0707 ; wl0763 ; wl0765 ; wl0770 ; wl0781 ; wl0782 ; wl0783 ; wl0784 ; wl0785 ; wl0786 ; wl0787 ; wl0788 ; wl0808 ; wl0831 ; wl0842 ; wl0843 ; wl0844 ; wl0846 ; wl0847 ; wl0866 ; wl0867 ; wl0868 ; wl0912 ; wl0913 ; wl0914 ; wl0915 ; wl0916 ; wl0917 ; wl0920 ; wl0923 ; wl0928 ; wl0932 ; wl0933 ; wl0934 ; wl0936 ; wl0937 ; wl0949 ; wl0950 ; wl0951 ; wl0961 ; wl0992 ; wl1155 ; wl1167 ; wl1257 ; wl1258 ; wl1259 ; wl1260 ; wl1266 ; wl1273 ; wl1316 ; wl1317 ; wl1318 ; wl1319 ; wl1320 ; wl1321 ; wl1322 ; wl1323 ; wl1324 ; wl1325 ; wl1326 ; wl1327 ; wl1328 ; wl1329 ; wl1330 ; wl1331 ; wl1332 ; wl1333 ; wl1334 ; wl1335 ; wl1336 ; wl1337 ; wl1338 ; wl1339 ; wp0011 ; wp0022 ; wp0025 ; wp0026 ; wp0034 ; wp0036 ; wp0081 ; wp0087 ; wp0090 ; wp0092 ; wp0109 ; wp0129 ; wp0131 ; wp0141 ; wp0161 ; wp0162 ; wp0167 ; wp0185 ; wp0189 ; wp0194 ; wp0195 ; wp0196 ; wp0197 ; wp0214 ; wp0262 ; wp0272 ; wp0294 ; wp0299 ; wp0308 ; wp0320 ; wp0352 ; wp0353 ; wp0354 ; wp0366 ; wp0377 ; wp0378 ; wp0380 ; wp0381 ; wp0382 ; wp0383 ; wp0389 ; wp0390 ; wp0394 ; wp0496 ; wp0499 ; wp0501 ; wp0505 ; wp0560 ; wp0563 ; wp0565 ; wp0566 ; wp0567 ; wp0687 ; wp0703 ; wp0705 ; wp0746 ; wp0759 ; wp0761 ; wp0762 ; wp0763 ; wp0764 ; wp0769 ; wp0774 ; wp0778 ; wp0779 ; wp0827 ; wp0897 ; wp0945 ; wp0949 ; wp1037 ; wp1055 ; wp1056 ; wp1059 ; wp1071 ; wp1094 ; wp1099 ; wp1141 ; wp1142 ; wp1143 ; wp1144 ; wp1145 ; wp1146 ; wp1147 ; wp1148 ; wp1149 ; wp1150 ; wp1151 ; wp1152 ; wp1153 ; wp1154 ; wp1155 ; wp1156 ; wp1157 ; wp1158 ; wp1159 ; wp1160 ; wp1161 ; wp1162 ; wp1163 ; wp1164 ; wp1165 ; wp1166 ; wp1167 ; wp1168 ; wp1169 ; wp1170 ; wp1171 ; wp1172 ; wp1173 ; wp1174 ; wp1175 ; wp1176 ; wp1177 ; wp1178 ; wp1179 ; wp1180 ; wp1181 ; wp1182 ; wp1183 ; wp1184 ; wp1185 ; wp1186 ; wp1187 ; wp1188 ; wp1189 ; wp1190 ; wp1191 ; wp1192 ; wp1193)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-box-cP-at03102132 ; lem-tP-at03102132)
open import Examples.Groups.Clifford+CS.Five.D.D006 using (lem-box-tQ-at0214203143 ; lem-sym-ab-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D007 using (lem-box-cP-at0210213443 ; lem-sym-bc-at0210243143 ; lem-tP-at0210213443)
open import Examples.Groups.Clifford+CS.Five.D.D009 using (lem-sym-ab-at0214203143)
open import Examples.Groups.Clifford+CS.Five.D.D014 using (lem-box-tQ-at0210213443 ; lem-box-tQ-at03102132)
open import Examples.Groups.Clifford+CS.Five.D.D015 using (lem-S2-SBOX⟨0·2·43·1⟩)
open import Examples.Groups.Clifford+CS.Five.D.D017 using (lem-box-cP-at02102441 ; lem-box-tQ-at02102441 ; lem-tP-at02102441)
open import Examples.Groups.Clifford+CS.Five.D.D023 using (lem-box-cP-at0312243041 ; lem-box-tQ-at0312243041 ; lem-tP-at0312243041)
open import Examples.Groups.Clifford+CS.Five.D.D030 using (lem-cQ-at031031)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CSd04-TOFF213 ; lem-comm-CZ04-CCZ123)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-CZ13-CCZ024 ; lem-comm-CZ24-CCZ013)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-CS04-TOFF213 ; lem-comm-CSd12-TOFF304 ; lem-comm-CX31-CCZ024 ; lem-comm-CX40-CCZ123 ; lem-comm-CX42-CCZ013)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-comm-CS12-TOFF304 ; lem-comm-CS13-TOFF204 ; lem-comm-CSd02-TOFF314 ; lem-comm-CSd13-TOFF204 ; lem-comm-CZ13-TOFF204 ; lem-comm-CZ24-TOFF301 ; lem-comm-SWAP14-BOX⟨2·03⟩)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-comm-CX24-TOFF301 ; lem-comm-CX31-TOFF204 ; lem-comm-SWAP02-BOX⟨3·41⟩ ; lem-comm-SWAP03-BOX⟨2·41⟩ ; lem-comm-TOFF302-CSd14)
-- L-CX10-2: 2 steps
lem-L-CX10-2 : Ws → ⟪ (CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ []) ⟫ʷ
lem-L-CX10-2 c4 = run b0
  where
  b0 : Chain (CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ []) (Toff234 ∷ [])
  b0 = at 1 2 (CCZ234 ∷ []) (lem-S2-SBOX⟨0·2·43·1⟩ c4) ▸
       at 0 4 (Toff234 ∷ []) (wl1316 (lit c4)) ▸ done


-- tP @031031: 7 steps
lem-tP-at031031 : Ws → ⟪ (Toff302 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ Toff302 ∷ []) ⟫ʷ
lem-tP-at031031 c4 = run b0
  where
  b0 : Chain (Toff302 ∷ Toff314 ∷ []) (Toff314 ∷ Toff302 ∷ [])
  b0 = at 0 1 (K3 ∷ CCZ023 ∷ K3⁻ ∷ []) (sym (wl0782 (lit c4))) ▸
       at 3 1 (K3 ∷ CCZ134 ∷ K3⁻ ∷ []) (sym (wl0781 (lit c4))) ▸
       at 2 2 [] (wl0436 (lit c4)) ▸
       at 1 2 (CCZ134 ∷ CCZ023 ∷ []) (lem-cQ-at031031 c4) ▸
       at 2 0 (K3⁻ ∷ K3 ∷ []) (sym (wl0436 (lit c4))) ▸
       at 0 3 (Toff314 ∷ []) (wl0781 (lit c4)) ▸
       at 1 3 (Toff302 ∷ []) (wl0782 (lit c4)) ▸ done


-- VPQ @031031: 14 steps
lem-VPQ-at031031 : Ws → ⟪ (Toff302 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CCZ134 ∷ Toff302 ∷ CCZ023 ∷ []) ⟫ʷ
lem-VPQ-at031031 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff302 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ []) (CS14⁻ ∷ CS02⁻ ∷ S3 ∷ Toff314 ∷ Toff302 ∷ S3⁻ ∷ [])
  b0 = at 0 2 (CS02⁻ ∷ S3 ∷ Toff302 ∷ S3⁻ ∷ []) (sym (wl0784 (lit c4))) ▸
       at 4 2 (CS14⁻ ∷ S3 ∷ Toff314 ∷ S3⁻ ∷ []) (sym (wl0783 (lit c4))) ▸
       at 3 2 (CS14⁻ ∷ S3⁻ ∷ []) (sym (wl0786 (lit c4))) ▸
       at 2 2 (CS14⁻ ∷ Toff302 ∷ []) (lem-comm-TOFF302-CSd14 (lit c4)) ▸
       at 1 2 (CS14⁻ ∷ S3 ∷ []) (sym (wl0785 (lit c4))) ▸
       at 0 2 (CS14⁻ ∷ CS02⁻ ∷ []) (wp0703 c4) ▸
       at 4 2 [] (wl0441 (lit c4)) ▸
       at 3 2 (Toff314 ∷ Toff302 ∷ []) (lem-tP-at031031 c4) ▸ done

  b1 : Chain (CS14⁻ ∷ CS02⁻ ∷ S3 ∷ Toff314 ∷ Toff302 ∷ S3⁻ ∷ []) (Toff314 ∷ CCZ134 ∷ Toff302 ∷ CCZ023 ∷ [])
  b1 = at 4 0 (S3⁻ ∷ S3 ∷ []) (sym (wl0441 (lit c4))) ▸
       at 1 2 (S3 ∷ CS02⁻ ∷ []) (c₃ (Swap ↑ • (CS • CS • CS) • Swap ↑) (S)) ▸
       at 2 2 (Toff314 ∷ CS02⁻ ∷ []) (lem-comm-CSd02-TOFF314 (lit c4)) ▸
       at 3 2 (S3⁻ ∷ CS02⁻ ∷ []) (c₃ (Swap ↑ • (CS • CS • CS) • Swap ↑) (S • S • S)) ▸
       at 0 4 (Toff314 ∷ CCZ134 ∷ []) (wl0783 (lit c4)) ▸
       at 2 4 (Toff302 ∷ CCZ023 ∷ []) (wl0784 (lit c4)) ▸ done


-- QVQ @031031: 3 steps
lem-QVQ-at031031 : Ws → ⟪ (CCZ134 ∷ Toff302 ∷ CCZ023 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ Toff302 ∷ CCZ023 ∷ Toff314 ∷ []) ⟫ʷ
lem-QVQ-at031031 c4 = run b0
  where
  b0 : Chain (CCZ134 ∷ Toff302 ∷ CCZ023 ∷ CCZ134 ∷ []) (Toff314 ∷ Toff302 ∷ CCZ023 ∷ Toff314 ∷ [])
  b0 = at 0 0 (Toff314 ∷ Toff314 ∷ []) (sym (wl0788 (lit c4))) ▸
       at 1 4 (Toff302 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ []) (sym (lem-VPQ-at031031 c4)) ▸
       at 4 2 [] (wl0321 (lit c4)) ▸ done


-- box-cP @031031: 12 steps
lem-box-cP-at031031 : Ws → ⟪ (Bx3-0214 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ []) ⟫ʷ
lem-box-cP-at031031 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-0214 ∷ []) (CCZ023 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ023 ∷ CCZ013 ∷ Toff013 ∷ CZ04 ∷ Toff013 ∷ CCZ013 ∷ CZ04 ∷ [])
  b0 = at 0 1 (CCZ023 ∷ Toff302 ∷ Bx0-314 ∷ Toff302 ∷ CCZ023 ∷ Bx0-314 ∷ []) (refl) ▸
       at 2 1 (CCZ013 ∷ Toff013 ∷ Bx3-04 ∷ Toff013 ∷ CCZ013 ∷ Bx3-04 ∷ []) (refl) ▸
       at 4 1 (CZ04 ∷ []) (refl) ▸
       at 7 1 (CZ04 ∷ []) (refl) ▸
       at 2 6 (CCZ134 ∷ []) (wp0262 c4) ▸
       at 5 1 (CCZ013 ∷ Toff013 ∷ Bx3-04 ∷ Toff013 ∷ CCZ013 ∷ Bx3-04 ∷ []) (refl) ▸
       at 7 1 (CZ04 ∷ []) (refl) ▸
       at 10 1 (CZ04 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ023 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ023 ∷ CCZ013 ∷ Toff013 ∷ CZ04 ∷ Toff013 ∷ CCZ013 ∷ CZ04 ∷ []) (CCZ023 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ [])
  b1 = at 5 6 (CCZ134 ∷ []) (wp0262 c4) ▸
       at 2 4 (Toff314 ∷ Toff302 ∷ CCZ023 ∷ Toff314 ∷ []) (lem-QVQ-at031031 c4) ▸
       at 1 2 (Toff314 ∷ Toff302 ∷ []) (lem-tP-at031031 c4) ▸
       at 2 2 [] (wl0787 (lit c4)) ▸ done


-- P-box @03102132: 8 steps
lem-P-box-at03102132 : Ws → ⟪ (Toff324 ∷ Bx3-0124 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ []) ⟫ʷ
lem-P-box-at03102132 c4 = run b0
  where
  b0 : Chain (Toff324 ∷ Bx3-0124 ∷ Toff324 ∷ []) (Bx3-0124 ∷ [])
  b0 = at 1 1 (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ []) (lem-box-tQ-at03102132 c4) ▸
       at 0 2 (Toff301 ∷ Toff324 ∷ []) (sym (lem-tP-at03102132 c4)) ▸
       at 1 2 (CCZ234 ∷ CZ24 ∷ Toff324 ∷ []) (sym (wl0842 (lit c4))) ▸
       at 3 2 (Toff301 ∷ Toff324 ∷ []) (sym (lem-tP-at03102132 c4)) ▸
       at 4 3 (CCZ234 ∷ CZ24 ∷ []) (sym (wl0843 (lit c4))) ▸
       at 2 2 (Toff301 ∷ CZ24 ∷ []) (lem-comm-CZ24-TOFF301 (lit c4)) ▸
       at 3 3 (CCZ234 ∷ []) (sym (wl0844 (lit c4))) ▸
       at 0 4 (Bx3-0124 ∷ []) (sym (lem-box-tQ-at03102132 c4)) ▸ done


-- pairs @03102132: 4 steps
lem-pairs-at03102132 : Ws → ⟪ (Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2401 ∷ []) ⟫ʷ
lem-pairs-at03102132 c4 = run b0
  where
  b0 : Chain (Bx3-0124 ∷ []) (Bx3-2401 ∷ [])
  b0 = at 0 1 (Toff324 ∷ Bx3-0124 ∷ Toff324 ∷ []) (sym (lem-P-box-at03102132 c4)) ▸
       at 1 1 (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ []) (lem-box-cP-at03102132 c4) ▸
       at 4 2 [] (wl0442 (lit c4)) ▸
       at 0 4 (Bx3-2401 ∷ []) (sym (lem-box-tQ-at0312243041 c4)) ▸ done


-- sym-ab @0312243041: 18 steps
lem-sym-ab-at0312243041 : Ws → ⟪ (Bx3-2401 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4201 ∷ []) ⟫ʷ
lem-sym-ab-at0312243041 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx3-2401 ∷ []) (CCZ234 ∷ Toff324 ∷ CCZ034 ∷ Toff403 ∷ Bx3-41 ∷ Toff403 ∷ CCZ034 ∷ Bx3-41 ∷ Toff324 ∷ CCZ234 ∷ Bx2-301 ∷ [])
  b0 = at 0 1 (CCZ234 ∷ Toff324 ∷ Bx2-301 ∷ Toff324 ∷ CCZ234 ∷ Bx2-301 ∷ []) (refl) ▸
       at 2 1 (CCZ023 ∷ Toff203 ∷ Bx3-21 ∷ Toff203 ∷ CCZ023 ∷ Bx3-21 ∷ []) (refl) ▸
       at 4 1 (CZ12 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 2 6 (CCZ013 ∷ []) (sym (wl0231 (lit c4))) ▸
       at 2 1 (CCZ034 ∷ Toff403 ∷ CZ14 ∷ Toff403 ∷ CCZ034 ∷ CZ14 ∷ []) (wp0214 c4) ▸
       at 4 1 (Bx3-41 ∷ []) (refl) ▸
       at 7 1 (Bx3-41 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ234 ∷ Toff324 ∷ CCZ034 ∷ Toff403 ∷ Bx3-41 ∷ Toff403 ∷ CCZ034 ∷ Bx3-41 ∷ Toff324 ∷ CCZ234 ∷ Bx2-301 ∷ []) (CCZ234 ∷ Toff324 ∷ Bx4-301 ∷ Toff324 ∷ CCZ234 ∷ CCZ034 ∷ Toff403 ∷ Bx3-41 ∷ Toff403 ∷ CCZ034 ∷ Bx3-41 ∷ [])
  b1 = at 2 6 (Bx4-301 ∷ []) (refl) ▸
       at 5 1 (CCZ023 ∷ Toff203 ∷ Bx3-21 ∷ Toff203 ∷ CCZ023 ∷ Bx3-21 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 10 1 (CZ12 ∷ []) (refl) ▸
       at 5 6 (CCZ013 ∷ []) (sym (wl0231 (lit c4))) ▸
       at 5 1 (CCZ034 ∷ Toff403 ∷ CZ14 ∷ Toff403 ∷ CCZ034 ∷ CZ14 ∷ []) (wp0214 c4) ▸
       at 7 1 (Bx3-41 ∷ []) (refl) ▸
       at 10 1 (Bx3-41 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ234 ∷ Toff324 ∷ Bx4-301 ∷ Toff324 ∷ CCZ234 ∷ CCZ034 ∷ Toff403 ∷ Bx3-41 ∷ Toff403 ∷ CCZ034 ∷ Bx3-41 ∷ []) (Bx3-4201 ∷ [])
  b2 = at 5 6 (Bx4-301 ∷ []) (refl) ▸
       at 0 6 (Bx3-4201 ∷ []) (refl) ▸ done


-- cQ @03143041: 7 steps
lem-cQ-at03143041 : Ws → ⟪ (CCZ234 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ CCZ234 ∷ []) ⟫ʷ
lem-cQ-at03143041 c4 = run b0
  where
  b0 : Chain (CCZ234 ∷ CCZ013 ∷ []) (CCZ013 ∷ CCZ234 ∷ [])
  b0 = at 0 1 (CS23 ∷ CX42 ∷ CS23⁻ ∷ CX42 ∷ CS34 ∷ []) (wl0675 (lit c4)) ▸
       at 4 2 (CCZ013 ∷ CS34 ∷ []) (sym (wp0185 c4)) ▸
       at 3 2 (CCZ013 ∷ CX42 ∷ []) (lem-comm-CX42-CCZ013 (lit c4)) ▸
       at 2 2 (CCZ013 ∷ CS23⁻ ∷ []) (sym (wl1167 (lit c4))) ▸
       at 1 2 (CCZ013 ∷ CX42 ∷ []) (lem-comm-CX42-CCZ013 (lit c4)) ▸
       at 0 2 (CCZ013 ∷ CS23 ∷ []) (sym (wl0324 (lit c4))) ▸
       at 1 5 (CCZ234 ∷ []) (sym (wl0675 (lit c4))) ▸ done


-- box-tQ @03143041: 13 steps
lem-box-tQ-at03143041 : Ws → ⟪ (Bx3-4201 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ []) ⟫ʷ
lem-box-tQ-at03143041 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-4201 ∷ []) (CCZ234 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ234 ∷ CCZ034 ∷ Toff403 ∷ CZ14 ∷ Toff403 ∷ CCZ034 ∷ CZ14 ∷ [])
  b0 = at 0 1 (CCZ234 ∷ Toff324 ∷ Bx4-301 ∷ Toff324 ∷ CCZ234 ∷ Bx4-301 ∷ []) (refl) ▸
       at 2 1 (CCZ034 ∷ Toff403 ∷ Bx3-41 ∷ Toff403 ∷ CCZ034 ∷ Bx3-41 ∷ []) (refl) ▸
       at 4 1 (CZ14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 2 6 (CCZ013 ∷ []) (sym (wp0214 c4)) ▸
       at 5 1 (CCZ034 ∷ Toff403 ∷ Bx3-41 ∷ Toff403 ∷ CCZ034 ∷ Bx3-41 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 10 1 (CZ14 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ234 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ234 ∷ CCZ034 ∷ Toff403 ∷ CZ14 ∷ Toff403 ∷ CCZ034 ∷ CZ14 ∷ []) (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ [])
  b1 = at 5 6 (CCZ013 ∷ []) (sym (wp0214 c4)) ▸
       at 0 2 (Toff324 ∷ CCZ234 ∷ CZ24 ∷ []) (wl0846 (lit c4)) ▸
       at 2 2 (CCZ013 ∷ CZ24 ∷ []) (lem-comm-CZ24-CCZ013 (lit c4)) ▸
       at 1 2 (CCZ013 ∷ CCZ234 ∷ []) (lem-cQ-at03143041 c4) ▸
       at 2 4 (Toff324 ∷ []) (wl0847 (lit c4)) ▸ done


-- CXbc-box @03143041: 17 steps
lem-CXbc-box-at03143041 : Ws → ⟪ (CX20 ∷ Bx3-4201 ∷ CX20 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4201 ∷ CCZ124 ∷ []) ⟫ʷ
lem-CXbc-box-at03143041 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX20 ∷ Bx3-4201 ∷ CX20 ∷ []) (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CX20 ∷ CCZ123 ∷ CS12 ∷ CX42 ∷ CS12⁻ ∷ CCZ013 ∷ CX42 ∷ CS14 ∷ CX20 ∷ [])
  b0 = at 1 1 (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ []) (lem-box-tQ-at03143041 c4) ▸
       at 0 2 (Toff324 ∷ CX20 ∷ []) (wp1099 c4) ▸
       at 1 2 (CCZ013 ∷ CX20 ∷ CCZ123 ∷ []) (sym (wl1317 (lit c4))) ▸
       at 3 2 (Toff324 ∷ CCZ123 ∷ CCZ124 ∷ []) (wl0445 (lit c4)) ▸
       at 2 2 (Toff324 ∷ CX20 ∷ []) (wp1099 c4) ▸
       at 5 1 (CS12 ∷ CX42 ∷ CS12⁻ ∷ CX42 ∷ CS14 ∷ []) (wl0702 (lit c4)) ▸
       at 9 2 (CCZ013 ∷ CS14 ∷ []) (sym (wp0299 c4)) ▸
       at 8 2 (CCZ013 ∷ CX42 ∷ []) (lem-comm-CX42-CCZ013 (lit c4)) ▸ done

  b1 : Chain (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CX20 ∷ CCZ123 ∷ CS12 ∷ CX42 ∷ CS12⁻ ∷ CCZ013 ∷ CX42 ∷ CS14 ∷ CX20 ∷ []) (Bx3-4201 ∷ CX20 ∷ CCZ124 ∷ CX20 ∷ [])
  b1 = at 7 2 (CCZ013 ∷ CS12⁻ ∷ []) (sym (wl0703 (lit c4))) ▸
       at 6 2 (CCZ013 ∷ CX42 ∷ []) (lem-comm-CX42-CCZ013 (lit c4)) ▸
       at 5 2 (CCZ013 ∷ CS12 ∷ []) (sym (wl0645 (lit c4))) ▸
       at 6 5 (CCZ124 ∷ []) (sym (wl0702 (lit c4))) ▸
       at 4 2 (CCZ013 ∷ CCZ123 ∷ []) (sym (wl0327 (lit c4))) ▸
       at 3 2 (CCZ013 ∷ CX20 ∷ CCZ123 ∷ []) (sym (wl1317 (lit c4))) ▸
       at 4 3 (CX20 ∷ []) (wl1318 (lit c4)) ▸
       at 0 4 (Bx3-4201 ∷ []) (sym (lem-box-tQ-at03143041 c4)) ▸ done

  b2 : Chain (Bx3-4201 ∷ CX20 ∷ CCZ124 ∷ CX20 ∷ []) (Bx3-4201 ∷ CCZ124 ∷ [])
  b2 = at 1 3 (CCZ124 ∷ []) (sym (wp0380 c4)) ▸ done


-- CXcb-box @03143041: 18 steps
lem-CXcb-box-at03143041 : Ws → ⟪ (CX02 ∷ Bx3-4201 ∷ CX02 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4201 ∷ CCZ014 ∷ []) ⟫ʷ
lem-CXcb-box-at03143041 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX02 ∷ Bx3-4201 ∷ CX02 ∷ []) (Toff324 ∷ CCZ013 ∷ CX02 ∷ Toff304 ∷ CS01 ∷ CX40 ∷ Toff324 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ CCZ013 ∷ CX02 ∷ [])
  b0 = at 1 1 (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ []) (lem-box-tQ-at03143041 c4) ▸
       at 0 2 (Toff324 ∷ CX02 ∷ Toff304 ∷ []) (wp1141 c4) ▸
       at 2 2 (CCZ013 ∷ Toff304 ∷ CCZ014 ∷ []) (sym (wp1142 c4)) ▸
       at 1 2 (CCZ013 ∷ CX02 ∷ []) (sym (wl0444 (lit c4))) ▸
       at 4 1 (CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ []) (wp1143 c4) ▸
       at 8 2 (Toff324 ∷ CS14 ∷ []) (wl0543 (lit c4)) ▸
       at 7 2 (Toff324 ∷ CX40 ∷ []) (wp1094 c4) ▸
       at 6 2 (Toff324 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (K ↑ • CCZ • K ↑ • iI)) ▸ done

  b1 : Chain (Toff324 ∷ CCZ013 ∷ CX02 ∷ Toff304 ∷ CS01 ∷ CX40 ∷ Toff324 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ CCZ013 ∷ CX02 ∷ []) (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ CX02 ∷ CCZ014 ∷ CX02 ∷ [])
  b1 = at 5 2 (Toff324 ∷ CX40 ∷ []) (wp1094 c4) ▸
       at 4 2 (Toff324 ∷ CS01 ∷ []) (c₂ (CS) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 5 5 (CCZ014 ∷ []) (sym (wp1143 c4)) ▸
       at 3 2 (Toff324 ∷ Toff304 ∷ []) (wp1144 c4) ▸
       at 2 2 (Toff324 ∷ CX02 ∷ Toff304 ∷ []) (wp1141 c4) ▸
       at 3 3 (CX02 ∷ []) (wp1145 c4) ▸
       at 4 2 (CCZ013 ∷ CCZ014 ∷ []) (sym (wp0394 c4)) ▸
       at 3 2 (CCZ013 ∷ CX02 ∷ []) (sym (wl0444 (lit c4))) ▸ done

  b2 : Chain (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ CX02 ∷ CCZ014 ∷ CX02 ∷ []) (Bx3-4201 ∷ CCZ014 ∷ [])
  b2 = at 0 4 (Bx3-4201 ∷ []) (sym (lem-box-tQ-at03143041 c4)) ▸
       at 1 3 (CCZ014 ∷ []) (sym (wp0378 c4)) ▸ done


-- SWbc-box @03143041: 11 steps
lem-SWbc-box-at03143041 : Ws → ⟪ (Sw02 ∷ Bx3-4201 ∷ Sw02 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4201 ∷ []) ⟫ʷ
lem-SWbc-box-at03143041 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw02 ∷ Bx3-4201 ∷ Sw02 ∷ []) (CX20 ∷ Bx3-4201 ∷ CX20 ∷ CCZ124 ∷ CCZ014 ∷ CCZ124 ∷ CCZ014 ∷ CCZ124 ∷ [])
  b0 = at 0 1 (CX20 ∷ CX02 ∷ CX20 ∷ []) (sym (wl0480 (lit c4))) ▸
       at 4 1 (CX20 ∷ CX02 ∷ CX20 ∷ []) (sym (wl0480 (lit c4))) ▸
       at 2 3 (Bx3-4201 ∷ CCZ124 ∷ []) (lem-CXbc-box-at03143041 c4) ▸
       at 3 2 (CX02 ∷ CCZ014 ∷ CCZ124 ∷ []) (wp0382 c4) ▸
       at 1 3 (Bx3-4201 ∷ CCZ014 ∷ []) (lem-CXcb-box-at03143041 c4) ▸
       at 4 2 (CX20 ∷ CCZ124 ∷ []) (wp0389 c4) ▸
       at 3 2 (CX20 ∷ CCZ124 ∷ CCZ014 ∷ []) (wp0381 c4) ▸
       at 2 2 (CX20 ∷ CCZ124 ∷ CCZ014 ∷ []) (wp0381 c4) ▸ done

  b1 : Chain (CX20 ∷ Bx3-4201 ∷ CX20 ∷ CCZ124 ∷ CCZ014 ∷ CCZ124 ∷ CCZ014 ∷ CCZ124 ∷ []) (Bx3-4201 ∷ [])
  b1 = at 3 5 (CCZ124 ∷ []) (wp0390 c4) ▸
       at 0 3 (Bx3-4201 ∷ CCZ124 ∷ []) (lem-CXbc-box-at03143041 c4) ▸
       at 1 2 [] (wl0263 (lit c4)) ▸ done


-- nat-SWbc @03143041: 23 steps
lem-nat-SWbc-at03143041 : Ws → ⟪ (Sw02 ∷ Bx3-4201 ∷ Sw02 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4021 ∷ []) ⟫ʷ
lem-nat-SWbc-at03143041 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw02 ∷ Bx3-4201 ∷ Sw02 ∷ []) (CCZ034 ∷ Toff304 ∷ CCZ234 ∷ Toff423 ∷ Bx3-41 ∷ Toff423 ∷ Sw02 ∷ CCZ034 ∷ Bx3-41 ∷ Toff324 ∷ CCZ234 ∷ Bx4-301 ∷ Sw02 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff324 ∷ Bx4-301 ∷ Toff324 ∷ CCZ234 ∷ Bx4-301 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw02 ∷ []) (sym (wp1146 c4)) ▸
       at 1 2 (Toff304 ∷ Sw02 ∷ []) (wp1147 c4) ▸
       at 3 1 (CCZ034 ∷ Toff403 ∷ Bx3-41 ∷ Toff403 ∷ CCZ034 ∷ Bx3-41 ∷ []) (refl) ▸
       at 2 2 (CCZ234 ∷ Sw02 ∷ []) (sym (wp1148 c4)) ▸
       at 3 2 (Toff423 ∷ Sw02 ∷ []) (wp1149 c4) ▸
       at 4 2 (Bx3-41 ∷ Sw02 ∷ []) (lem-comm-SWAP02-BOX⟨3·41⟩ (lit c4)) ▸
       at 5 2 (Toff423 ∷ Sw02 ∷ []) (wp1149 c4) ▸ done

  b1 : Chain (CCZ034 ∷ Toff304 ∷ CCZ234 ∷ Toff423 ∷ Bx3-41 ∷ Toff423 ∷ Sw02 ∷ CCZ034 ∷ Bx3-41 ∷ Toff324 ∷ CCZ234 ∷ Bx4-301 ∷ Sw02 ∷ []) (CCZ034 ∷ Toff304 ∷ CCZ234 ∷ Toff423 ∷ Bx3-41 ∷ Toff423 ∷ CCZ234 ∷ Bx3-41 ∷ Toff304 ∷ CCZ034 ∷ CCZ234 ∷ Toff423 ∷ Bx3-41 ∷ Sw02 ∷ Toff403 ∷ CCZ034 ∷ Bx3-41 ∷ Sw02 ∷ [])
  b1 = at 6 2 (CCZ234 ∷ Sw02 ∷ []) (sym (wp1148 c4)) ▸
       at 7 2 (Bx3-41 ∷ Sw02 ∷ []) (lem-comm-SWAP02-BOX⟨3·41⟩ (lit c4)) ▸
       at 8 2 (Toff304 ∷ Sw02 ∷ []) (wp1147 c4) ▸
       at 9 2 (CCZ034 ∷ Sw02 ∷ []) (sym (wp1146 c4)) ▸
       at 11 1 (CCZ034 ∷ Toff403 ∷ Bx3-41 ∷ Toff403 ∷ CCZ034 ∷ Bx3-41 ∷ []) (refl) ▸
       at 10 2 (CCZ234 ∷ Sw02 ∷ []) (sym (wp1148 c4)) ▸
       at 11 2 (Toff423 ∷ Sw02 ∷ []) (wp1149 c4) ▸
       at 12 2 (Bx3-41 ∷ Sw02 ∷ []) (lem-comm-SWAP02-BOX⟨3·41⟩ (lit c4)) ▸ done

  b2 : Chain (CCZ034 ∷ Toff304 ∷ CCZ234 ∷ Toff423 ∷ Bx3-41 ∷ Toff423 ∷ CCZ234 ∷ Bx3-41 ∷ Toff304 ∷ CCZ034 ∷ CCZ234 ∷ Toff423 ∷ Bx3-41 ∷ Sw02 ∷ Toff403 ∷ CCZ034 ∷ Bx3-41 ∷ Sw02 ∷ []) (Bx3-4021 ∷ [])
  b2 = at 13 2 (Toff423 ∷ Sw02 ∷ []) (wp1149 c4) ▸
       at 14 2 (CCZ234 ∷ Sw02 ∷ []) (sym (wp1148 c4)) ▸
       at 15 2 (Bx3-41 ∷ Sw02 ∷ []) (lem-comm-SWAP02-BOX⟨3·41⟩ (lit c4)) ▸
       at 16 2 [] (wl0485 (lit c4)) ▸
       at 2 6 (Bx4-321 ∷ []) (refl) ▸
       at 5 6 (Bx4-321 ∷ []) (refl) ▸
       at 0 6 (Bx3-4021 ∷ []) (refl) ▸ done


-- sym-bc @03143041: 2 steps
lem-sym-bc-at03143041 : Ws → ⟪ (Bx3-4201 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4021 ∷ []) ⟫ʷ
lem-sym-bc-at03143041 c4 = run b0
  where
  b0 : Chain (Bx3-4201 ∷ []) (Bx3-4021 ∷ [])
  b0 = at 0 1 (Sw02 ∷ Bx3-4201 ∷ Sw02 ∷ []) (sym (lem-SWbc-box-at03143041 c4)) ▸
       at 0 3 (Bx3-4021 ∷ []) (lem-nat-SWbc-at03143041 c4) ▸ done


-- box-perm-4132 @03102132: 3 steps
lem-box-perm-4132-at03102132 : Ws → ⟪ (Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4021 ∷ []) ⟫ʷ
lem-box-perm-4132-at03102132 c4 = run b0
  where
  b0 : Chain (Bx3-0124 ∷ []) (Bx3-4021 ∷ [])
  b0 = at 0 1 (Bx3-2401 ∷ []) (lem-pairs-at03102132 c4) ▸
       at 0 1 (Bx3-4201 ∷ []) (lem-sym-ab-at0312243041 c4) ▸
       at 0 1 (Bx3-4021 ∷ []) (lem-sym-bc-at03143041 c4) ▸ done


-- cQ @0314203241: 7 steps
lem-cQ-at0314203241 : Ws → ⟪ (CCZ034 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CCZ034 ∷ []) ⟫ʷ
lem-cQ-at0314203241 c4 = run b0
  where
  b0 : Chain (CCZ034 ∷ CCZ123 ∷ []) (CCZ123 ∷ CCZ034 ∷ [])
  b0 = at 0 1 (CS03 ∷ CX40 ∷ CS03⁻ ∷ CX40 ∷ CS34 ∷ []) (wp0320 c4) ▸
       at 4 2 (CCZ123 ∷ CS34 ∷ []) (sym (wl0492 (lit c4))) ▸
       at 3 2 (CCZ123 ∷ CX40 ∷ []) (lem-comm-CX40-CCZ123 (lit c4)) ▸
       at 2 2 (CCZ123 ∷ CS03⁻ ∷ []) (sym (wl0495 (lit c4))) ▸
       at 1 2 (CCZ123 ∷ CX40 ∷ []) (lem-comm-CX40-CCZ123 (lit c4)) ▸
       at 0 2 (CCZ123 ∷ CS03 ∷ []) (sym (wl0490 (lit c4))) ▸
       at 1 5 (CCZ034 ∷ []) (sym (wp0320 c4)) ▸ done


-- box-tQ @0314203241: 13 steps
lem-box-tQ-at0314203241 : Ws → ⟪ (Bx3-4021 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) ⟫ʷ
lem-box-tQ-at0314203241 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-4021 ∷ []) (CCZ034 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ034 ∷ CCZ234 ∷ Toff423 ∷ CZ14 ∷ Toff423 ∷ CCZ234 ∷ CZ14 ∷ [])
  b0 = at 0 1 (CCZ034 ∷ Toff304 ∷ Bx4-321 ∷ Toff304 ∷ CCZ034 ∷ Bx4-321 ∷ []) (refl) ▸
       at 2 1 (CCZ234 ∷ Toff423 ∷ Bx3-41 ∷ Toff423 ∷ CCZ234 ∷ Bx3-41 ∷ []) (refl) ▸
       at 4 1 (CZ14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 2 6 (CCZ123 ∷ []) (sym (wl1319 (lit c4))) ▸
       at 5 1 (CCZ234 ∷ Toff423 ∷ Bx3-41 ∷ Toff423 ∷ CCZ234 ∷ Bx3-41 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 10 1 (CZ14 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ034 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ034 ∷ CCZ234 ∷ Toff423 ∷ CZ14 ∷ Toff423 ∷ CCZ234 ∷ CZ14 ∷ []) (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ [])
  b1 = at 5 6 (CCZ123 ∷ []) (sym (wl1319 (lit c4))) ▸
       at 0 2 (Toff304 ∷ CCZ034 ∷ CZ04 ∷ []) (wp0353 c4) ▸
       at 2 2 (CCZ123 ∷ CZ04 ∷ []) (lem-comm-CZ04-CCZ123 (lit c4)) ▸
       at 1 2 (CCZ123 ∷ CCZ034 ∷ []) (lem-cQ-at0314203241 c4) ▸
       at 2 4 (Toff304 ∷ []) (wp0354 c4) ▸ done


-- cQ @02142041: 7 steps
lem-cQ-at02142041 : Ws → ⟪ (CCZ024 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CCZ024 ∷ []) ⟫ʷ
lem-cQ-at02142041 c4 = run b0
  where
  b0 : Chain (CCZ024 ∷ CCZ123 ∷ []) (CCZ123 ∷ CCZ024 ∷ [])
  b0 = at 0 1 (CS02 ∷ CX40 ∷ CS02⁻ ∷ CX40 ∷ CS24 ∷ []) (wp0496 c4) ▸
       at 4 2 (CCZ123 ∷ CS24 ∷ []) (sym (wl0173 (lit c4))) ▸
       at 3 2 (CCZ123 ∷ CX40 ∷ []) (lem-comm-CX40-CCZ123 (lit c4)) ▸
       at 2 2 (CCZ123 ∷ CS02⁻ ∷ []) (sym (wl0611 (lit c4))) ▸
       at 1 2 (CCZ123 ∷ CX40 ∷ []) (lem-comm-CX40-CCZ123 (lit c4)) ▸
       at 0 2 (CCZ123 ∷ CS02 ∷ []) (sym (wl0171 (lit c4))) ▸
       at 1 5 (CCZ024 ∷ []) (sym (wp0496 c4)) ▸ done


-- box-tQ @02142041: 13 steps
lem-box-tQ-at02142041 : Ws → ⟪ (Bx2-4031 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) ⟫ʷ
lem-box-tQ-at02142041 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx2-4031 ∷ []) (CCZ024 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ024 ∷ CCZ234 ∷ Toff423 ∷ CZ14 ∷ Toff423 ∷ CCZ234 ∷ CZ14 ∷ [])
  b0 = at 0 1 (CCZ024 ∷ Toff204 ∷ Bx4-231 ∷ Toff204 ∷ CCZ024 ∷ Bx4-231 ∷ []) (refl) ▸
       at 2 1 (CCZ234 ∷ Toff423 ∷ Bx2-41 ∷ Toff423 ∷ CCZ234 ∷ Bx2-41 ∷ []) (refl) ▸
       at 4 1 (CZ14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 2 6 (CCZ123 ∷ []) (sym (wl1319 (lit c4))) ▸
       at 5 1 (CCZ234 ∷ Toff423 ∷ Bx2-41 ∷ Toff423 ∷ CCZ234 ∷ Bx2-41 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 10 1 (CZ14 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ024 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ024 ∷ CCZ234 ∷ Toff423 ∷ CZ14 ∷ Toff423 ∷ CCZ234 ∷ CZ14 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ [])
  b1 = at 5 6 (CCZ123 ∷ []) (sym (wl1319 (lit c4))) ▸
       at 0 2 (Toff204 ∷ CCZ024 ∷ CZ04 ∷ []) (wp0025 c4) ▸
       at 2 2 (CCZ123 ∷ CZ04 ∷ []) (lem-comm-CZ04-CCZ123 (lit c4)) ▸
       at 1 2 (CCZ123 ∷ CCZ024 ∷ []) (lem-cQ-at02142041 c4) ▸
       at 2 4 (Toff204 ∷ []) (wp0026 c4) ▸ done


-- CXbc-box @02142041: 17 steps
lem-CXbc-box-at02142041 : Ws → ⟪ (CX03 ∷ Bx2-4031 ∷ CX03 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4031 ∷ CCZ014 ∷ []) ⟫ʷ
lem-CXbc-box-at02142041 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX03 ∷ Bx2-4031 ∷ CX03 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CX03 ∷ CCZ012 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CCZ123 ∷ CX40 ∷ CS14 ∷ CX03 ∷ [])
  b0 = at 1 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-box-tQ-at02142041 c4) ▸
       at 0 2 (Toff204 ∷ CX03 ∷ []) (wp0949 c4) ▸
       at 1 2 (CCZ123 ∷ CX03 ∷ CCZ012 ∷ []) (sym (wl1320 (lit c4))) ▸
       at 3 2 (Toff204 ∷ CCZ012 ∷ CCZ014 ∷ []) (wp1150 c4) ▸
       at 2 2 (Toff204 ∷ CX03 ∷ []) (wp0949 c4) ▸
       at 5 1 (CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ []) (wp1143 c4) ▸
       at 9 2 (CCZ123 ∷ CS14 ∷ []) (sym (wl0765 (lit c4))) ▸
       at 8 2 (CCZ123 ∷ CX40 ∷ []) (lem-comm-CX40-CCZ123 (lit c4)) ▸ done

  b1 : Chain (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CX03 ∷ CCZ012 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CCZ123 ∷ CX40 ∷ CS14 ∷ CX03 ∷ []) (Bx2-4031 ∷ CX03 ∷ CCZ014 ∷ CX03 ∷ [])
  b1 = at 7 2 (CCZ123 ∷ CS01⁻ ∷ []) (sym (wl1321 (lit c4))) ▸
       at 6 2 (CCZ123 ∷ CX40 ∷ []) (lem-comm-CX40-CCZ123 (lit c4)) ▸
       at 5 2 (CCZ123 ∷ CS01 ∷ []) (sym (wl0763 (lit c4))) ▸
       at 6 5 (CCZ014 ∷ []) (sym (wp1143 c4)) ▸
       at 4 2 (CCZ123 ∷ CCZ012 ∷ []) (wl0298 (lit c4)) ▸
       at 3 2 (CCZ123 ∷ CX03 ∷ CCZ012 ∷ []) (sym (wl1320 (lit c4))) ▸
       at 4 3 (CX03 ∷ []) (wl1322 (lit c4)) ▸
       at 0 4 (Bx2-4031 ∷ []) (sym (lem-box-tQ-at02142041 c4)) ▸ done

  b2 : Chain (Bx2-4031 ∷ CX03 ∷ CCZ014 ∷ CX03 ∷ []) (Bx2-4031 ∷ CCZ014 ∷ [])
  b2 = at 1 3 (CCZ014 ∷ []) (sym (wp0761 c4)) ▸ done


-- CXcb-box @02142041: 18 steps
lem-CXcb-box-at02142041 : Ws → ⟪ (CX30 ∷ Bx2-4031 ∷ CX30 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4031 ∷ CCZ134 ∷ []) ⟫ʷ
lem-CXcb-box-at02142041 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX30 ∷ Bx2-4031 ∷ CX30 ∷ []) (Toff204 ∷ CCZ123 ∷ CX30 ∷ Toff234 ∷ CS13 ∷ CX43 ∷ Toff204 ∷ CS13⁻ ∷ CX43 ∷ CS14 ∷ CCZ123 ∷ CX30 ∷ [])
  b0 = at 1 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-box-tQ-at02142041 c4) ▸
       at 0 2 (Toff204 ∷ CX30 ∷ Toff234 ∷ []) (wp1151 c4) ▸
       at 2 2 (CCZ123 ∷ Toff234 ∷ CCZ134 ∷ []) (sym (wl1323 (lit c4))) ▸
       at 1 2 (CCZ123 ∷ CX30 ∷ []) (sym (wl1324 (lit c4))) ▸
       at 4 1 (CS13 ∷ CX43 ∷ CS13⁻ ∷ CX43 ∷ CS14 ∷ []) (wl0707 (lit c4)) ▸
       at 8 2 (Toff204 ∷ CS14 ∷ []) (wp1152 c4) ▸
       at 7 2 (Toff204 ∷ CX43 ∷ []) (wp0945 c4) ▸
       at 6 2 (Toff204 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-TOFF204 (lit c4)) ▸ done

  b1 : Chain (Toff204 ∷ CCZ123 ∷ CX30 ∷ Toff234 ∷ CS13 ∷ CX43 ∷ Toff204 ∷ CS13⁻ ∷ CX43 ∷ CS14 ∷ CCZ123 ∷ CX30 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ CX30 ∷ CCZ134 ∷ CX30 ∷ [])
  b1 = at 5 2 (Toff204 ∷ CX43 ∷ []) (wp0945 c4) ▸
       at 4 2 (Toff204 ∷ CS13 ∷ []) (lem-comm-CS13-TOFF204 (lit c4)) ▸
       at 5 5 (CCZ134 ∷ []) (sym (wl0707 (lit c4))) ▸
       at 3 2 (Toff204 ∷ Toff234 ∷ []) (sym (wp1153 c4)) ▸
       at 2 2 (Toff204 ∷ CX30 ∷ Toff234 ∷ []) (wp1151 c4) ▸
       at 3 3 (CX30 ∷ []) (wp1154 c4) ▸
       at 4 2 (CCZ123 ∷ CCZ134 ∷ []) (sym (wl0618 (lit c4))) ▸
       at 3 2 (CCZ123 ∷ CX30 ∷ []) (sym (wl1324 (lit c4))) ▸ done

  b2 : Chain (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ CX30 ∷ CCZ134 ∷ CX30 ∷ []) (Bx2-4031 ∷ CCZ134 ∷ [])
  b2 = at 0 4 (Bx2-4031 ∷ []) (sym (lem-box-tQ-at02142041 c4)) ▸
       at 1 3 (CCZ134 ∷ []) (sym (wp0759 c4)) ▸ done


-- SWbc-box @02142041: 11 steps
lem-SWbc-box-at02142041 : Ws → ⟪ (Sw03 ∷ Bx2-4031 ∷ Sw03 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4031 ∷ []) ⟫ʷ
lem-SWbc-box-at02142041 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw03 ∷ Bx2-4031 ∷ Sw03 ∷ []) (CX03 ∷ Bx2-4031 ∷ CX03 ∷ CCZ014 ∷ CCZ134 ∷ CCZ014 ∷ CCZ134 ∷ CCZ014 ∷ [])
  b0 = at 0 1 (CX03 ∷ CX30 ∷ CX03 ∷ []) (sym (wl0961 (lit c4))) ▸
       at 4 1 (CX03 ∷ CX30 ∷ CX03 ∷ []) (sym (wl0961 (lit c4))) ▸
       at 2 3 (Bx2-4031 ∷ CCZ014 ∷ []) (lem-CXbc-box-at02142041 c4) ▸
       at 3 2 (CX30 ∷ CCZ134 ∷ CCZ014 ∷ []) (wp0763 c4) ▸
       at 1 3 (Bx2-4031 ∷ CCZ134 ∷ []) (lem-CXcb-box-at02142041 c4) ▸
       at 4 2 (CX03 ∷ CCZ014 ∷ []) (wp0778 c4) ▸
       at 3 2 (CX03 ∷ CCZ014 ∷ CCZ134 ∷ []) (wp0762 c4) ▸
       at 2 2 (CX03 ∷ CCZ014 ∷ CCZ134 ∷ []) (wp0762 c4) ▸ done

  b1 : Chain (CX03 ∷ Bx2-4031 ∷ CX03 ∷ CCZ014 ∷ CCZ134 ∷ CCZ014 ∷ CCZ134 ∷ CCZ014 ∷ []) (Bx2-4031 ∷ [])
  b1 = at 3 5 (CCZ014 ∷ []) (wp0779 c4) ▸
       at 0 3 (Bx2-4031 ∷ CCZ014 ∷ []) (lem-CXbc-box-at02142041 c4) ▸
       at 1 2 [] (wp0161 c4) ▸ done


-- nat-SWbc @02142041: 23 steps
lem-nat-SWbc-at02142041 : Ws → ⟪ (Sw03 ∷ Bx2-4031 ∷ Sw03 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4301 ∷ []) ⟫ʷ
lem-nat-SWbc-at02142041 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw03 ∷ Bx2-4031 ∷ Sw03 ∷ []) (CCZ234 ∷ Toff234 ∷ CCZ024 ∷ Toff402 ∷ Bx2-41 ∷ Toff402 ∷ Sw03 ∷ CCZ234 ∷ Bx2-41 ∷ Toff204 ∷ CCZ024 ∷ Bx4-231 ∷ Sw03 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff204 ∷ Bx4-231 ∷ Toff204 ∷ CCZ024 ∷ Bx4-231 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw03 ∷ []) (sym (wp1155 c4)) ▸
       at 1 2 (Toff234 ∷ Sw03 ∷ []) (wp1156 c4) ▸
       at 3 1 (CCZ234 ∷ Toff423 ∷ Bx2-41 ∷ Toff423 ∷ CCZ234 ∷ Bx2-41 ∷ []) (refl) ▸
       at 2 2 (CCZ024 ∷ Sw03 ∷ []) (sym (wp1157 c4)) ▸
       at 3 2 (Toff402 ∷ Sw03 ∷ []) (wp1158 c4) ▸
       at 4 2 (Bx2-41 ∷ Sw03 ∷ []) (lem-comm-SWAP03-BOX⟨2·41⟩ (lit c4)) ▸
       at 5 2 (Toff402 ∷ Sw03 ∷ []) (wp1158 c4) ▸ done

  b1 : Chain (CCZ234 ∷ Toff234 ∷ CCZ024 ∷ Toff402 ∷ Bx2-41 ∷ Toff402 ∷ Sw03 ∷ CCZ234 ∷ Bx2-41 ∷ Toff204 ∷ CCZ024 ∷ Bx4-231 ∷ Sw03 ∷ []) (CCZ234 ∷ Toff234 ∷ CCZ024 ∷ Toff402 ∷ Bx2-41 ∷ Toff402 ∷ CCZ024 ∷ Bx2-41 ∷ Toff234 ∷ CCZ234 ∷ CCZ024 ∷ Toff402 ∷ Bx2-41 ∷ Sw03 ∷ Toff423 ∷ CCZ234 ∷ Bx2-41 ∷ Sw03 ∷ [])
  b1 = at 6 2 (CCZ024 ∷ Sw03 ∷ []) (sym (wp1157 c4)) ▸
       at 7 2 (Bx2-41 ∷ Sw03 ∷ []) (lem-comm-SWAP03-BOX⟨2·41⟩ (lit c4)) ▸
       at 8 2 (Toff234 ∷ Sw03 ∷ []) (wp1156 c4) ▸
       at 9 2 (CCZ234 ∷ Sw03 ∷ []) (sym (wp1155 c4)) ▸
       at 11 1 (CCZ234 ∷ Toff423 ∷ Bx2-41 ∷ Toff423 ∷ CCZ234 ∷ Bx2-41 ∷ []) (refl) ▸
       at 10 2 (CCZ024 ∷ Sw03 ∷ []) (sym (wp1157 c4)) ▸
       at 11 2 (Toff402 ∷ Sw03 ∷ []) (wp1158 c4) ▸
       at 12 2 (Bx2-41 ∷ Sw03 ∷ []) (lem-comm-SWAP03-BOX⟨2·41⟩ (lit c4)) ▸ done

  b2 : Chain (CCZ234 ∷ Toff234 ∷ CCZ024 ∷ Toff402 ∷ Bx2-41 ∷ Toff402 ∷ CCZ024 ∷ Bx2-41 ∷ Toff234 ∷ CCZ234 ∷ CCZ024 ∷ Toff402 ∷ Bx2-41 ∷ Sw03 ∷ Toff423 ∷ CCZ234 ∷ Bx2-41 ∷ Sw03 ∷ []) (Bx2-4301 ∷ [])
  b2 = at 13 2 (Toff402 ∷ Sw03 ∷ []) (wp1158 c4) ▸
       at 14 2 (CCZ024 ∷ Sw03 ∷ []) (sym (wp1157 c4)) ▸
       at 15 2 (Bx2-41 ∷ Sw03 ∷ []) (lem-comm-SWAP03-BOX⟨2·41⟩ (lit c4)) ▸
       at 16 2 [] (wl0928 (lit c4)) ▸
       at 2 6 (Bx4-201 ∷ []) (refl) ▸
       at 5 6 (Bx4-201 ∷ []) (refl) ▸
       at 0 6 (Bx2-4301 ∷ []) (refl) ▸ done


-- sym-bc @02142041: 2 steps
lem-sym-bc-at02142041 : Ws → ⟪ (Bx2-4031 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4301 ∷ []) ⟫ʷ
lem-sym-bc-at02142041 c4 = run b0
  where
  b0 : Chain (Bx2-4031 ∷ []) (Bx2-4301 ∷ [])
  b0 = at 0 1 (Sw03 ∷ Bx2-4031 ∷ Sw03 ∷ []) (sym (lem-SWbc-box-at02142041 c4)) ▸
       at 0 3 (Bx2-4301 ∷ []) (lem-nat-SWbc-at02142041 c4) ▸ done


-- box-perm-1324 @02142041: 1 steps
lem-box-perm-1324-at02142041 : Ws → ⟪ (Bx2-4031 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4301 ∷ []) ⟫ʷ
lem-box-perm-1324-at02142041 c4 = run b0
  where
  b0 : Chain (Bx2-4031 ∷ []) (Bx2-4301 ∷ [])
  b0 = at 0 1 (Bx2-4301 ∷ []) (lem-sym-bc-at02142041 c4) ▸ done


-- cQ @0214233041: 7 steps
lem-cQ-at0214233041 : Ws → ⟪ (CCZ234 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ CCZ234 ∷ []) ⟫ʷ
lem-cQ-at0214233041 c4 = run b0
  where
  b0 : Chain (CCZ234 ∷ CCZ012 ∷ []) (CCZ012 ∷ CCZ234 ∷ [])
  b0 = at 0 1 (CS23 ∷ CX43 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ []) (wl0330 (lit c4)) ▸
       at 4 2 (CCZ012 ∷ CS24 ∷ []) (sym (wp0141 c4)) ▸
       at 3 2 (CCZ012 ∷ CX43 ∷ []) (sym (c₃ (CCZ) (CX₁₀))) ▸
       at 2 2 (CCZ012 ∷ CS23⁻ ∷ []) (sym (wl0331 (lit c4))) ▸
       at 1 2 (CCZ012 ∷ CX43 ∷ []) (sym (c₃ (CCZ) (CX₁₀))) ▸
       at 0 2 (CCZ012 ∷ CS23 ∷ []) (sym (wl0294 (lit c4))) ▸
       at 1 5 (CCZ234 ∷ []) (sym (wl0330 (lit c4))) ▸ done


-- tP @0214233041: 7 steps
lem-tP-at0214233041 : Ws → ⟪ (Toff234 ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ Toff234 ∷ []) ⟫ʷ
lem-tP-at0214233041 c4 = run b0
  where
  b0 : Chain (Toff234 ∷ Toff201 ∷ []) (Toff201 ∷ Toff234 ∷ [])
  b0 = at 0 1 (K2 ∷ CCZ234 ∷ K2⁻ ∷ []) (sym (wl0417 (lit c4))) ▸
       at 3 1 (K2 ∷ CCZ012 ∷ K2⁻ ∷ []) (sym (wl0416 (lit c4))) ▸
       at 2 2 [] (wl0175 (lit c4)) ▸
       at 1 2 (CCZ012 ∷ CCZ234 ∷ []) (lem-cQ-at0214233041 c4) ▸
       at 2 0 (K2⁻ ∷ K2 ∷ []) (sym (wl0175 (lit c4))) ▸
       at 0 3 (Toff201 ∷ []) (wl0416 (lit c4)) ▸
       at 1 3 (Toff234 ∷ []) (wl0417 (lit c4)) ▸ done


-- VPQ @0214233041: 14 steps
lem-VPQ-at0214233041 : Ws → ⟪ (Toff234 ∷ CCZ234 ∷ Toff201 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CCZ012 ∷ Toff234 ∷ CCZ234 ∷ []) ⟫ʷ
lem-VPQ-at0214233041 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff234 ∷ CCZ234 ∷ Toff201 ∷ CCZ012 ∷ []) (CS01⁻ ∷ CS34⁻ ∷ S2 ∷ Toff201 ∷ Toff234 ∷ S2⁻ ∷ [])
  b0 = at 0 2 (CS34⁻ ∷ S2 ∷ Toff234 ∷ S2⁻ ∷ []) (sym (wl0419 (lit c4))) ▸
       at 4 2 (CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ []) (sym (wl0418 (lit c4))) ▸
       at 3 2 (CS01⁻ ∷ S2⁻ ∷ []) (sym (c₂ (CS • CS • CS) (S • S • S))) ▸
       at 2 2 (CS01⁻ ∷ Toff234 ∷ []) (sym (c₂ (CS • CS • CS) (Toff))) ▸
       at 1 2 (CS01⁻ ∷ S2 ∷ []) (sym (c₂ (CS • CS • CS) (S))) ▸
       at 0 2 (CS01⁻ ∷ CS34⁻ ∷ []) (sym (c₂ (CS • CS • CS) ((CS • CS • CS) ↑))) ▸
       at 4 2 [] (wl0179 (lit c4)) ▸
       at 3 2 (Toff201 ∷ Toff234 ∷ []) (lem-tP-at0214233041 c4) ▸ done

  b1 : Chain (CS01⁻ ∷ CS34⁻ ∷ S2 ∷ Toff201 ∷ Toff234 ∷ S2⁻ ∷ []) (Toff201 ∷ CCZ012 ∷ Toff234 ∷ CCZ234 ∷ [])
  b1 = at 4 0 (S2⁻ ∷ S2 ∷ []) (sym (wl0179 (lit c4))) ▸
       at 1 2 (S2 ∷ CS34⁻ ∷ []) (sym (c₃ (S ↑ ↑) (CS • CS • CS))) ▸
       at 2 2 (Toff201 ∷ CS34⁻ ∷ []) (sym (c₃ (Toffᵗ) (CS • CS • CS))) ▸
       at 3 2 (S2⁻ ∷ CS34⁻ ∷ []) (sym (c₃ ((S • S • S) ↑ ↑) (CS • CS • CS))) ▸
       at 0 4 (Toff201 ∷ CCZ012 ∷ []) (wl0418 (lit c4)) ▸
       at 2 4 (Toff234 ∷ CCZ234 ∷ []) (wl0419 (lit c4)) ▸ done


-- QVQ @0214233041: 3 steps
lem-QVQ-at0214233041 : Ws → ⟪ (CCZ012 ∷ Toff234 ∷ CCZ234 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ Toff234 ∷ CCZ234 ∷ Toff201 ∷ []) ⟫ʷ
lem-QVQ-at0214233041 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Toff234 ∷ CCZ234 ∷ CCZ012 ∷ []) (Toff201 ∷ Toff234 ∷ CCZ234 ∷ Toff201 ∷ [])
  b0 = at 0 0 (Toff201 ∷ Toff201 ∷ []) (sym (wl0421 (lit c4))) ▸
       at 1 4 (Toff234 ∷ CCZ234 ∷ Toff201 ∷ CCZ012 ∷ []) (sym (lem-VPQ-at0214233041 c4)) ▸
       at 4 2 [] (wl0341 (lit c4)) ▸ done


-- box-cP @0214233041: 12 steps
lem-box-cP-at0214233041 : Ws → ⟪ (Bx2-4301 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ []) ⟫ʷ
lem-box-cP-at0214233041 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx2-4301 ∷ []) (CCZ234 ∷ Toff234 ∷ CCZ012 ∷ Toff234 ∷ CCZ234 ∷ CCZ024 ∷ Toff402 ∷ CZ14 ∷ Toff402 ∷ CCZ024 ∷ CZ14 ∷ [])
  b0 = at 0 1 (CCZ234 ∷ Toff234 ∷ Bx4-201 ∷ Toff234 ∷ CCZ234 ∷ Bx4-201 ∷ []) (refl) ▸
       at 2 1 (CCZ024 ∷ Toff402 ∷ Bx2-41 ∷ Toff402 ∷ CCZ024 ∷ Bx2-41 ∷ []) (refl) ▸
       at 4 1 (CZ14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 2 6 (CCZ012 ∷ []) (sym (wp0162 c4)) ▸
       at 5 1 (CCZ024 ∷ Toff402 ∷ Bx2-41 ∷ Toff402 ∷ CCZ024 ∷ Bx2-41 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 10 1 (CZ14 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ234 ∷ Toff234 ∷ CCZ012 ∷ Toff234 ∷ CCZ234 ∷ CCZ024 ∷ Toff402 ∷ CZ14 ∷ Toff402 ∷ CCZ024 ∷ CZ14 ∷ []) (CCZ234 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ [])
  b1 = at 5 6 (CCZ012 ∷ []) (sym (wp0162 c4)) ▸
       at 2 4 (Toff201 ∷ Toff234 ∷ CCZ234 ∷ Toff201 ∷ []) (lem-QVQ-at0214233041 c4) ▸
       at 1 2 (Toff201 ∷ Toff234 ∷ []) (lem-tP-at0214233041 c4) ▸
       at 2 2 [] (wl0420 (lit c4)) ▸ done


-- sym-ab @0214233041: 18 steps
lem-sym-ab-at0214233041 : Ws → ⟪ (Bx2-4301 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3401 ∷ []) ⟫ʷ
lem-sym-ab-at0214233041 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx2-4301 ∷ []) (CCZ234 ∷ Toff234 ∷ CCZ023 ∷ Toff302 ∷ Bx2-31 ∷ Toff302 ∷ CCZ023 ∷ Bx2-31 ∷ Toff234 ∷ CCZ234 ∷ Bx4-201 ∷ [])
  b0 = at 0 1 (CCZ234 ∷ Toff234 ∷ Bx4-201 ∷ Toff234 ∷ CCZ234 ∷ Bx4-201 ∷ []) (refl) ▸
       at 2 1 (CCZ024 ∷ Toff402 ∷ Bx2-41 ∷ Toff402 ∷ CCZ024 ∷ Bx2-41 ∷ []) (refl) ▸
       at 4 1 (CZ14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 2 6 (CCZ012 ∷ []) (sym (wp0162 c4)) ▸
       at 2 1 (CCZ023 ∷ Toff302 ∷ CZ13 ∷ Toff302 ∷ CCZ023 ∷ CZ13 ∷ []) (wl0288 (lit c4)) ▸
       at 4 1 (Bx2-31 ∷ []) (refl) ▸
       at 7 1 (Bx2-31 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ234 ∷ Toff234 ∷ CCZ023 ∷ Toff302 ∷ Bx2-31 ∷ Toff302 ∷ CCZ023 ∷ Bx2-31 ∷ Toff234 ∷ CCZ234 ∷ Bx4-201 ∷ []) (CCZ234 ∷ Toff234 ∷ Bx3-201 ∷ Toff234 ∷ CCZ234 ∷ CCZ023 ∷ Toff302 ∷ Bx2-31 ∷ Toff302 ∷ CCZ023 ∷ Bx2-31 ∷ [])
  b1 = at 2 6 (Bx3-201 ∷ []) (refl) ▸
       at 5 1 (CCZ024 ∷ Toff402 ∷ Bx2-41 ∷ Toff402 ∷ CCZ024 ∷ Bx2-41 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 10 1 (CZ14 ∷ []) (refl) ▸
       at 5 6 (CCZ012 ∷ []) (sym (wp0162 c4)) ▸
       at 5 1 (CCZ023 ∷ Toff302 ∷ CZ13 ∷ Toff302 ∷ CCZ023 ∷ CZ13 ∷ []) (wl0288 (lit c4)) ▸
       at 7 1 (Bx2-31 ∷ []) (refl) ▸
       at 10 1 (Bx2-31 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ234 ∷ Toff234 ∷ Bx3-201 ∷ Toff234 ∷ CCZ234 ∷ CCZ023 ∷ Toff302 ∷ Bx2-31 ∷ Toff302 ∷ CCZ023 ∷ Bx2-31 ∷ []) (Bx2-3401 ∷ [])
  b2 = at 5 6 (Bx3-201 ∷ []) (refl) ▸
       at 0 6 (Bx2-3401 ∷ []) (refl) ▸ done


-- box-perm-3124 @02142041: 2 steps
lem-box-perm-3124-at02142041 : Ws → ⟪ (Bx2-4031 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3401 ∷ []) ⟫ʷ
lem-box-perm-3124-at02142041 c4 = run b0
  where
  b0 : Chain (Bx2-4031 ∷ []) (Bx2-3401 ∷ [])
  b0 = at 0 1 (Bx2-4301 ∷ []) (lem-sym-bc-at02142041 c4) ▸
       at 0 1 (Bx2-3401 ∷ []) (lem-sym-ab-at0214233041 c4) ▸ done


-- CXbc-box @0314203241: 17 steps
lem-CXbc-box-at0314203241 : Ws → ⟪ (CX02 ∷ Bx3-4021 ∷ CX02 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4021 ∷ CCZ014 ∷ []) ⟫ʷ
lem-CXbc-box-at0314203241 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX02 ∷ Bx3-4021 ∷ CX02 ∷ []) (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CX02 ∷ CCZ013 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CCZ123 ∷ CX40 ∷ CS14 ∷ CX02 ∷ [])
  b0 = at 1 1 (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) (lem-box-tQ-at0314203241 c4) ▸
       at 0 2 (Toff304 ∷ CX02 ∷ []) (wp1059 c4) ▸
       at 1 2 (CCZ123 ∷ CX02 ∷ CCZ013 ∷ []) (sym (wl1325 (lit c4))) ▸
       at 3 2 (Toff304 ∷ CCZ013 ∷ CCZ014 ∷ []) (wp1159 c4) ▸
       at 2 2 (Toff304 ∷ CX02 ∷ []) (wp1059 c4) ▸
       at 5 1 (CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ []) (wp1143 c4) ▸
       at 9 2 (CCZ123 ∷ CS14 ∷ []) (sym (wl0765 (lit c4))) ▸
       at 8 2 (CCZ123 ∷ CX40 ∷ []) (lem-comm-CX40-CCZ123 (lit c4)) ▸ done

  b1 : Chain (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CX02 ∷ CCZ013 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CCZ123 ∷ CX40 ∷ CS14 ∷ CX02 ∷ []) (Bx3-4021 ∷ CX02 ∷ CCZ014 ∷ CX02 ∷ [])
  b1 = at 7 2 (CCZ123 ∷ CS01⁻ ∷ []) (sym (wl1321 (lit c4))) ▸
       at 6 2 (CCZ123 ∷ CX40 ∷ []) (lem-comm-CX40-CCZ123 (lit c4)) ▸
       at 5 2 (CCZ123 ∷ CS01 ∷ []) (sym (wl0763 (lit c4))) ▸
       at 6 5 (CCZ014 ∷ []) (sym (wp1143 c4)) ▸
       at 4 2 (CCZ123 ∷ CCZ013 ∷ []) (wl0327 (lit c4)) ▸
       at 3 2 (CCZ123 ∷ CX02 ∷ CCZ013 ∷ []) (sym (wl1325 (lit c4))) ▸
       at 4 3 (CX02 ∷ []) (wl1326 (lit c4)) ▸
       at 0 4 (Bx3-4021 ∷ []) (sym (lem-box-tQ-at0314203241 c4)) ▸ done

  b2 : Chain (Bx3-4021 ∷ CX02 ∷ CCZ014 ∷ CX02 ∷ []) (Bx3-4021 ∷ CCZ014 ∷ [])
  b2 = at 1 3 (CCZ014 ∷ []) (sym (wp0378 c4)) ▸ done


-- CXcb-box @0314203241: 18 steps
lem-CXcb-box-at0314203241 : Ws → ⟪ (CX20 ∷ Bx3-4021 ∷ CX20 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4021 ∷ CCZ124 ∷ []) ⟫ʷ
lem-CXcb-box-at0314203241 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX20 ∷ Bx3-4021 ∷ CX20 ∷ []) (Toff304 ∷ CCZ123 ∷ CX20 ∷ Toff324 ∷ CS12 ∷ CX42 ∷ Toff304 ∷ CS12⁻ ∷ CX42 ∷ CS14 ∷ CCZ123 ∷ CX20 ∷ [])
  b0 = at 1 1 (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) (lem-box-tQ-at0314203241 c4) ▸
       at 0 2 (Toff304 ∷ CX20 ∷ Toff324 ∷ []) (wp1160 c4) ▸
       at 2 2 (CCZ123 ∷ Toff324 ∷ CCZ124 ∷ []) (sym (wl1327 (lit c4))) ▸
       at 1 2 (CCZ123 ∷ CX20 ∷ []) (sym (wl0482 (lit c4))) ▸
       at 4 1 (CS12 ∷ CX42 ∷ CS12⁻ ∷ CX42 ∷ CS14 ∷ []) (wl0702 (lit c4)) ▸
       at 8 2 (Toff304 ∷ CS14 ∷ []) (wp1037 c4) ▸
       at 7 2 (Toff304 ∷ CX42 ∷ []) (wp1055 c4) ▸
       at 6 2 (Toff304 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-TOFF304 (lit c4)) ▸ done

  b1 : Chain (Toff304 ∷ CCZ123 ∷ CX20 ∷ Toff324 ∷ CS12 ∷ CX42 ∷ Toff304 ∷ CS12⁻ ∷ CX42 ∷ CS14 ∷ CCZ123 ∷ CX20 ∷ []) (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ CX20 ∷ CCZ124 ∷ CX20 ∷ [])
  b1 = at 5 2 (Toff304 ∷ CX42 ∷ []) (wp1055 c4) ▸
       at 4 2 (Toff304 ∷ CS12 ∷ []) (lem-comm-CS12-TOFF304 (lit c4)) ▸
       at 5 5 (CCZ124 ∷ []) (sym (wl0702 (lit c4))) ▸
       at 3 2 (Toff304 ∷ Toff324 ∷ []) (sym (wp1144 c4)) ▸
       at 2 2 (Toff304 ∷ CX20 ∷ Toff324 ∷ []) (wp1160 c4) ▸
       at 3 3 (CX20 ∷ []) (wp1161 c4) ▸
       at 4 2 (CCZ123 ∷ CCZ124 ∷ []) (sym (wl0770 (lit c4))) ▸
       at 3 2 (CCZ123 ∷ CX20 ∷ []) (sym (wl0482 (lit c4))) ▸ done

  b2 : Chain (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ CX20 ∷ CCZ124 ∷ CX20 ∷ []) (Bx3-4021 ∷ CCZ124 ∷ [])
  b2 = at 0 4 (Bx3-4021 ∷ []) (sym (lem-box-tQ-at0314203241 c4)) ▸
       at 1 3 (CCZ124 ∷ []) (sym (wp0380 c4)) ▸ done


-- SWbc-box @0314203241: 11 steps
lem-SWbc-box-at0314203241 : Ws → ⟪ (Sw02 ∷ Bx3-4021 ∷ Sw02 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4021 ∷ []) ⟫ʷ
lem-SWbc-box-at0314203241 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw02 ∷ Bx3-4021 ∷ Sw02 ∷ []) (CX02 ∷ Bx3-4021 ∷ CX02 ∷ CCZ014 ∷ CCZ124 ∷ CCZ014 ∷ CCZ124 ∷ CCZ014 ∷ [])
  b0 = at 0 1 (CX02 ∷ CX20 ∷ CX02 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 4 1 (CX02 ∷ CX20 ∷ CX02 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 2 3 (Bx3-4021 ∷ CCZ014 ∷ []) (lem-CXbc-box-at0314203241 c4) ▸
       at 3 2 (CX20 ∷ CCZ124 ∷ CCZ014 ∷ []) (wp0381 c4) ▸
       at 1 3 (Bx3-4021 ∷ CCZ124 ∷ []) (lem-CXcb-box-at0314203241 c4) ▸
       at 4 2 (CX02 ∷ CCZ014 ∷ []) (wp0308 c4) ▸
       at 3 2 (CX02 ∷ CCZ014 ∷ CCZ124 ∷ []) (wp0382 c4) ▸
       at 2 2 (CX02 ∷ CCZ014 ∷ CCZ124 ∷ []) (wp0382 c4) ▸ done

  b1 : Chain (CX02 ∷ Bx3-4021 ∷ CX02 ∷ CCZ014 ∷ CCZ124 ∷ CCZ014 ∷ CCZ124 ∷ CCZ014 ∷ []) (Bx3-4021 ∷ [])
  b1 = at 3 5 (CCZ014 ∷ []) (wp0383 c4) ▸
       at 0 3 (Bx3-4021 ∷ CCZ014 ∷ []) (lem-CXbc-box-at0314203241 c4) ▸
       at 1 2 [] (wp0161 c4) ▸ done


-- nat-SWbc @0314203241: 23 steps
lem-nat-SWbc-at0314203241 : Ws → ⟪ (Sw02 ∷ Bx3-4021 ∷ Sw02 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4201 ∷ []) ⟫ʷ
lem-nat-SWbc-at0314203241 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw02 ∷ Bx3-4021 ∷ Sw02 ∷ []) (CCZ234 ∷ Toff324 ∷ CCZ034 ∷ Toff403 ∷ Bx3-41 ∷ Toff403 ∷ Sw02 ∷ CCZ234 ∷ Bx3-41 ∷ Toff304 ∷ CCZ034 ∷ Bx4-321 ∷ Sw02 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff304 ∷ Bx4-321 ∷ Toff304 ∷ CCZ034 ∷ Bx4-321 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw02 ∷ []) (sym (wp1148 c4)) ▸
       at 1 2 (Toff324 ∷ Sw02 ∷ []) (wp1162 c4) ▸
       at 3 1 (CCZ234 ∷ Toff423 ∷ Bx3-41 ∷ Toff423 ∷ CCZ234 ∷ Bx3-41 ∷ []) (refl) ▸
       at 2 2 (CCZ034 ∷ Sw02 ∷ []) (sym (wp1146 c4)) ▸
       at 3 2 (Toff403 ∷ Sw02 ∷ []) (wp1163 c4) ▸
       at 4 2 (Bx3-41 ∷ Sw02 ∷ []) (lem-comm-SWAP02-BOX⟨3·41⟩ (lit c4)) ▸
       at 5 2 (Toff403 ∷ Sw02 ∷ []) (wp1163 c4) ▸ done

  b1 : Chain (CCZ234 ∷ Toff324 ∷ CCZ034 ∷ Toff403 ∷ Bx3-41 ∷ Toff403 ∷ Sw02 ∷ CCZ234 ∷ Bx3-41 ∷ Toff304 ∷ CCZ034 ∷ Bx4-321 ∷ Sw02 ∷ []) (CCZ234 ∷ Toff324 ∷ CCZ034 ∷ Toff403 ∷ Bx3-41 ∷ Toff403 ∷ CCZ034 ∷ Bx3-41 ∷ Toff324 ∷ CCZ234 ∷ CCZ034 ∷ Toff403 ∷ Bx3-41 ∷ Sw02 ∷ Toff423 ∷ CCZ234 ∷ Bx3-41 ∷ Sw02 ∷ [])
  b1 = at 6 2 (CCZ034 ∷ Sw02 ∷ []) (sym (wp1146 c4)) ▸
       at 7 2 (Bx3-41 ∷ Sw02 ∷ []) (lem-comm-SWAP02-BOX⟨3·41⟩ (lit c4)) ▸
       at 8 2 (Toff324 ∷ Sw02 ∷ []) (wp1162 c4) ▸
       at 9 2 (CCZ234 ∷ Sw02 ∷ []) (sym (wp1148 c4)) ▸
       at 11 1 (CCZ234 ∷ Toff423 ∷ Bx3-41 ∷ Toff423 ∷ CCZ234 ∷ Bx3-41 ∷ []) (refl) ▸
       at 10 2 (CCZ034 ∷ Sw02 ∷ []) (sym (wp1146 c4)) ▸
       at 11 2 (Toff403 ∷ Sw02 ∷ []) (wp1163 c4) ▸
       at 12 2 (Bx3-41 ∷ Sw02 ∷ []) (lem-comm-SWAP02-BOX⟨3·41⟩ (lit c4)) ▸ done

  b2 : Chain (CCZ234 ∷ Toff324 ∷ CCZ034 ∷ Toff403 ∷ Bx3-41 ∷ Toff403 ∷ CCZ034 ∷ Bx3-41 ∷ Toff324 ∷ CCZ234 ∷ CCZ034 ∷ Toff403 ∷ Bx3-41 ∷ Sw02 ∷ Toff423 ∷ CCZ234 ∷ Bx3-41 ∷ Sw02 ∷ []) (Bx3-4201 ∷ [])
  b2 = at 13 2 (Toff403 ∷ Sw02 ∷ []) (wp1163 c4) ▸
       at 14 2 (CCZ034 ∷ Sw02 ∷ []) (sym (wp1146 c4)) ▸
       at 15 2 (Bx3-41 ∷ Sw02 ∷ []) (lem-comm-SWAP02-BOX⟨3·41⟩ (lit c4)) ▸
       at 16 2 [] (wl0485 (lit c4)) ▸
       at 2 6 (Bx4-301 ∷ []) (refl) ▸
       at 5 6 (Bx4-301 ∷ []) (refl) ▸
       at 0 6 (Bx3-4201 ∷ []) (refl) ▸ done


-- sym-bc @0314203241: 2 steps
lem-sym-bc-at0314203241 : Ws → ⟪ (Bx3-4021 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4201 ∷ []) ⟫ʷ
lem-sym-bc-at0314203241 c4 = run b0
  where
  b0 : Chain (Bx3-4021 ∷ []) (Bx3-4201 ∷ [])
  b0 = at 0 1 (Sw02 ∷ Bx3-4021 ∷ Sw02 ∷ []) (sym (lem-SWbc-box-at0314203241 c4)) ▸
       at 0 3 (Bx3-4201 ∷ []) (lem-nat-SWbc-at0314203241 c4) ▸ done


-- sym-ab @03143041: 18 steps
lem-sym-ab-at03143041 : Ws → ⟪ (Bx3-4201 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2401 ∷ []) ⟫ʷ
lem-sym-ab-at03143041 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx3-4201 ∷ []) (CCZ234 ∷ Toff324 ∷ CCZ023 ∷ Toff203 ∷ Bx3-21 ∷ Toff203 ∷ CCZ023 ∷ Bx3-21 ∷ Toff324 ∷ CCZ234 ∷ Bx4-301 ∷ [])
  b0 = at 0 1 (CCZ234 ∷ Toff324 ∷ Bx4-301 ∷ Toff324 ∷ CCZ234 ∷ Bx4-301 ∷ []) (refl) ▸
       at 2 1 (CCZ034 ∷ Toff403 ∷ Bx3-41 ∷ Toff403 ∷ CCZ034 ∷ Bx3-41 ∷ []) (refl) ▸
       at 4 1 (CZ14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 2 6 (CCZ013 ∷ []) (sym (wp0214 c4)) ▸
       at 2 1 (CCZ023 ∷ Toff203 ∷ CZ12 ∷ Toff203 ∷ CCZ023 ∷ CZ12 ∷ []) (wl0231 (lit c4)) ▸
       at 4 1 (Bx3-21 ∷ []) (refl) ▸
       at 7 1 (Bx3-21 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ234 ∷ Toff324 ∷ CCZ023 ∷ Toff203 ∷ Bx3-21 ∷ Toff203 ∷ CCZ023 ∷ Bx3-21 ∷ Toff324 ∷ CCZ234 ∷ Bx4-301 ∷ []) (CCZ234 ∷ Toff324 ∷ Bx2-301 ∷ Toff324 ∷ CCZ234 ∷ CCZ023 ∷ Toff203 ∷ Bx3-21 ∷ Toff203 ∷ CCZ023 ∷ Bx3-21 ∷ [])
  b1 = at 2 6 (Bx2-301 ∷ []) (refl) ▸
       at 5 1 (CCZ034 ∷ Toff403 ∷ Bx3-41 ∷ Toff403 ∷ CCZ034 ∷ Bx3-41 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 10 1 (CZ14 ∷ []) (refl) ▸
       at 5 6 (CCZ013 ∷ []) (sym (wp0214 c4)) ▸
       at 5 1 (CCZ023 ∷ Toff203 ∷ CZ12 ∷ Toff203 ∷ CCZ023 ∷ CZ12 ∷ []) (wl0231 (lit c4)) ▸
       at 7 1 (Bx3-21 ∷ []) (refl) ▸
       at 10 1 (Bx3-21 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ234 ∷ Toff324 ∷ Bx2-301 ∷ Toff324 ∷ CCZ234 ∷ CCZ023 ∷ Toff203 ∷ Bx3-21 ∷ Toff203 ∷ CCZ023 ∷ Bx3-21 ∷ []) (Bx3-2401 ∷ [])
  b2 = at 5 6 (Bx2-301 ∷ []) (refl) ▸
       at 0 6 (Bx3-2401 ∷ []) (refl) ▸ done


-- box-perm-3124 @0314203241: 2 steps
lem-box-perm-3124-at0314203241 : Ws → ⟪ (Bx3-4021 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2401 ∷ []) ⟫ʷ
lem-box-perm-3124-at0314203241 c4 = run b0
  where
  b0 : Chain (Bx3-4021 ∷ []) (Bx3-2401 ∷ [])
  b0 = at 0 1 (Bx3-4201 ∷ []) (lem-sym-bc-at0314203241 c4) ▸
       at 0 1 (Bx3-2401 ∷ []) (lem-sym-ab-at03143041 c4) ▸ done


-- sym-ab @0213243041: 18 steps
lem-sym-ab-at0213243041 : Ws → ⟪ (Bx2-3401 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4301 ∷ []) ⟫ʷ
lem-sym-ab-at0213243041 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx2-3401 ∷ []) (CCZ234 ∷ Toff234 ∷ CCZ024 ∷ Toff402 ∷ Bx2-41 ∷ Toff402 ∷ CCZ024 ∷ Bx2-41 ∷ Toff234 ∷ CCZ234 ∷ Bx3-201 ∷ [])
  b0 = at 0 1 (CCZ234 ∷ Toff234 ∷ Bx3-201 ∷ Toff234 ∷ CCZ234 ∷ Bx3-201 ∷ []) (refl) ▸
       at 2 1 (CCZ023 ∷ Toff302 ∷ Bx2-31 ∷ Toff302 ∷ CCZ023 ∷ Bx2-31 ∷ []) (refl) ▸
       at 4 1 (CZ13 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 2 6 (CCZ012 ∷ []) (sym (wl0288 (lit c4))) ▸
       at 2 1 (CCZ024 ∷ Toff402 ∷ CZ14 ∷ Toff402 ∷ CCZ024 ∷ CZ14 ∷ []) (wp0162 c4) ▸
       at 4 1 (Bx2-41 ∷ []) (refl) ▸
       at 7 1 (Bx2-41 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ234 ∷ Toff234 ∷ CCZ024 ∷ Toff402 ∷ Bx2-41 ∷ Toff402 ∷ CCZ024 ∷ Bx2-41 ∷ Toff234 ∷ CCZ234 ∷ Bx3-201 ∷ []) (CCZ234 ∷ Toff234 ∷ Bx4-201 ∷ Toff234 ∷ CCZ234 ∷ CCZ024 ∷ Toff402 ∷ Bx2-41 ∷ Toff402 ∷ CCZ024 ∷ Bx2-41 ∷ [])
  b1 = at 2 6 (Bx4-201 ∷ []) (refl) ▸
       at 5 1 (CCZ023 ∷ Toff302 ∷ Bx2-31 ∷ Toff302 ∷ CCZ023 ∷ Bx2-31 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 10 1 (CZ13 ∷ []) (refl) ▸
       at 5 6 (CCZ012 ∷ []) (sym (wl0288 (lit c4))) ▸
       at 5 1 (CCZ024 ∷ Toff402 ∷ CZ14 ∷ Toff402 ∷ CCZ024 ∷ CZ14 ∷ []) (wp0162 c4) ▸
       at 7 1 (Bx2-41 ∷ []) (refl) ▸
       at 10 1 (Bx2-41 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ234 ∷ Toff234 ∷ Bx4-201 ∷ Toff234 ∷ CCZ234 ∷ CCZ024 ∷ Toff402 ∷ Bx2-41 ∷ Toff402 ∷ CCZ024 ∷ Bx2-41 ∷ []) (Bx2-4301 ∷ [])
  b2 = at 5 6 (Bx4-201 ∷ []) (refl) ▸
       at 0 6 (Bx2-4301 ∷ []) (refl) ▸ done


-- box-tQ @0214233041: 13 steps
lem-box-tQ-at0214233041 : Ws → ⟪ (Bx2-4301 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ CCZ012 ∷ Toff234 ∷ CCZ012 ∷ []) ⟫ʷ
lem-box-tQ-at0214233041 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx2-4301 ∷ []) (CCZ234 ∷ Toff234 ∷ CCZ012 ∷ Toff234 ∷ CCZ234 ∷ CCZ024 ∷ Toff402 ∷ CZ14 ∷ Toff402 ∷ CCZ024 ∷ CZ14 ∷ [])
  b0 = at 0 1 (CCZ234 ∷ Toff234 ∷ Bx4-201 ∷ Toff234 ∷ CCZ234 ∷ Bx4-201 ∷ []) (refl) ▸
       at 2 1 (CCZ024 ∷ Toff402 ∷ Bx2-41 ∷ Toff402 ∷ CCZ024 ∷ Bx2-41 ∷ []) (refl) ▸
       at 4 1 (CZ14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 2 6 (CCZ012 ∷ []) (sym (wp0162 c4)) ▸
       at 5 1 (CCZ024 ∷ Toff402 ∷ Bx2-41 ∷ Toff402 ∷ CCZ024 ∷ Bx2-41 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 10 1 (CZ14 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ234 ∷ Toff234 ∷ CCZ012 ∷ Toff234 ∷ CCZ234 ∷ CCZ024 ∷ Toff402 ∷ CZ14 ∷ Toff402 ∷ CCZ024 ∷ CZ14 ∷ []) (Toff234 ∷ CCZ012 ∷ Toff234 ∷ CCZ012 ∷ [])
  b1 = at 5 6 (CCZ012 ∷ []) (sym (wp0162 c4)) ▸
       at 0 2 (Toff234 ∷ CCZ234 ∷ CZ34 ∷ []) (wl0936 (lit c4)) ▸
       at 2 2 (CCZ012 ∷ CZ34 ∷ []) (sym (c₃ (CCZ) (CZ))) ▸
       at 1 2 (CCZ012 ∷ CCZ234 ∷ []) (lem-cQ-at0214233041 c4) ▸
       at 2 4 (Toff234 ∷ []) (wl0937 (lit c4)) ▸ done


-- P-box @0214233041: 8 steps
lem-P-box-at0214233041 : Ws → ⟪ (Toff201 ∷ Bx2-4301 ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4301 ∷ []) ⟫ʷ
lem-P-box-at0214233041 c4 = run b0
  where
  b0 : Chain (Toff201 ∷ Bx2-4301 ∷ Toff201 ∷ []) (Bx2-4301 ∷ [])
  b0 = at 1 1 (Toff234 ∷ CCZ012 ∷ Toff234 ∷ CCZ012 ∷ []) (lem-box-tQ-at0214233041 c4) ▸
       at 0 2 (Toff234 ∷ Toff201 ∷ []) (sym (lem-tP-at0214233041 c4)) ▸
       at 1 2 (CCZ012 ∷ CZ01 ∷ Toff201 ∷ []) (sym (wl0949 (lit c4))) ▸
       at 3 2 (Toff234 ∷ Toff201 ∷ []) (sym (lem-tP-at0214233041 c4)) ▸
       at 4 3 (CCZ012 ∷ CZ01 ∷ []) (sym (wl0950 (lit c4))) ▸
       at 2 2 (Toff234 ∷ CZ01 ∷ []) (c₂ (CZ) (Toff)) ▸
       at 3 3 (CCZ012 ∷ []) (sym (wl0951 (lit c4))) ▸
       at 0 4 (Bx2-4301 ∷ []) (sym (lem-box-tQ-at0214233041 c4)) ▸ done


-- pairs @0214233041: 4 steps
lem-pairs-at0214233041 : Ws → ⟪ (Bx2-4301 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0143 ∷ []) ⟫ʷ
lem-pairs-at0214233041 c4 = run b0
  where
  b0 : Chain (Bx2-4301 ∷ []) (Bx2-0143 ∷ [])
  b0 = at 0 1 (Toff201 ∷ Bx2-4301 ∷ Toff201 ∷ []) (sym (lem-P-box-at0214233041 c4)) ▸
       at 1 1 (CCZ234 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ []) (lem-box-cP-at0214233041 c4) ▸
       at 4 2 [] (wl0421 (lit c4)) ▸
       at 0 4 (Bx2-0143 ∷ []) (sym (lem-box-tQ-at0210213443 c4)) ▸ done


-- CXbc-box @0210213443: 17 steps
lem-CXbc-box-at0210213443 : Ws → ⟪ (CX14 ∷ Bx2-0143 ∷ CX14 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0143 ∷ CCZ013 ∷ []) ⟫ʷ
lem-CXbc-box-at0210213443 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX14 ∷ Bx2-0143 ∷ CX14 ∷ []) (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CX14 ∷ CCZ123 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CCZ234 ∷ CX01 ∷ CS03 ∷ CX14 ∷ [])
  b0 = at 1 1 (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-box-tQ-at0210213443 c4) ▸
       at 0 2 (Toff201 ∷ CX14 ∷ []) (wp1164 c4) ▸
       at 1 2 (CCZ234 ∷ CX14 ∷ CCZ123 ∷ []) (sym (wl1257 (lit c4))) ▸
       at 3 2 (Toff201 ∷ CCZ123 ∷ CCZ013 ∷ []) (wl1328 (lit c4)) ▸
       at 2 2 (Toff201 ∷ CX14 ∷ []) (wp1164 c4) ▸
       at 5 1 (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ []) (wl0184 (lit c4)) ▸
       at 9 2 (CCZ234 ∷ CS03 ∷ []) (sym (wp0294 c4)) ▸
       at 8 2 (CCZ234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (CCZ)) ▸ done

  b1 : Chain (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CX14 ∷ CCZ123 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CCZ234 ∷ CX01 ∷ CS03 ∷ CX14 ∷ []) (Bx2-0143 ∷ CX14 ∷ CCZ013 ∷ CX14 ∷ [])
  b1 = at 7 2 (CCZ234 ∷ CS13⁻ ∷ []) (sym (wl0432 (lit c4))) ▸
       at 6 2 (CCZ234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (CCZ)) ▸
       at 5 2 (CCZ234 ∷ CS13 ∷ []) (sym (wl0433 (lit c4))) ▸
       at 6 5 (CCZ013 ∷ []) (sym (wl0184 (lit c4))) ▸
       at 4 2 (CCZ234 ∷ CCZ123 ∷ []) (wl0508 (lit c4)) ▸
       at 3 2 (CCZ234 ∷ CX14 ∷ CCZ123 ∷ []) (sym (wl1257 (lit c4))) ▸
       at 4 3 (CX14 ∷ []) (wl1259 (lit c4)) ▸
       at 0 4 (Bx2-0143 ∷ []) (sym (lem-box-tQ-at0210213443 c4)) ▸ done

  b2 : Chain (Bx2-0143 ∷ CX14 ∷ CCZ013 ∷ CX14 ∷ []) (Bx2-0143 ∷ CCZ013 ∷ [])
  b2 = at 1 3 (CCZ013 ∷ []) (sym (wp0565 c4)) ▸ done


-- CXcb-box @0210213443: 18 steps
lem-CXcb-box-at0210213443 : Ws → ⟪ (CX41 ∷ Bx2-0143 ∷ CX41 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0143 ∷ CCZ034 ∷ []) ⟫ʷ
lem-CXcb-box-at0210213443 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX41 ∷ Bx2-0143 ∷ CX41 ∷ []) (Toff201 ∷ CCZ234 ∷ CX41 ∷ Toff204 ∷ CS34 ∷ CX04 ∷ Toff201 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ CCZ234 ∷ CX41 ∷ [])
  b0 = at 1 1 (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-box-tQ-at0210213443 c4) ▸
       at 0 2 (Toff201 ∷ CX41 ∷ Toff204 ∷ []) (wp1165 c4) ▸
       at 2 2 (CCZ234 ∷ Toff204 ∷ CCZ034 ∷ []) (sym (wp1166 c4)) ▸
       at 1 2 (CCZ234 ∷ CX41 ∷ []) (sym (wl0302 (lit c4))) ▸
       at 4 1 (CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ []) (wp0352 c4) ▸
       at 8 2 (Toff201 ∷ CS03 ∷ []) (wl1329 (lit c4)) ▸
       at 7 2 (Toff201 ∷ CX04 ∷ []) (wp1167 c4) ▸
       at 6 2 (Toff201 ∷ CS34⁻ ∷ []) (sym (c₃ (Toffᵗ) (CS • CS • CS))) ▸ done

  b1 : Chain (Toff201 ∷ CCZ234 ∷ CX41 ∷ Toff204 ∷ CS34 ∷ CX04 ∷ Toff201 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ CCZ234 ∷ CX41 ∷ []) (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ CX41 ∷ CCZ034 ∷ CX41 ∷ [])
  b1 = at 5 2 (Toff201 ∷ CX04 ∷ []) (wp1167 c4) ▸
       at 4 2 (Toff201 ∷ CS34 ∷ []) (sym (c₃ (Toffᵗ) (CS))) ▸
       at 5 5 (CCZ034 ∷ []) (sym (wp0352 c4)) ▸
       at 3 2 (Toff201 ∷ Toff204 ∷ []) (sym (wp0563 c4)) ▸
       at 2 2 (Toff201 ∷ CX41 ∷ Toff204 ∷ []) (wp1165 c4) ▸
       at 3 3 (CX41 ∷ []) (wp1168 c4) ▸
       at 4 2 (CCZ234 ∷ CCZ034 ∷ []) (wp0129 c4) ▸
       at 3 2 (CCZ234 ∷ CX41 ∷ []) (sym (wl0302 (lit c4))) ▸ done

  b2 : Chain (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ CX41 ∷ CCZ034 ∷ CX41 ∷ []) (Bx2-0143 ∷ CCZ034 ∷ [])
  b2 = at 0 4 (Bx2-0143 ∷ []) (sym (lem-box-tQ-at0210213443 c4)) ▸
       at 1 3 (CCZ034 ∷ []) (sym (wp0560 c4)) ▸ done


-- SWbc-box @0210213443: 11 steps
lem-SWbc-box-at0210213443 : Ws → ⟪ (Sw14 ∷ Bx2-0143 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0143 ∷ []) ⟫ʷ
lem-SWbc-box-at0210213443 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw14 ∷ Bx2-0143 ∷ Sw14 ∷ []) (CX14 ∷ Bx2-0143 ∷ CX14 ∷ CCZ013 ∷ CCZ034 ∷ CCZ013 ∷ CCZ034 ∷ CCZ013 ∷ [])
  b0 = at 0 1 (CX14 ∷ CX41 ∷ CX14 ∷ []) (sym (wl0423 (lit c4))) ▸
       at 4 1 (CX14 ∷ CX41 ∷ CX14 ∷ []) (sym (wl0423 (lit c4))) ▸
       at 2 3 (Bx2-0143 ∷ CCZ013 ∷ []) (lem-CXbc-box-at0210213443 c4) ▸
       at 3 2 (CX41 ∷ CCZ034 ∷ CCZ013 ∷ []) (wp0567 c4) ▸
       at 1 3 (Bx2-0143 ∷ CCZ034 ∷ []) (lem-CXcb-box-at0210213443 c4) ▸
       at 4 2 (CX14 ∷ CCZ013 ∷ []) (wp0189 c4) ▸
       at 3 2 (CX14 ∷ CCZ013 ∷ CCZ034 ∷ []) (wp0566 c4) ▸
       at 2 2 (CX14 ∷ CCZ013 ∷ CCZ034 ∷ []) (wp0566 c4) ▸ done

  b1 : Chain (CX14 ∷ Bx2-0143 ∷ CX14 ∷ CCZ013 ∷ CCZ034 ∷ CCZ013 ∷ CCZ034 ∷ CCZ013 ∷ []) (Bx2-0143 ∷ [])
  b1 = at 3 5 (CCZ013 ∷ []) (wp0769 c4) ▸
       at 0 3 (Bx2-0143 ∷ CCZ013 ∷ []) (lem-CXbc-box-at0210213443 c4) ▸
       at 1 2 [] (wl0230 (lit c4)) ▸ done


-- nat-SWbc @0210213443: 23 steps
lem-nat-SWbc-at0210213443 : Ws → ⟪ (Sw14 ∷ Bx2-0143 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ []) ⟫ʷ
lem-nat-SWbc-at0210213443 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw14 ∷ Bx2-0143 ∷ Sw14 ∷ []) (CCZ024 ∷ Toff204 ∷ CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ Sw14 ∷ CCZ024 ∷ Bx2-03 ∷ Toff201 ∷ CCZ012 ∷ Bx0-243 ∷ Sw14 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff201 ∷ Bx0-243 ∷ Toff201 ∷ CCZ012 ∷ Bx0-243 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw14 ∷ []) (sym (wp0196 c4)) ▸
       at 1 2 (Toff204 ∷ Sw14 ∷ []) (wp0197 c4) ▸
       at 3 1 (CCZ024 ∷ Toff024 ∷ Bx2-03 ∷ Toff024 ∷ CCZ024 ∷ Bx2-03 ∷ []) (refl) ▸
       at 2 2 (CCZ012 ∷ Sw14 ∷ []) (sym (wp0194 c4)) ▸
       at 3 2 (Toff012 ∷ Sw14 ∷ []) (wp0195 c4) ▸
       at 4 2 (Bx2-03 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨2·03⟩ (lit c4)) ▸
       at 5 2 (Toff012 ∷ Sw14 ∷ []) (wp0195 c4) ▸ done

  b1 : Chain (CCZ024 ∷ Toff204 ∷ CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ Sw14 ∷ CCZ024 ∷ Bx2-03 ∷ Toff201 ∷ CCZ012 ∷ Bx0-243 ∷ Sw14 ∷ []) (CCZ024 ∷ Toff204 ∷ CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ Toff204 ∷ CCZ024 ∷ CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Sw14 ∷ Toff024 ∷ CCZ024 ∷ Bx2-03 ∷ Sw14 ∷ [])
  b1 = at 6 2 (CCZ012 ∷ Sw14 ∷ []) (sym (wp0194 c4)) ▸
       at 7 2 (Bx2-03 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨2·03⟩ (lit c4)) ▸
       at 8 2 (Toff204 ∷ Sw14 ∷ []) (wp0197 c4) ▸
       at 9 2 (CCZ024 ∷ Sw14 ∷ []) (sym (wp0196 c4)) ▸
       at 11 1 (CCZ024 ∷ Toff024 ∷ Bx2-03 ∷ Toff024 ∷ CCZ024 ∷ Bx2-03 ∷ []) (refl) ▸
       at 10 2 (CCZ012 ∷ Sw14 ∷ []) (sym (wp0194 c4)) ▸
       at 11 2 (Toff012 ∷ Sw14 ∷ []) (wp0195 c4) ▸
       at 12 2 (Bx2-03 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨2·03⟩ (lit c4)) ▸ done

  b2 : Chain (CCZ024 ∷ Toff204 ∷ CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ Toff204 ∷ CCZ024 ∷ CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Sw14 ∷ Toff024 ∷ CCZ024 ∷ Bx2-03 ∷ Sw14 ∷ []) (Bx2-0413 ∷ [])
  b2 = at 13 2 (Toff012 ∷ Sw14 ∷ []) (wp0195 c4) ▸
       at 14 2 (CCZ012 ∷ Sw14 ∷ []) (sym (wp0194 c4)) ▸
       at 15 2 (Bx2-03 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨2·03⟩ (lit c4)) ▸
       at 16 2 [] (wl0306 (lit c4)) ▸
       at 2 6 (Bx0-213 ∷ []) (refl) ▸
       at 5 6 (Bx0-213 ∷ []) (refl) ▸
       at 0 6 (Bx2-0413 ∷ []) (refl) ▸ done


-- sym-bc @0210213443: 2 steps
lem-sym-bc-at0210213443 : Ws → ⟪ (Bx2-0143 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ []) ⟫ʷ
lem-sym-bc-at0210213443 c4 = run b0
  where
  b0 : Chain (Bx2-0143 ∷ []) (Bx2-0413 ∷ [])
  b0 = at 0 1 (Sw14 ∷ Bx2-0143 ∷ Sw14 ∷ []) (sym (lem-SWbc-box-at0210213443 c4)) ▸
       at 0 3 (Bx2-0413 ∷ []) (lem-nat-SWbc-at0210213443 c4) ▸ done


-- box-perm-2341 @0213243041: 4 steps
lem-box-perm-2341-at0213243041 : Ws → ⟪ (Bx2-3401 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4013 ∷ []) ⟫ʷ
lem-box-perm-2341-at0213243041 c4 = run b0
  where
  b0 : Chain (Bx2-3401 ∷ []) (Bx2-4013 ∷ [])
  b0 = at 0 1 (Bx2-4301 ∷ []) (lem-sym-ab-at0213243041 c4) ▸
       at 0 1 (Bx2-0143 ∷ []) (lem-pairs-at0214233041 c4) ▸
       at 0 1 (Bx2-0413 ∷ []) (lem-sym-bc-at0210213443 c4) ▸
       at 0 1 (Bx2-4013 ∷ []) (lem-sym-ab-at0210243143 c4) ▸ done


-- P-box @0210213443: 8 steps
lem-P-box-at0210213443 : Ws → ⟪ (Toff234 ∷ Bx2-0143 ∷ Toff234 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0143 ∷ []) ⟫ʷ
lem-P-box-at0210213443 c4 = run b0
  where
  b0 : Chain (Toff234 ∷ Bx2-0143 ∷ Toff234 ∷ []) (Bx2-0143 ∷ [])
  b0 = at 1 1 (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-box-tQ-at0210213443 c4) ▸
       at 0 2 (Toff201 ∷ Toff234 ∷ []) (sym (lem-tP-at0210213443 c4)) ▸
       at 1 2 (CCZ234 ∷ CZ34 ∷ Toff234 ∷ []) (sym (wl0932 (lit c4))) ▸
       at 3 2 (Toff201 ∷ Toff234 ∷ []) (sym (lem-tP-at0210213443 c4)) ▸
       at 4 3 (CCZ234 ∷ CZ34 ∷ []) (sym (wl0933 (lit c4))) ▸
       at 2 2 (Toff201 ∷ CZ34 ∷ []) (sym (c₃ (Toffᵗ) (CZ))) ▸
       at 3 3 (CCZ234 ∷ []) (sym (wl0934 (lit c4))) ▸
       at 0 4 (Bx2-0143 ∷ []) (sym (lem-box-tQ-at0210213443 c4)) ▸ done


-- pairs @0210213443: 4 steps
lem-pairs-at0210213443 : Ws → ⟪ (Bx2-0143 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4301 ∷ []) ⟫ʷ
lem-pairs-at0210213443 c4 = run b0
  where
  b0 : Chain (Bx2-0143 ∷ []) (Bx2-4301 ∷ [])
  b0 = at 0 1 (Toff234 ∷ Bx2-0143 ∷ Toff234 ∷ []) (sym (lem-P-box-at0210213443 c4)) ▸
       at 1 1 (CCZ012 ∷ Toff234 ∷ CCZ012 ∷ Toff234 ∷ []) (lem-box-cP-at0210213443 c4) ▸
       at 4 2 [] (wl0420 (lit c4)) ▸
       at 0 4 (Bx2-4301 ∷ []) (sym (lem-box-tQ-at0214233041 c4)) ▸ done


-- box-perm-4123 @0214203143: 4 steps
lem-box-perm-4123-at0214203143 : Ws → ⟪ (Bx2-4013 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3401 ∷ []) ⟫ʷ
lem-box-perm-4123-at0214203143 c4 = run b0
  where
  b0 : Chain (Bx2-4013 ∷ []) (Bx2-3401 ∷ [])
  b0 = at 0 1 (Bx2-0413 ∷ []) (lem-sym-ab-at0214203143 c4) ▸
       at 0 1 (Bx2-0143 ∷ []) (lem-sym-bc-at0210243143 c4) ▸
       at 0 1 (Bx2-4301 ∷ []) (lem-pairs-at0210213443 c4) ▸
       at 0 1 (Bx2-3401 ∷ []) (lem-sym-ab-at0214233041 c4) ▸ done


-- box-box-1 @0213243041: 105 steps
lem-box-box-1-at0213243041 : Ws → ⟪ (Bx2-3401 ∷ Bx3-2401 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2401 ∷ Bx2-3401 ∷ []) ⟫ʷ
lem-box-box-1-at0213243041 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (run b13)))))))))))))
  where
  b0 : Chain (Bx2-3401 ∷ Bx3-2401 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ234 ∷ Toff301 ∷ CCZ123 ∷ CS01 ∷ CX20 ∷ CS01⁻ ∷ CCZ234 ∷ CX20 ∷ CS12 ∷ Toff301 ∷ [])
  b0 = at 0 1 (Bx2-4013 ∷ []) (lem-box-perm-2341-at0213243041 c4) ▸
       at 0 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-box-tQ-at0214203143 c4) ▸
       at 4 1 (CCZ234 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ []) (lem-box-cP-at0312243041 c4) ▸
       at 3 2 (CCZ234 ∷ CCZ123 ∷ []) (wl0508 (lit c4)) ▸
       at 4 2 (Toff301 ∷ CCZ123 ∷ CCZ012 ∷ []) (wl1258 (lit c4)) ▸
       at 6 1 (CS01 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ []) (wl1273 (lit c4)) ▸
       at 10 2 (CCZ234 ∷ CS12 ∷ []) (sym (wl0415 (lit c4))) ▸
       at 9 2 (CCZ234 ∷ CX20 ∷ []) (sym (wp0366 c4)) ▸ done

  b1 : Chain (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ234 ∷ Toff301 ∷ CCZ123 ∷ CS01 ∷ CX20 ∷ CS01⁻ ∷ CCZ234 ∷ CX20 ∷ CS12 ∷ Toff301 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ123 ∷ [])
  b1 = at 8 2 (CCZ234 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (CCZ)) ▸
       at 7 2 (CCZ234 ∷ CX20 ∷ []) (sym (wp0366 c4)) ▸
       at 6 2 (CCZ234 ∷ CS01 ∷ []) (c₂ (CS) (CCZ)) ▸
       at 7 5 (CCZ012 ∷ []) (sym (wl1273 (lit c4))) ▸
       at 5 2 (CCZ234 ∷ CCZ123 ∷ []) (wl0508 (lit c4)) ▸
       at 6 3 (Toff301 ∷ CCZ123 ∷ []) (wl1330 (lit c4)) ▸
       at 3 4 (Bx3-2401 ∷ []) (sym (lem-box-cP-at0312243041 c4)) ▸
       at 3 1 (CCZ234 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ []) (lem-box-cP-at0312243041 c4) ▸ done

  b2 : Chain (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ123 ∷ []) (Toff204 ∷ CCZ123 ∷ CCZ234 ∷ K2 ∷ CS04 ∷ Toff301 ∷ CX24 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ K2⁻ ∷ CCZ034 ∷ CCZ014 ∷ CCZ234 ∷ Toff301 ∷ CCZ123 ∷ [])
  b2 = at 2 2 (CCZ234 ∷ Toff204 ∷ CCZ034 ∷ []) (sym (wp1166 c4)) ▸
       at 4 2 (Toff301 ∷ CCZ034 ∷ CCZ014 ∷ []) (wp0377 c4) ▸
       at 3 1 (K2 ∷ CS04 ∷ CX24 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ K2⁻ ∷ []) (sym (wp1169 c4)) ▸
       at 9 2 (Toff301 ∷ K2⁻ ∷ []) (wl1331 (lit c4)) ▸
       at 8 2 (Toff301 ∷ CS02 ∷ []) (wl1260 (lit c4)) ▸
       at 7 2 (Toff301 ∷ CX24 ∷ []) (lem-comm-CX24-TOFF301 (lit c4)) ▸
       at 6 2 (Toff301 ∷ CS04⁻ ∷ []) (wp1170 c4) ▸
       at 5 2 (Toff301 ∷ CX24 ∷ []) (lem-comm-CX24-TOFF301 (lit c4)) ▸ done

  b3 : Chain (Toff204 ∷ CCZ123 ∷ CCZ234 ∷ K2 ∷ CS04 ∷ Toff301 ∷ CX24 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ K2⁻ ∷ CCZ034 ∷ CCZ014 ∷ CCZ234 ∷ Toff301 ∷ CCZ123 ∷ []) (Toff204 ∷ CCZ123 ∷ CCZ234 ∷ Toff301 ∷ Toff204 ∷ CCZ034 ∷ CS01 ∷ CCZ234 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ Toff301 ∷ CCZ123 ∷ [])
  b3 = at 4 2 (Toff301 ∷ CS04 ∷ []) (wp0897 c4) ▸
       at 3 2 (Toff301 ∷ K2 ∷ []) (wl1266 (lit c4)) ▸
       at 4 7 (Toff204 ∷ []) (wp1169 c4) ▸
       at 6 1 (CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ []) (wp1143 c4) ▸
       at 10 2 (CCZ234 ∷ CS14 ∷ []) (sym (wl0452 (lit c4))) ▸
       at 9 2 (CCZ234 ∷ CX40 ∷ []) (sym (wp1171 c4)) ▸
       at 8 2 (CCZ234 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (CCZ)) ▸
       at 7 2 (CCZ234 ∷ CX40 ∷ []) (sym (wp1171 c4)) ▸ done

  b4 : Chain (Toff204 ∷ CCZ123 ∷ CCZ234 ∷ Toff301 ∷ Toff204 ∷ CCZ034 ∷ CS01 ∷ CCZ234 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ Toff301 ∷ CCZ123 ∷ []) (Toff204 ∷ CCZ123 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ K2 ∷ CS04 ∷ CX24 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ Toff301 ∷ K2⁻ ∷ CCZ014 ∷ CCZ123 ∷ [])
  b4 = at 6 2 (CCZ234 ∷ CS01 ∷ []) (c₂ (CS) (CCZ)) ▸
       at 7 5 (CCZ014 ∷ []) (sym (wp1143 c4)) ▸
       at 5 2 (CCZ234 ∷ CCZ034 ∷ []) (wp0129 c4) ▸
       at 4 2 (CCZ234 ∷ Toff204 ∷ CCZ034 ∷ []) (sym (wp1166 c4)) ▸
       at 5 3 (Toff204 ∷ []) (wp1172 c4) ▸
       at 6 2 (Toff301 ∷ CCZ014 ∷ []) (wp1173 c4) ▸
       at 5 1 (K2 ∷ CS04 ∷ CX24 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ K2⁻ ∷ []) (sym (wp1169 c4)) ▸
       at 11 2 (Toff301 ∷ K2⁻ ∷ []) (wl1331 (lit c4)) ▸ done

  b5 : Chain (Toff204 ∷ CCZ123 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ K2 ∷ CS04 ∷ CX24 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ Toff301 ∷ K2⁻ ∷ CCZ014 ∷ CCZ123 ∷ []) (Toff204 ∷ CCZ123 ∷ Bx3-2401 ∷ Toff204 ∷ CCZ014 ∷ CCZ123 ∷ [])
  b5 = at 10 2 (Toff301 ∷ CS02 ∷ []) (wl1260 (lit c4)) ▸
       at 9 2 (Toff301 ∷ CX24 ∷ []) (lem-comm-CX24-TOFF301 (lit c4)) ▸
       at 8 2 (Toff301 ∷ CS04⁻ ∷ []) (wp1170 c4) ▸
       at 7 2 (Toff301 ∷ CX24 ∷ []) (lem-comm-CX24-TOFF301 (lit c4)) ▸
       at 6 2 (Toff301 ∷ CS04 ∷ []) (wp0897 c4) ▸
       at 5 2 (Toff301 ∷ K2 ∷ []) (wl1266 (lit c4)) ▸
       at 6 7 (Toff204 ∷ []) (wp1169 c4) ▸
       at 2 4 (Bx3-2401 ∷ []) (sym (lem-box-cP-at0312243041 c4)) ▸ done

  b6 : Chain (Toff204 ∷ CCZ123 ∷ Bx3-2401 ∷ Toff204 ∷ CCZ014 ∷ CCZ123 ∷ []) (Toff204 ∷ CCZ234 ∷ Toff301 ∷ CCZ123 ∷ CS01 ∷ CCZ234 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ Toff301 ∷ Toff204 ∷ CCZ014 ∷ CCZ123 ∷ [])
  b6 = at 2 1 (CCZ234 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ []) (lem-box-cP-at0312243041 c4) ▸
       at 1 2 (CCZ234 ∷ CCZ123 ∷ []) (wl0508 (lit c4)) ▸
       at 2 2 (Toff301 ∷ CCZ123 ∷ CCZ012 ∷ []) (wl1258 (lit c4)) ▸
       at 4 1 (CS01 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ []) (wl1273 (lit c4)) ▸
       at 8 2 (CCZ234 ∷ CS12 ∷ []) (sym (wl0415 (lit c4))) ▸
       at 7 2 (CCZ234 ∷ CX20 ∷ []) (sym (wp0366 c4)) ▸
       at 6 2 (CCZ234 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (CCZ)) ▸
       at 5 2 (CCZ234 ∷ CX20 ∷ []) (sym (wp0366 c4)) ▸ done

  b7 : Chain (Toff204 ∷ CCZ234 ∷ Toff301 ∷ CCZ123 ∷ CS01 ∷ CCZ234 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ Toff301 ∷ Toff204 ∷ CCZ014 ∷ CCZ123 ∷ []) (CCZ234 ∷ Toff204 ∷ Toff301 ∷ CCZ034 ∷ CCZ014 ∷ CCZ234 ∷ Toff301 ∷ CCZ123 ∷ Toff204 ∷ CCZ014 ∷ CCZ123 ∷ [])
  b7 = at 4 2 (CCZ234 ∷ CS01 ∷ []) (c₂ (CS) (CCZ)) ▸
       at 5 5 (CCZ012 ∷ []) (sym (wl1273 (lit c4))) ▸
       at 3 2 (CCZ234 ∷ CCZ123 ∷ []) (wl0508 (lit c4)) ▸
       at 4 3 (Toff301 ∷ CCZ123 ∷ []) (wl1330 (lit c4)) ▸
       at 1 4 (Bx3-2401 ∷ []) (sym (lem-box-cP-at0312243041 c4)) ▸
       at 1 1 (CCZ234 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ []) (lem-box-cP-at0312243041 c4) ▸
       at 0 2 (CCZ234 ∷ Toff204 ∷ CCZ034 ∷ []) (sym (wp1166 c4)) ▸
       at 2 2 (Toff301 ∷ CCZ034 ∷ CCZ014 ∷ []) (wp0377 c4) ▸ done

  b8 : Chain (CCZ234 ∷ Toff204 ∷ Toff301 ∷ CCZ034 ∷ CCZ014 ∷ CCZ234 ∷ Toff301 ∷ CCZ123 ∷ Toff204 ∷ CCZ014 ∷ CCZ123 ∷ []) (CCZ234 ∷ Toff301 ∷ K2 ∷ CS04 ∷ CX24 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ K2⁻ ∷ CCZ034 ∷ CCZ014 ∷ CCZ234 ∷ Toff301 ∷ CCZ123 ∷ Toff204 ∷ CCZ014 ∷ CCZ123 ∷ [])
  b8 = at 1 1 (K2 ∷ CS04 ∷ CX24 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ K2⁻ ∷ []) (sym (wp1169 c4)) ▸
       at 7 2 (Toff301 ∷ K2⁻ ∷ []) (wl1331 (lit c4)) ▸
       at 6 2 (Toff301 ∷ CS02 ∷ []) (wl1260 (lit c4)) ▸
       at 5 2 (Toff301 ∷ CX24 ∷ []) (lem-comm-CX24-TOFF301 (lit c4)) ▸
       at 4 2 (Toff301 ∷ CS04⁻ ∷ []) (wp1170 c4) ▸
       at 3 2 (Toff301 ∷ CX24 ∷ []) (lem-comm-CX24-TOFF301 (lit c4)) ▸
       at 2 2 (Toff301 ∷ CS04 ∷ []) (wp0897 c4) ▸
       at 1 2 (Toff301 ∷ K2 ∷ []) (wl1266 (lit c4)) ▸ done

  b9 : Chain (CCZ234 ∷ Toff301 ∷ K2 ∷ CS04 ∷ CX24 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ K2⁻ ∷ CCZ034 ∷ CCZ014 ∷ CCZ234 ∷ Toff301 ∷ CCZ123 ∷ Toff204 ∷ CCZ014 ∷ CCZ123 ∷ []) (CCZ234 ∷ Toff301 ∷ Toff204 ∷ CCZ034 ∷ CCZ234 ∷ CCZ014 ∷ Toff301 ∷ CCZ123 ∷ Toff204 ∷ CCZ014 ∷ CCZ123 ∷ [])
  b9 = at 2 7 (Toff204 ∷ []) (wp1169 c4) ▸
       at 4 1 (CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ []) (wp1143 c4) ▸
       at 8 2 (CCZ234 ∷ CS14 ∷ []) (sym (wl0452 (lit c4))) ▸
       at 7 2 (CCZ234 ∷ CX40 ∷ []) (sym (wp1171 c4)) ▸
       at 6 2 (CCZ234 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (CCZ)) ▸
       at 5 2 (CCZ234 ∷ CX40 ∷ []) (sym (wp1171 c4)) ▸
       at 4 2 (CCZ234 ∷ CS01 ∷ []) (c₂ (CS) (CCZ)) ▸
       at 5 5 (CCZ014 ∷ []) (sym (wp1143 c4)) ▸ done

  b10 : Chain (CCZ234 ∷ Toff301 ∷ Toff204 ∷ CCZ034 ∷ CCZ234 ∷ CCZ014 ∷ Toff301 ∷ CCZ123 ∷ Toff204 ∷ CCZ014 ∷ CCZ123 ∷ []) (CCZ234 ∷ Toff301 ∷ CCZ234 ∷ K2 ∷ CS04 ∷ CX24 ∷ CS04⁻ ∷ Toff301 ∷ CX24 ∷ CS02 ∷ K2⁻ ∷ CCZ014 ∷ CCZ123 ∷ Toff204 ∷ CCZ014 ∷ CCZ123 ∷ [])
  b10 = at 3 2 (CCZ234 ∷ CCZ034 ∷ []) (wp0129 c4) ▸
       at 2 2 (CCZ234 ∷ Toff204 ∷ CCZ034 ∷ []) (sym (wp1166 c4)) ▸
       at 3 3 (Toff204 ∷ []) (wp1172 c4) ▸
       at 4 2 (Toff301 ∷ CCZ014 ∷ []) (wp1173 c4) ▸
       at 3 1 (K2 ∷ CS04 ∷ CX24 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ K2⁻ ∷ []) (sym (wp1169 c4)) ▸
       at 9 2 (Toff301 ∷ K2⁻ ∷ []) (wl1331 (lit c4)) ▸
       at 8 2 (Toff301 ∷ CS02 ∷ []) (wl1260 (lit c4)) ▸
       at 7 2 (Toff301 ∷ CX24 ∷ []) (lem-comm-CX24-TOFF301 (lit c4)) ▸ done

  b11 : Chain (CCZ234 ∷ Toff301 ∷ CCZ234 ∷ K2 ∷ CS04 ∷ CX24 ∷ CS04⁻ ∷ Toff301 ∷ CX24 ∷ CS02 ∷ K2⁻ ∷ CCZ014 ∷ CCZ123 ∷ Toff204 ∷ CCZ014 ∷ CCZ123 ∷ []) (Bx3-2401 ∷ Toff204 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CCZ123 ∷ CS14 ∷ Toff204 ∷ CCZ014 ∷ CCZ123 ∷ [])
  b11 = at 6 2 (Toff301 ∷ CS04⁻ ∷ []) (wp1170 c4) ▸
       at 5 2 (Toff301 ∷ CX24 ∷ []) (lem-comm-CX24-TOFF301 (lit c4)) ▸
       at 4 2 (Toff301 ∷ CS04 ∷ []) (wp0897 c4) ▸
       at 3 2 (Toff301 ∷ K2 ∷ []) (wl1266 (lit c4)) ▸
       at 4 7 (Toff204 ∷ []) (wp1169 c4) ▸
       at 0 4 (Bx3-2401 ∷ []) (sym (lem-box-cP-at0312243041 c4)) ▸
       at 2 1 (CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ []) (wp1143 c4) ▸
       at 6 2 (CCZ123 ∷ CS14 ∷ []) (sym (wl0765 (lit c4))) ▸ done

  b12 : Chain (Bx3-2401 ∷ Toff204 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CCZ123 ∷ CS14 ∷ Toff204 ∷ CCZ014 ∷ CCZ123 ∷ []) (Bx3-2401 ∷ Bx2-4013 ∷ [])
  b12 = at 5 2 (CCZ123 ∷ CX40 ∷ []) (lem-comm-CX40-CCZ123 (lit c4)) ▸
       at 4 2 (CCZ123 ∷ CS01⁻ ∷ []) (sym (wl1321 (lit c4))) ▸
       at 3 2 (CCZ123 ∷ CX40 ∷ []) (lem-comm-CX40-CCZ123 (lit c4)) ▸
       at 2 2 (CCZ123 ∷ CS01 ∷ []) (sym (wl0763 (lit c4))) ▸
       at 3 5 (CCZ014 ∷ []) (sym (wp1143 c4)) ▸
       at 3 2 (Toff204 ∷ CCZ014 ∷ []) (wp1174 c4) ▸
       at 4 2 [] (wp0161 c4) ▸
       at 1 4 (Bx2-4013 ∷ []) (sym (lem-box-tQ-at0214203143 c4)) ▸ done

  b13 : Chain (Bx3-2401 ∷ Bx2-4013 ∷ []) (Bx3-2401 ∷ Bx2-3401 ∷ [])
  b13 = at 1 1 (Bx2-3401 ∷ []) (lem-box-perm-4123-at0214203143 c4) ▸ done


-- box-perm-2314 @0312243041: 2 steps
lem-box-perm-2314-at0312243041 : Ws → ⟪ (Bx3-2401 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4021 ∷ []) ⟫ʷ
lem-box-perm-2314-at0312243041 c4 = run b0
  where
  b0 : Chain (Bx3-2401 ∷ []) (Bx3-4021 ∷ [])
  b0 = at 0 1 (Bx3-4201 ∷ []) (lem-sym-ab-at0312243041 c4) ▸
       at 0 1 (Bx3-4021 ∷ []) (lem-sym-bc-at03143041 c4) ▸ done


-- CXbc-box @0214233041: 17 steps
lem-CXbc-box-at0214233041 : Ws → ⟪ (CX30 ∷ Bx2-4301 ∷ CX30 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4301 ∷ CCZ134 ∷ []) ⟫ʷ
lem-CXbc-box-at0214233041 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX30 ∷ Bx2-4301 ∷ CX30 ∷ []) (Toff234 ∷ CCZ012 ∷ Toff234 ∷ CX30 ∷ CCZ123 ∷ CS13 ∷ CX43 ∷ CS13⁻ ∷ CCZ012 ∷ CX43 ∷ CS14 ∷ CX30 ∷ [])
  b0 = at 1 1 (Toff234 ∷ CCZ012 ∷ Toff234 ∷ CCZ012 ∷ []) (lem-box-tQ-at0214233041 c4) ▸
       at 0 2 (Toff234 ∷ CX30 ∷ []) (wp1175 c4) ▸
       at 1 2 (CCZ012 ∷ CX30 ∷ CCZ123 ∷ []) (sym (wl0383 (lit c4))) ▸
       at 3 2 (Toff234 ∷ CCZ123 ∷ CCZ134 ∷ []) (wl0426 (lit c4)) ▸
       at 2 2 (Toff234 ∷ CX30 ∷ []) (wp1175 c4) ▸
       at 5 1 (CS13 ∷ CX43 ∷ CS13⁻ ∷ CX43 ∷ CS14 ∷ []) (wl0707 (lit c4)) ▸
       at 9 2 (CCZ012 ∷ CS14 ∷ []) (sym (wp0011 c4)) ▸
       at 8 2 (CCZ012 ∷ CX43 ∷ []) (sym (c₃ (CCZ) (CX₁₀))) ▸ done

  b1 : Chain (Toff234 ∷ CCZ012 ∷ Toff234 ∷ CX30 ∷ CCZ123 ∷ CS13 ∷ CX43 ∷ CS13⁻ ∷ CCZ012 ∷ CX43 ∷ CS14 ∷ CX30 ∷ []) (Bx2-4301 ∷ CX30 ∷ CCZ134 ∷ CX30 ∷ [])
  b1 = at 7 2 (CCZ012 ∷ CS13⁻ ∷ []) (sym (wl0992 (lit c4))) ▸
       at 6 2 (CCZ012 ∷ CX43 ∷ []) (sym (c₃ (CCZ) (CX₁₀))) ▸
       at 5 2 (CCZ012 ∷ CS13 ∷ []) (sym (wl0311 (lit c4))) ▸
       at 6 5 (CCZ134 ∷ []) (sym (wl0707 (lit c4))) ▸
       at 4 2 (CCZ012 ∷ CCZ123 ∷ []) (sym (wl0298 (lit c4))) ▸
       at 3 2 (CCZ012 ∷ CX30 ∷ CCZ123 ∷ []) (sym (wl0383 (lit c4))) ▸
       at 4 3 (CX30 ∷ []) (wl0384 (lit c4)) ▸
       at 0 4 (Bx2-4301 ∷ []) (sym (lem-box-tQ-at0214233041 c4)) ▸ done

  b2 : Chain (Bx2-4301 ∷ CX30 ∷ CCZ134 ∷ CX30 ∷ []) (Bx2-4301 ∷ CCZ134 ∷ [])
  b2 = at 1 3 (CCZ134 ∷ []) (sym (wp0759 c4)) ▸ done


-- CXcb-box @0214233041: 18 steps
lem-CXcb-box-at0214233041 : Ws → ⟪ (CX03 ∷ Bx2-4301 ∷ CX03 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4301 ∷ CCZ014 ∷ []) ⟫ʷ
lem-CXcb-box-at0214233041 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX03 ∷ Bx2-4301 ∷ CX03 ∷ []) (Toff234 ∷ CCZ012 ∷ CX03 ∷ Toff204 ∷ CS01 ∷ CX40 ∷ Toff234 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ CCZ012 ∷ CX03 ∷ [])
  b0 = at 1 1 (Toff234 ∷ CCZ012 ∷ Toff234 ∷ CCZ012 ∷ []) (lem-box-tQ-at0214233041 c4) ▸
       at 0 2 (Toff234 ∷ CX03 ∷ Toff204 ∷ []) (wp1176 c4) ▸
       at 2 2 (CCZ012 ∷ Toff204 ∷ CCZ014 ∷ []) (sym (wp1177 c4)) ▸
       at 1 2 (CCZ012 ∷ CX03 ∷ []) (sym (wl0381 (lit c4))) ▸
       at 4 1 (CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ []) (wp1143 c4) ▸
       at 8 2 (Toff234 ∷ CS14 ∷ []) (wl1332 (lit c4)) ▸
       at 7 2 (Toff234 ∷ CX40 ∷ []) (wp1178 c4) ▸
       at 6 2 (Toff234 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (Toff)) ▸ done

  b1 : Chain (Toff234 ∷ CCZ012 ∷ CX03 ∷ Toff204 ∷ CS01 ∷ CX40 ∷ Toff234 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ CCZ012 ∷ CX03 ∷ []) (Toff234 ∷ CCZ012 ∷ Toff234 ∷ CCZ012 ∷ CX03 ∷ CCZ014 ∷ CX03 ∷ [])
  b1 = at 5 2 (Toff234 ∷ CX40 ∷ []) (wp1178 c4) ▸
       at 4 2 (Toff234 ∷ CS01 ∷ []) (c₂ (CS) (Toff)) ▸
       at 5 5 (CCZ014 ∷ []) (sym (wp1143 c4)) ▸
       at 3 2 (Toff234 ∷ Toff204 ∷ []) (wp1153 c4) ▸
       at 2 2 (Toff234 ∷ CX03 ∷ Toff204 ∷ []) (wp1176 c4) ▸
       at 3 3 (CX03 ∷ []) (wp1179 c4) ▸
       at 4 2 (CCZ012 ∷ CCZ014 ∷ []) (sym (wp0167 c4)) ▸
       at 3 2 (CCZ012 ∷ CX03 ∷ []) (sym (wl0381 (lit c4))) ▸ done

  b2 : Chain (Toff234 ∷ CCZ012 ∷ Toff234 ∷ CCZ012 ∷ CX03 ∷ CCZ014 ∷ CX03 ∷ []) (Bx2-4301 ∷ CCZ014 ∷ [])
  b2 = at 0 4 (Bx2-4301 ∷ []) (sym (lem-box-tQ-at0214233041 c4)) ▸
       at 1 3 (CCZ014 ∷ []) (sym (wp0761 c4)) ▸ done


-- SWbc-box @0214233041: 11 steps
lem-SWbc-box-at0214233041 : Ws → ⟪ (Sw03 ∷ Bx2-4301 ∷ Sw03 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4301 ∷ []) ⟫ʷ
lem-SWbc-box-at0214233041 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw03 ∷ Bx2-4301 ∷ Sw03 ∷ []) (CX30 ∷ Bx2-4301 ∷ CX30 ∷ CCZ134 ∷ CCZ014 ∷ CCZ134 ∷ CCZ014 ∷ CCZ134 ∷ [])
  b0 = at 0 1 (CX30 ∷ CX03 ∷ CX30 ∷ []) (sym (wl0923 (lit c4))) ▸
       at 4 1 (CX30 ∷ CX03 ∷ CX30 ∷ []) (sym (wl0923 (lit c4))) ▸
       at 2 3 (Bx2-4301 ∷ CCZ134 ∷ []) (lem-CXbc-box-at0214233041 c4) ▸
       at 3 2 (CX03 ∷ CCZ014 ∷ CCZ134 ∷ []) (wp0762 c4) ▸
       at 1 3 (Bx2-4301 ∷ CCZ014 ∷ []) (lem-CXcb-box-at0214233041 c4) ▸
       at 4 2 (CX30 ∷ CCZ134 ∷ []) (wp0705 c4) ▸
       at 3 2 (CX30 ∷ CCZ134 ∷ CCZ014 ∷ []) (wp0763 c4) ▸
       at 2 2 (CX30 ∷ CCZ134 ∷ CCZ014 ∷ []) (wp0763 c4) ▸ done

  b1 : Chain (CX30 ∷ Bx2-4301 ∷ CX30 ∷ CCZ134 ∷ CCZ014 ∷ CCZ134 ∷ CCZ014 ∷ CCZ134 ∷ []) (Bx2-4301 ∷ [])
  b1 = at 3 5 (CCZ134 ∷ []) (wp0764 c4) ▸
       at 0 3 (Bx2-4301 ∷ CCZ134 ∷ []) (lem-CXbc-box-at0214233041 c4) ▸
       at 1 2 [] (wl0321 (lit c4)) ▸ done


-- nat-SWbc @0214233041: 23 steps
lem-nat-SWbc-at0214233041 : Ws → ⟪ (Sw03 ∷ Bx2-4301 ∷ Sw03 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4031 ∷ []) ⟫ʷ
lem-nat-SWbc-at0214233041 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw03 ∷ Bx2-4301 ∷ Sw03 ∷ []) (CCZ024 ∷ Toff204 ∷ CCZ234 ∷ Toff423 ∷ Bx2-41 ∷ Toff423 ∷ Sw03 ∷ CCZ024 ∷ Bx2-41 ∷ Toff234 ∷ CCZ234 ∷ Bx4-201 ∷ Sw03 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff234 ∷ Bx4-201 ∷ Toff234 ∷ CCZ234 ∷ Bx4-201 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw03 ∷ []) (sym (wp1157 c4)) ▸
       at 1 2 (Toff204 ∷ Sw03 ∷ []) (wp1180 c4) ▸
       at 3 1 (CCZ024 ∷ Toff402 ∷ Bx2-41 ∷ Toff402 ∷ CCZ024 ∷ Bx2-41 ∷ []) (refl) ▸
       at 2 2 (CCZ234 ∷ Sw03 ∷ []) (sym (wp1155 c4)) ▸
       at 3 2 (Toff423 ∷ Sw03 ∷ []) (wp1181 c4) ▸
       at 4 2 (Bx2-41 ∷ Sw03 ∷ []) (lem-comm-SWAP03-BOX⟨2·41⟩ (lit c4)) ▸
       at 5 2 (Toff423 ∷ Sw03 ∷ []) (wp1181 c4) ▸ done

  b1 : Chain (CCZ024 ∷ Toff204 ∷ CCZ234 ∷ Toff423 ∷ Bx2-41 ∷ Toff423 ∷ Sw03 ∷ CCZ024 ∷ Bx2-41 ∷ Toff234 ∷ CCZ234 ∷ Bx4-201 ∷ Sw03 ∷ []) (CCZ024 ∷ Toff204 ∷ CCZ234 ∷ Toff423 ∷ Bx2-41 ∷ Toff423 ∷ CCZ234 ∷ Bx2-41 ∷ Toff204 ∷ CCZ024 ∷ CCZ234 ∷ Toff423 ∷ Bx2-41 ∷ Sw03 ∷ Toff402 ∷ CCZ024 ∷ Bx2-41 ∷ Sw03 ∷ [])
  b1 = at 6 2 (CCZ234 ∷ Sw03 ∷ []) (sym (wp1155 c4)) ▸
       at 7 2 (Bx2-41 ∷ Sw03 ∷ []) (lem-comm-SWAP03-BOX⟨2·41⟩ (lit c4)) ▸
       at 8 2 (Toff204 ∷ Sw03 ∷ []) (wp1180 c4) ▸
       at 9 2 (CCZ024 ∷ Sw03 ∷ []) (sym (wp1157 c4)) ▸
       at 11 1 (CCZ024 ∷ Toff402 ∷ Bx2-41 ∷ Toff402 ∷ CCZ024 ∷ Bx2-41 ∷ []) (refl) ▸
       at 10 2 (CCZ234 ∷ Sw03 ∷ []) (sym (wp1155 c4)) ▸
       at 11 2 (Toff423 ∷ Sw03 ∷ []) (wp1181 c4) ▸
       at 12 2 (Bx2-41 ∷ Sw03 ∷ []) (lem-comm-SWAP03-BOX⟨2·41⟩ (lit c4)) ▸ done

  b2 : Chain (CCZ024 ∷ Toff204 ∷ CCZ234 ∷ Toff423 ∷ Bx2-41 ∷ Toff423 ∷ CCZ234 ∷ Bx2-41 ∷ Toff204 ∷ CCZ024 ∷ CCZ234 ∷ Toff423 ∷ Bx2-41 ∷ Sw03 ∷ Toff402 ∷ CCZ024 ∷ Bx2-41 ∷ Sw03 ∷ []) (Bx2-4031 ∷ [])
  b2 = at 13 2 (Toff423 ∷ Sw03 ∷ []) (wp1181 c4) ▸
       at 14 2 (CCZ234 ∷ Sw03 ∷ []) (sym (wp1155 c4)) ▸
       at 15 2 (Bx2-41 ∷ Sw03 ∷ []) (lem-comm-SWAP03-BOX⟨2·41⟩ (lit c4)) ▸
       at 16 2 [] (wl0928 (lit c4)) ▸
       at 2 6 (Bx4-231 ∷ []) (refl) ▸
       at 5 6 (Bx4-231 ∷ []) (refl) ▸
       at 0 6 (Bx2-4031 ∷ []) (refl) ▸ done


-- sym-bc @0214233041: 2 steps
lem-sym-bc-at0214233041 : Ws → ⟪ (Bx2-4301 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4031 ∷ []) ⟫ʷ
lem-sym-bc-at0214233041 c4 = run b0
  where
  b0 : Chain (Bx2-4301 ∷ []) (Bx2-4031 ∷ [])
  b0 = at 0 1 (Sw03 ∷ Bx2-4301 ∷ Sw03 ∷ []) (sym (lem-SWbc-box-at0214233041 c4)) ▸
       at 0 3 (Bx2-4031 ∷ []) (lem-nat-SWbc-at0214233041 c4) ▸ done


-- box-perm-2314 @0213243041: 2 steps
lem-box-perm-2314-at0213243041 : Ws → ⟪ (Bx2-3401 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4031 ∷ []) ⟫ʷ
lem-box-perm-2314-at0213243041 c4 = run b0
  where
  b0 : Chain (Bx2-3401 ∷ []) (Bx2-4031 ∷ [])
  b0 = at 0 1 (Bx2-4301 ∷ []) (lem-sym-ab-at0213243041 c4) ▸
       at 0 1 (Bx2-4031 ∷ []) (lem-sym-bc-at0214233041 c4) ▸ done


-- Tu-box @0314203241: 83 steps
lem-Tu-box-at0314203241 : Ws → ⟪ (Toff234 ∷ Bx3-4021 ∷ Toff234 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4021 ∷ Bx2-4031 ∷ []) ⟫ʷ
lem-Tu-box-at0314203241 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (run b10))))))))))
  where
  b0 : Chain (Toff234 ∷ Bx3-4021 ∷ Toff234 ∷ []) (Toff304 ∷ Toff204 ∷ CCZ123 ∷ Toff304 ∷ CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ Toff204 ∷ CCZ014 ∷ CCZ123 ∷ CCZ134 ∷ [])
  b0 = at 1 1 (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) (lem-box-tQ-at0314203241 c4) ▸
       at 0 2 (Toff304 ∷ Toff204 ∷ Toff234 ∷ []) (wp1182 c4) ▸
       at 2 2 (CCZ123 ∷ CCZ134 ∷ Toff234 ∷ []) (sym (wl1333 (lit c4))) ▸
       at 4 2 (Toff304 ∷ Toff204 ∷ Toff234 ∷ []) (wp1182 c4) ▸
       at 6 3 (CCZ123 ∷ CCZ134 ∷ []) (sym (wl1334 (lit c4))) ▸
       at 3 2 (Toff304 ∷ CCZ134 ∷ CCZ014 ∷ []) (wp1056 c4) ▸
       at 5 2 (Toff204 ∷ CCZ014 ∷ []) (wp1174 c4) ▸
       at 4 1 (CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ []) (wl0831 (lit c4)) ▸ done

  b1 : Chain (Toff304 ∷ Toff204 ∷ CCZ123 ∷ Toff304 ∷ CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ Toff204 ∷ CCZ014 ∷ CCZ123 ∷ CCZ134 ∷ []) (Toff304 ∷ Toff204 ∷ CCZ123 ∷ Toff304 ∷ Toff204 ∷ CCZ014 ∷ CCZ123 ∷ [])
  b1 = at 8 2 (Toff204 ∷ CS34 ∷ []) (wp0501 c4) ▸
       at 7 2 (Toff204 ∷ CX31 ∷ []) (lem-comm-CX31-TOFF204 (lit c4)) ▸
       at 6 2 (Toff204 ∷ CS14⁻ ∷ []) (wp1183 c4) ▸
       at 5 2 (Toff204 ∷ CX31 ∷ []) (lem-comm-CX31-TOFF204 (lit c4)) ▸
       at 4 2 (Toff204 ∷ CS14 ∷ []) (wp1152 c4) ▸
       at 5 5 (CCZ134 ∷ []) (sym (wl0831 (lit c4))) ▸
       at 5 2 (CCZ014 ∷ CCZ134 ∷ []) (sym (wp0272 c4)) ▸
       at 6 3 (CCZ123 ∷ []) (sym (wl1335 (lit c4))) ▸ done

  b2 : Chain (Toff304 ∷ Toff204 ∷ CCZ123 ∷ Toff304 ∷ Toff204 ∷ CCZ014 ∷ CCZ123 ∷ []) (Toff304 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ Toff304 ∷ CCZ123 ∷ CCZ014 ∷ [])
  b2 = at 5 1 (CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ []) (wp1143 c4) ▸
       at 9 2 (CCZ123 ∷ CS14 ∷ []) (sym (wl0765 (lit c4))) ▸
       at 8 2 (CCZ123 ∷ CX40 ∷ []) (lem-comm-CX40-CCZ123 (lit c4)) ▸
       at 7 2 (CCZ123 ∷ CS01⁻ ∷ []) (sym (wl1321 (lit c4))) ▸
       at 6 2 (CCZ123 ∷ CX40 ∷ []) (lem-comm-CX40-CCZ123 (lit c4)) ▸
       at 5 2 (CCZ123 ∷ CS01 ∷ []) (sym (wl0763 (lit c4))) ▸
       at 6 5 (CCZ014 ∷ []) (sym (wp1143 c4)) ▸
       at 3 2 (Toff204 ∷ Toff304 ∷ []) (sym (wp1184 c4)) ▸ done

  b3 : Chain (Toff304 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ Toff304 ∷ CCZ123 ∷ CCZ014 ∷ []) (CCZ234 ∷ K3 ∷ CS04 ∷ CX34 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ Toff201 ∷ K3⁻ ∷ CCZ024 ∷ CCZ014 ∷ CCZ234 ∷ Toff201 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ CCZ014 ∷ [])
  b3 = at 4 0 (CCZ123 ∷ CCZ123 ∷ []) (sym (wl0181 (lit c4))) ▸
       at 1 4 (Bx2-4031 ∷ []) (sym (lem-box-tQ-at02142041 c4)) ▸
       at 1 1 (Bx2-4301 ∷ []) (lem-box-perm-1324-at02142041 c4) ▸
       at 1 1 (CCZ234 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ []) (lem-box-cP-at0214233041 c4) ▸
       at 0 2 (CCZ234 ∷ Toff304 ∷ CCZ024 ∷ []) (sym (wp1071 c4)) ▸
       at 2 2 (Toff201 ∷ CCZ024 ∷ CCZ014 ∷ []) (wp0774 c4) ▸
       at 1 1 (K3 ∷ CS04 ∷ CX34 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ K3⁻ ∷ []) (sym (wp1185 c4)) ▸
       at 7 2 (Toff201 ∷ K3⁻ ∷ []) (sym (c₃ (Toffᵗ) (K • iI))) ▸ done

  b4 : Chain (CCZ234 ∷ K3 ∷ CS04 ∷ CX34 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ Toff201 ∷ K3⁻ ∷ CCZ024 ∷ CCZ014 ∷ CCZ234 ∷ Toff201 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ CCZ014 ∷ []) (CCZ234 ∷ Toff201 ∷ Toff304 ∷ CCZ024 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ CCZ234 ∷ Toff201 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ CCZ014 ∷ [])
  b4 = at 6 2 (Toff201 ∷ CS03 ∷ []) (wl1329 (lit c4)) ▸
       at 5 2 (Toff201 ∷ CX34 ∷ []) (sym (c₃ (Toffᵗ) (CX₀₁))) ▸
       at 4 2 (Toff201 ∷ CS04⁻ ∷ []) (wp1186 c4) ▸
       at 3 2 (Toff201 ∷ CX34 ∷ []) (sym (c₃ (Toffᵗ) (CX₀₁))) ▸
       at 2 2 (Toff201 ∷ CS04 ∷ []) (wp1187 c4) ▸
       at 1 2 (Toff201 ∷ K3 ∷ []) (sym (c₃ (Toffᵗ) (K))) ▸
       at 2 7 (Toff304 ∷ []) (wp1185 c4) ▸
       at 4 1 (CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ []) (wp1143 c4) ▸ done

  b5 : Chain (CCZ234 ∷ Toff201 ∷ Toff304 ∷ CCZ024 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ CCZ234 ∷ Toff201 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ CCZ014 ∷ []) (CCZ234 ∷ Toff201 ∷ CCZ234 ∷ Toff304 ∷ CCZ024 ∷ CCZ024 ∷ CCZ014 ∷ Toff201 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ CCZ014 ∷ [])
  b5 = at 8 2 (CCZ234 ∷ CS14 ∷ []) (sym (wl0452 (lit c4))) ▸
       at 7 2 (CCZ234 ∷ CX40 ∷ []) (sym (wp1171 c4)) ▸
       at 6 2 (CCZ234 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (CCZ)) ▸
       at 5 2 (CCZ234 ∷ CX40 ∷ []) (sym (wp1171 c4)) ▸
       at 4 2 (CCZ234 ∷ CS01 ∷ []) (c₂ (CS) (CCZ)) ▸
       at 5 5 (CCZ014 ∷ []) (sym (wp1143 c4)) ▸
       at 3 2 (CCZ234 ∷ CCZ024 ∷ []) (wp0090 c4) ▸
       at 2 2 (CCZ234 ∷ Toff304 ∷ CCZ024 ∷ []) (sym (wp1071 c4)) ▸ done

  b6 : Chain (CCZ234 ∷ Toff201 ∷ CCZ234 ∷ Toff304 ∷ CCZ024 ∷ CCZ024 ∷ CCZ014 ∷ Toff201 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ CCZ014 ∷ []) (CCZ234 ∷ Toff201 ∷ CCZ234 ∷ K3 ∷ CS04 ∷ Toff201 ∷ CX34 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ K3⁻ ∷ CCZ014 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ CCZ014 ∷ [])
  b6 = at 3 3 (Toff304 ∷ []) (wp1188 c4) ▸
       at 4 2 (Toff201 ∷ CCZ014 ∷ []) (wp1189 c4) ▸
       at 3 1 (K3 ∷ CS04 ∷ CX34 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ K3⁻ ∷ []) (sym (wp1185 c4)) ▸
       at 9 2 (Toff201 ∷ K3⁻ ∷ []) (sym (c₃ (Toffᵗ) (K • iI))) ▸
       at 8 2 (Toff201 ∷ CS03 ∷ []) (wl1329 (lit c4)) ▸
       at 7 2 (Toff201 ∷ CX34 ∷ []) (sym (c₃ (Toffᵗ) (CX₀₁))) ▸
       at 6 2 (Toff201 ∷ CS04⁻ ∷ []) (wp1186 c4) ▸
       at 5 2 (Toff201 ∷ CX34 ∷ []) (sym (c₃ (Toffᵗ) (CX₀₁))) ▸ done

  b7 : Chain (CCZ234 ∷ Toff201 ∷ CCZ234 ∷ K3 ∷ CS04 ∷ Toff201 ∷ CX34 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ K3⁻ ∷ CCZ014 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ CCZ014 ∷ []) (Bx2-4031 ∷ Toff304 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CCZ123 ∷ CX40 ∷ CS14 ∷ Toff304 ∷ CCZ123 ∷ CCZ014 ∷ [])
  b7 = at 4 2 (Toff201 ∷ CS04 ∷ []) (wp1187 c4) ▸
       at 3 2 (Toff201 ∷ K3 ∷ []) (sym (c₃ (Toffᵗ) (K))) ▸
       at 4 7 (Toff304 ∷ []) (wp1185 c4) ▸
       at 0 4 (Bx2-4301 ∷ []) (sym (lem-box-cP-at0214233041 c4)) ▸
       at 0 1 (Bx2-4031 ∷ []) (sym (lem-box-perm-1324-at02142041 c4)) ▸
       at 2 1 (CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ []) (wp1143 c4) ▸
       at 6 2 (CCZ123 ∷ CS14 ∷ []) (sym (wl0765 (lit c4))) ▸
       at 5 2 (CCZ123 ∷ CX40 ∷ []) (lem-comm-CX40-CCZ123 (lit c4)) ▸ done

  b8 : Chain (Bx2-4031 ∷ Toff304 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CCZ123 ∷ CX40 ∷ CS14 ∷ Toff304 ∷ CCZ123 ∷ CCZ014 ∷ []) (Bx2-4031 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CCZ123 ∷ CX40 ∷ CS14 ∷ CCZ014 ∷ [])
  b8 = at 4 2 (CCZ123 ∷ CS01⁻ ∷ []) (sym (wl1321 (lit c4))) ▸
       at 3 2 (CCZ123 ∷ CX40 ∷ []) (lem-comm-CX40-CCZ123 (lit c4)) ▸
       at 2 2 (CCZ123 ∷ CS01 ∷ []) (sym (wl0763 (lit c4))) ▸
       at 3 5 (CCZ014 ∷ []) (sym (wp1143 c4)) ▸
       at 3 2 (Toff304 ∷ CCZ014 ∷ []) (wp0687 c4) ▸
       at 4 1 (CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ []) (wp1143 c4) ▸
       at 8 2 (CCZ123 ∷ CS14 ∷ []) (sym (wl0765 (lit c4))) ▸
       at 7 2 (CCZ123 ∷ CX40 ∷ []) (lem-comm-CX40-CCZ123 (lit c4)) ▸ done

  b9 : Chain (Bx2-4031 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CCZ123 ∷ CX40 ∷ CS14 ∷ CCZ014 ∷ []) (Bx2-3401 ∷ Bx3-2401 ∷ [])
  b9 = at 6 2 (CCZ123 ∷ CS01⁻ ∷ []) (sym (wl1321 (lit c4))) ▸
       at 5 2 (CCZ123 ∷ CX40 ∷ []) (lem-comm-CX40-CCZ123 (lit c4)) ▸
       at 4 2 (CCZ123 ∷ CS01 ∷ []) (sym (wl0763 (lit c4))) ▸
       at 5 5 (CCZ014 ∷ []) (sym (wp1143 c4)) ▸
       at 5 2 [] (wp0161 c4) ▸
       at 1 4 (Bx3-4021 ∷ []) (sym (lem-box-tQ-at0314203241 c4)) ▸
       at 0 1 (Bx2-3401 ∷ []) (lem-box-perm-3124-at02142041 c4) ▸
       at 1 1 (Bx3-2401 ∷ []) (lem-box-perm-3124-at0314203241 c4) ▸ done

  b10 : Chain (Bx2-3401 ∷ Bx3-2401 ∷ []) (Bx3-4021 ∷ Bx2-4031 ∷ [])
  b10 = at 0 2 (Bx3-2401 ∷ Bx2-3401 ∷ []) (lem-box-box-1-at0213243041 c4) ▸
       at 0 1 (Bx3-4021 ∷ []) (lem-box-perm-2314-at0312243041 c4) ▸
       at 1 1 (Bx2-4031 ∷ []) (lem-box-perm-2314-at0213243041 c4) ▸ done


-- P-box @0312243041: 8 steps
lem-P-box-at0312243041 : Ws → ⟪ (Toff301 ∷ Bx3-2401 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2401 ∷ []) ⟫ʷ
lem-P-box-at0312243041 c4 = run b0
  where
  b0 : Chain (Toff301 ∷ Bx3-2401 ∷ Toff301 ∷ []) (Bx3-2401 ∷ [])
  b0 = at 1 1 (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ []) (lem-box-tQ-at0312243041 c4) ▸
       at 0 2 (Toff324 ∷ Toff301 ∷ []) (sym (lem-tP-at0312243041 c4)) ▸
       at 1 2 (CCZ013 ∷ CZ01 ∷ Toff301 ∷ []) (sym (wl0866 (lit c4))) ▸
       at 3 2 (Toff324 ∷ Toff301 ∷ []) (sym (lem-tP-at0312243041 c4)) ▸
       at 4 3 (CCZ013 ∷ CZ01 ∷ []) (sym (wl0867 (lit c4))) ▸
       at 2 2 (Toff324 ∷ CZ01 ∷ []) (c₂ (CZ) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 3 3 (CCZ013 ∷ []) (sym (wl0868 (lit c4))) ▸
       at 0 4 (Bx3-2401 ∷ []) (sym (lem-box-tQ-at0312243041 c4)) ▸ done


-- pairs @0312243041: 4 steps
lem-pairs-at0312243041 : Ws → ⟪ (Bx3-2401 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ []) ⟫ʷ
lem-pairs-at0312243041 c4 = run b0
  where
  b0 : Chain (Bx3-2401 ∷ []) (Bx3-0124 ∷ [])
  b0 = at 0 1 (Toff301 ∷ Bx3-2401 ∷ Toff301 ∷ []) (sym (lem-P-box-at0312243041 c4)) ▸
       at 1 1 (CCZ234 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ []) (lem-box-cP-at0312243041 c4) ▸
       at 4 2 [] (wl0443 (lit c4)) ▸
       at 0 4 (Bx3-0124 ∷ []) (sym (lem-box-tQ-at03102132 c4)) ▸ done


-- box-perm-2431 @0314203241: 3 steps
lem-box-perm-2431-at0314203241 : Ws → ⟪ (Bx3-4021 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ []) ⟫ʷ
lem-box-perm-2431-at0314203241 c4 = run b0
  where
  b0 : Chain (Bx3-4021 ∷ []) (Bx3-0124 ∷ [])
  b0 = at 0 1 (Bx3-4201 ∷ []) (lem-sym-bc-at0314203241 c4) ▸
       at 0 1 (Bx3-2401 ∷ []) (lem-sym-ab-at03143041 c4) ▸
       at 0 1 (Bx3-0124 ∷ []) (lem-pairs-at0312243041 c4) ▸ done


-- sym-ab @02142041: 18 steps
lem-sym-ab-at02142041 : Ws → ⟪ (Bx2-4031 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0431 ∷ []) ⟫ʷ
lem-sym-ab-at02142041 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx2-4031 ∷ []) (CCZ024 ∷ Toff204 ∷ CCZ023 ∷ Toff023 ∷ Bx2-01 ∷ Toff023 ∷ CCZ023 ∷ Bx2-01 ∷ Toff204 ∷ CCZ024 ∷ Bx4-231 ∷ [])
  b0 = at 0 1 (CCZ024 ∷ Toff204 ∷ Bx4-231 ∷ Toff204 ∷ CCZ024 ∷ Bx4-231 ∷ []) (refl) ▸
       at 2 1 (CCZ234 ∷ Toff423 ∷ Bx2-41 ∷ Toff423 ∷ CCZ234 ∷ Bx2-41 ∷ []) (refl) ▸
       at 4 1 (CZ14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 2 6 (CCZ123 ∷ []) (sym (wl1319 (lit c4))) ▸
       at 2 1 (CCZ023 ∷ Toff023 ∷ CZ01 ∷ Toff023 ∷ CCZ023 ∷ CZ01 ∷ []) (sym (wl1155 (lit c4))) ▸
       at 4 1 (Bx2-01 ∷ []) (refl) ▸
       at 7 1 (Bx2-01 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ024 ∷ Toff204 ∷ CCZ023 ∷ Toff023 ∷ Bx2-01 ∷ Toff023 ∷ CCZ023 ∷ Bx2-01 ∷ Toff204 ∷ CCZ024 ∷ Bx4-231 ∷ []) (CCZ024 ∷ Toff204 ∷ Bx0-231 ∷ Toff204 ∷ CCZ024 ∷ CCZ023 ∷ Toff023 ∷ Bx2-01 ∷ Toff023 ∷ CCZ023 ∷ Bx2-01 ∷ [])
  b1 = at 2 6 (Bx0-231 ∷ []) (refl) ▸
       at 5 1 (CCZ234 ∷ Toff423 ∷ Bx2-41 ∷ Toff423 ∷ CCZ234 ∷ Bx2-41 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 10 1 (CZ14 ∷ []) (refl) ▸
       at 5 6 (CCZ123 ∷ []) (sym (wl1319 (lit c4))) ▸
       at 5 1 (CCZ023 ∷ Toff023 ∷ CZ01 ∷ Toff023 ∷ CCZ023 ∷ CZ01 ∷ []) (sym (wl1155 (lit c4))) ▸
       at 7 1 (Bx2-01 ∷ []) (refl) ▸
       at 10 1 (Bx2-01 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ024 ∷ Toff204 ∷ Bx0-231 ∷ Toff204 ∷ CCZ024 ∷ CCZ023 ∷ Toff023 ∷ Bx2-01 ∷ Toff023 ∷ CCZ023 ∷ Bx2-01 ∷ []) (Bx2-0431 ∷ [])
  b2 = at 5 6 (Bx0-231 ∷ []) (refl) ▸
       at 0 6 (Bx2-0431 ∷ []) (refl) ▸ done


-- P-box @02102441: 8 steps
lem-P-box-at02102441 : Ws → ⟪ (Toff213 ∷ Bx2-0431 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0431 ∷ []) ⟫ʷ
lem-P-box-at02102441 c4 = run b0
  where
  b0 : Chain (Toff213 ∷ Bx2-0431 ∷ Toff213 ∷ []) (Bx2-0431 ∷ [])
  b0 = at 1 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-box-tQ-at02102441 c4) ▸
       at 0 2 (Toff204 ∷ Toff213 ∷ []) (sym (lem-tP-at02102441 c4)) ▸
       at 1 2 (CCZ123 ∷ CZ13 ∷ Toff213 ∷ []) (sym (wl0912 (lit c4))) ▸
       at 3 2 (Toff204 ∷ Toff213 ∷ []) (sym (lem-tP-at02102441 c4)) ▸
       at 4 3 (CCZ123 ∷ CZ13 ∷ []) (sym (wl0913 (lit c4))) ▸
       at 2 2 (Toff204 ∷ CZ13 ∷ []) (lem-comm-CZ13-TOFF204 (lit c4)) ▸
       at 3 3 (CCZ123 ∷ []) (sym (wl0914 (lit c4))) ▸
       at 0 4 (Bx2-0431 ∷ []) (sym (lem-box-tQ-at02102441 c4)) ▸ done


-- cQ @02132130: 7 steps
lem-cQ-at02132130 : Ws → ⟪ (CCZ123 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ CCZ123 ∷ []) ⟫ʷ
lem-cQ-at02132130 c4 = run b0
  where
  b0 : Chain (CCZ123 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ123 ∷ [])
  b0 = at 0 1 (CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ []) (wl0297 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ CS23 ∷ []) (sym (wp0092 c4)) ▸
       at 3 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ CS12⁻ ∷ []) (sym (wp0087 c4)) ▸
       at 1 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸
       at 0 2 (CCZ024 ∷ CS12 ∷ []) (sym (wp0081 c4)) ▸
       at 1 5 (CCZ123 ∷ []) (sym (wl0297 (lit c4))) ▸ done


-- box-tQ @02132130: 13 steps
lem-box-tQ-at02132130 : Ws → ⟪ (Bx2-3104 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ []) ⟫ʷ
lem-box-tQ-at02132130 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx2-3104 ∷ []) (CCZ123 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ CCZ023 ∷ Toff302 ∷ CZ34 ∷ Toff302 ∷ CCZ023 ∷ CZ34 ∷ [])
  b0 = at 0 1 (CCZ123 ∷ Toff213 ∷ Bx3-204 ∷ Toff213 ∷ CCZ123 ∷ Bx3-204 ∷ []) (refl) ▸
       at 2 1 (CCZ023 ∷ Toff302 ∷ Bx2-34 ∷ Toff302 ∷ CCZ023 ∷ Bx2-34 ∷ []) (refl) ▸
       at 4 1 (CZ34 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 2 6 (CCZ024 ∷ []) (wp0131 c4) ▸
       at 5 1 (CCZ023 ∷ Toff302 ∷ Bx2-34 ∷ Toff302 ∷ CCZ023 ∷ Bx2-34 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 10 1 (CZ34 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ123 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ CCZ023 ∷ Toff302 ∷ CZ34 ∷ Toff302 ∷ CCZ023 ∷ CZ34 ∷ []) (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ [])
  b1 = at 5 6 (CCZ024 ∷ []) (wp0131 c4) ▸
       at 0 2 (Toff213 ∷ CCZ123 ∷ CZ13 ∷ []) (wl0915 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ CZ13 ∷ []) (lem-comm-CZ13-CCZ024 (lit c4)) ▸
       at 1 2 (CCZ024 ∷ CCZ123 ∷ []) (lem-cQ-at02132130 c4) ▸
       at 2 4 (Toff213 ∷ []) (wl0916 (lit c4)) ▸ done


-- pairs @02102441: 4 steps
lem-pairs-at02102441 : Ws → ⟪ (Bx2-0431 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3104 ∷ []) ⟫ʷ
lem-pairs-at02102441 c4 = run b0
  where
  b0 : Chain (Bx2-0431 ∷ []) (Bx2-3104 ∷ [])
  b0 = at 0 1 (Toff213 ∷ Bx2-0431 ∷ Toff213 ∷ []) (sym (lem-P-box-at02102441 c4)) ▸
       at 1 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at02102441 c4) ▸
       at 4 2 [] (wl0180 (lit c4)) ▸
       at 0 4 (Bx2-3104 ∷ []) (sym (lem-box-tQ-at02132130 c4)) ▸ done


-- CXbc-box @02132130: 17 steps
lem-CXbc-box-at02132130 : Ws → ⟪ (CX10 ∷ Bx2-3104 ∷ CX10 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3104 ∷ CCZ134 ∷ []) ⟫ʷ
lem-CXbc-box-at02132130 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX10 ∷ Bx2-3104 ∷ CX10 ∷ []) (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CX10 ∷ CCZ124 ∷ CS14 ∷ CX31 ∷ CS14⁻ ∷ CCZ024 ∷ CX31 ∷ CS34 ∷ CX10 ∷ [])
  b0 = at 1 1 (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ []) (lem-box-tQ-at02132130 c4) ▸
       at 0 2 (Toff213 ∷ CX10 ∷ []) (wl0920 (lit c4)) ▸
       at 1 2 (CCZ024 ∷ CX10 ∷ CCZ124 ∷ []) (sym (wp1190 c4)) ▸
       at 3 2 (Toff213 ∷ CCZ124 ∷ CCZ134 ∷ []) (wl1336 (lit c4)) ▸
       at 2 2 (Toff213 ∷ CX10 ∷ []) (wl0920 (lit c4)) ▸
       at 5 1 (CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ []) (wl0831 (lit c4)) ▸
       at 9 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 8 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸ done

  b1 : Chain (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CX10 ∷ CCZ124 ∷ CS14 ∷ CX31 ∷ CS14⁻ ∷ CCZ024 ∷ CX31 ∷ CS34 ∷ CX10 ∷ []) (Bx2-3104 ∷ CX10 ∷ CCZ134 ∷ CX10 ∷ [])
  b1 = at 7 2 (CCZ024 ∷ CS14⁻ ∷ []) (sym (wp0746 c4)) ▸
       at 6 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ CS14 ∷ []) (sym (wp0034 c4)) ▸
       at 6 5 (CCZ134 ∷ []) (sym (wl0831 (lit c4))) ▸
       at 4 2 (CCZ024 ∷ CCZ124 ∷ []) (sym (wp0827 c4)) ▸
       at 3 2 (CCZ024 ∷ CX10 ∷ CCZ124 ∷ []) (sym (wp1190 c4)) ▸
       at 4 3 (CX10 ∷ []) (wp1191 c4) ▸
       at 0 4 (Bx2-3104 ∷ []) (sym (lem-box-tQ-at02132130 c4)) ▸ done

  b2 : Chain (Bx2-3104 ∷ CX10 ∷ CCZ134 ∷ CX10 ∷ []) (Bx2-3104 ∷ CCZ134 ∷ [])
  b2 = at 1 3 (CCZ134 ∷ []) (sym (wp0505 c4)) ▸ done


-- CXcb-box @02132130: 18 steps
lem-CXcb-box-at02132130 : Ws → ⟪ (CX01 ∷ Bx2-3104 ∷ CX01 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3104 ∷ CCZ034 ∷ []) ⟫ʷ
lem-CXcb-box-at02132130 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX01 ∷ Bx2-3104 ∷ CX01 ∷ []) (Toff213 ∷ CCZ024 ∷ CX01 ∷ Toff203 ∷ CS04 ∷ CX30 ∷ Toff213 ∷ CS04⁻ ∷ CX30 ∷ CS34 ∷ CCZ024 ∷ CX01 ∷ [])
  b0 = at 1 1 (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ []) (lem-box-tQ-at02132130 c4) ▸
       at 0 2 (Toff213 ∷ CX01 ∷ Toff203 ∷ []) (wl1337 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ Toff203 ∷ CCZ034 ∷ []) (sym (wp1192 c4)) ▸
       at 1 2 (CCZ024 ∷ CX01 ∷ []) (sym (wp0022 c4)) ▸
       at 4 1 (CS04 ∷ CX30 ∷ CS04⁻ ∷ CX30 ∷ CS34 ∷ []) (wp1193 c4) ▸
       at 8 2 (Toff213 ∷ CS34 ∷ []) (wl0808 (lit c4)) ▸
       at 7 2 (Toff213 ∷ CX30 ∷ []) (wl0917 (lit c4)) ▸
       at 6 2 (Toff213 ∷ CS04⁻ ∷ []) (lem-comm-CSd04-TOFF213 (lit c4)) ▸ done

  b1 : Chain (Toff213 ∷ CCZ024 ∷ CX01 ∷ Toff203 ∷ CS04 ∷ CX30 ∷ Toff213 ∷ CS04⁻ ∷ CX30 ∷ CS34 ∷ CCZ024 ∷ CX01 ∷ []) (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ CX01 ∷ CCZ034 ∷ CX01 ∷ [])
  b1 = at 5 2 (Toff213 ∷ CX30 ∷ []) (wl0917 (lit c4)) ▸
       at 4 2 (Toff213 ∷ CS04 ∷ []) (lem-comm-CS04-TOFF213 (lit c4)) ▸
       at 5 5 (CCZ034 ∷ []) (sym (wp1193 c4)) ▸
       at 3 2 (Toff213 ∷ Toff203 ∷ []) (wl1338 (lit c4)) ▸
       at 2 2 (Toff213 ∷ CX01 ∷ Toff203 ∷ []) (wl1337 (lit c4)) ▸
       at 3 3 (CX01 ∷ []) (wl1339 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ CCZ034 ∷ []) (sym (wp0109 c4)) ▸
       at 3 2 (CCZ024 ∷ CX01 ∷ []) (sym (wp0022 c4)) ▸ done

  b2 : Chain (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ CX01 ∷ CCZ034 ∷ CX01 ∷ []) (Bx2-3104 ∷ CCZ034 ∷ [])
  b2 = at 0 4 (Bx2-3104 ∷ []) (sym (lem-box-tQ-at02132130 c4)) ▸
       at 1 3 (CCZ034 ∷ []) (sym (wp0499 c4)) ▸ done

