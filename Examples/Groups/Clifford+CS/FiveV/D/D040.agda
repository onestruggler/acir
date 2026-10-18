{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.FiveV.D.D040 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.FiveV.WinSig using (Ws ; lit ; wl0175 ; wl0179 ; wl0199 ; wl0204 ; wl0263 ; wl0272 ; wl0277 ; wl0278 ; wl0279 ; wl0280 ; wl0281 ; wl0282 ; wl0283 ; wl0285 ; wl0287 ; wl0298 ; wl0305 ; wl0327 ; wl0330 ; wl0332 ; wl0334 ; wl0336 ; wl0344 ; wl0348 ; wl0433 ; wl0436 ; wl0441 ; wl0451 ; wl0452 ; wl0477 ; wl0492 ; wl0499 ; wl0501 ; wl0508 ; wl0519 ; wl0520 ; wl0527 ; wl0616 ; wl0620 ; wl0621 ; wl0624 ; wl0625 ; wl0629 ; wl0630 ; wl0631 ; wl0632 ; wl0633 ; wl0634 ; wl0635 ; wl0636 ; wl0637 ; wl0638 ; wl0639 ; wl0644 ; wl0667 ; wl0670 ; wl0696 ; wl0698 ; wl0749 ; wl0750 ; wl0765 ; wl0774 ; wl0778 ; wl0781 ; wl0782 ; wl0783 ; wl0784 ; wl0785 ; wl0786 ; wl0787 ; wl0788 ; wl0829 ; wl0871 ; wl0955 ; wl0958 ; wl0974 ; wl0989 ; wl0990 ; wl1213 ; wl1235 ; wl1236 ; wl1253 ; wl1254 ; wl1255 ; wl1256 ; wl1284 ; wl1303 ; wl1324 ; wl1343 ; wl1347 ; wl1356 ; wl1366 ; wl1379 ; wl1380 ; wl1381 ; wl1382 ; wl1383 ; wl1384 ; wl1385 ; wl1386 ; wl1387 ; wl1388 ; wl1389 ; wl1390 ; wl1391 ; wl1392 ; wl1393 ; wl1394 ; wl1395 ; wl1396 ; wl1397 ; wp0003 ; wp0008 ; wp0048 ; wp0056 ; wp0057 ; wp0066 ; wp0102 ; wp0103 ; wp0108 ; wp0111 ; wp0122 ; wp0124 ; wp0129 ; wp0130 ; wp0131 ; wp0161 ; wp0203 ; wp0206 ; wp0208 ; wp0221 ; wp0231 ; wp0262 ; wp0294 ; wp0300 ; wp0301 ; wp0302 ; wp0341 ; wp0342 ; wp0357 ; wp0363 ; wp0379 ; wp0513 ; wp0514 ; wp0515 ; wp0540 ; wp0543 ; wp0546 ; wp0550 ; wp0559 ; wp0562 ; wp0574 ; wp0575 ; wp0661 ; wp0687 ; wp0702 ; wp0703 ; wp0795 ; wp0817 ; wp0822 ; wp0948 ; wp0960 ; wp0963 ; wp1035 ; wp1038 ; wp1058 ; wp1065 ; wp1068 ; wp1114 ; wp1150 ; wp1159 ; wp1173 ; wp1174 ; wp1187 ; wp1189 ; wp1193 ; wp1216 ; wp1217 ; wp1218 ; wp1219 ; wp1220 ; wp1221 ; wp1222 ; wp1223 ; wp1224 ; wp1225 ; wp1226 ; wp1227 ; wp1228 ; wp1229 ; wp1230 ; wp1231 ; wp1232 ; wp1233 ; wp1234 ; wp1235 ; wp1236 ; wp1237 ; wp1238 ; wp1239 ; wp1240 ; wp1241 ; wp1242 ; wp1243 ; wp1244 ; wp1245 ; wp1246 ; wp1247 ; wp1248)
open import Examples.Groups.Clifford+CS.FiveV.Chain
open import Examples.Groups.Clifford+CS.FiveV.D.D001 using (lem-box-perm-2134)
open import Examples.Groups.Clifford+CS.FiveV.D.D002 using (lem-box-cP-at14233142 ; lem-pairs-at14233142 ; lem-sym-ab-at13243142 ; lem-sym-bc-at14233142)
open import Examples.Groups.Clifford+CS.FiveV.D.D003 using (lem-sym-ab-at243243)
open import Examples.Groups.Clifford+CS.FiveV.D.D004 using (lem-box-cP-at0330 ; lem-pairs-at0330 ; lem-pairs-at3443 ; lem-sym-ab-at14233142)
open import Examples.Groups.Clifford+CS.FiveV.D.D005 using (lem-box-cP-at0310243142 ; lem-box-tQ-at032032 ; lem-pairs-at0310243142 ; lem-sym-ab-at03102132 ; lem-sym-ab-at032032 ; lem-sym-bc-at032032 ; lem-sym-bc-at0330)
open import Examples.Groups.Clifford+CS.FiveV.D.D006 using (lem-box-tQ-at14213243)
open import Examples.Groups.Clifford+CS.FiveV.D.D007 using (lem-sym-bc-at243243)
open import Examples.Groups.Clifford+CS.FiveV.D.D008 using (lem-box-perm-2314-at0310243142 ; lem-box-perm-3124-at0314213042 ; lem-box-tQ-at0314213042)
open import Examples.Groups.Clifford+CS.FiveV.D.D009 using (lem-box-perm-2341-at03102132 ; lem-box-tQ-at033440)
open import Examples.Groups.Clifford+CS.FiveV.D.D010 using (lem-box-tQ-at0220 ; lem-sym-ab-at021021 ; lem-sym-ab-at0220 ; lem-sym-bc-at022330)
open import Examples.Groups.Clifford+CS.FiveV.D.D011 using (lem-box-box-1-at021021 ; lem-sym-bc-at0220)
open import Examples.Groups.Clifford+CS.FiveV.D.D012 using (lem-sym-ab-at14213243)
open import Examples.Groups.Clifford+CS.FiveV.D.D014 using (lem-sym-bc-at03102132)
open import Examples.Groups.Clifford+CS.FiveV.D.D022 using (lem-sym-bc-at0310243142)
open import Examples.Groups.Clifford+CS.FiveV.D.D023 using (lem-sym-bc-at0310213442)
open import Examples.Groups.Clifford+CS.FiveV.D.D024 using (lem-sym-bc-at3443)
open import Examples.Groups.Clifford+CS.FiveV.D.D030 using (lem-box-tQ-at031031 ; lem-sym-ab-at03122031 ; lem-sym-bc-at031031)
open import Examples.Groups.Clifford+CS.FiveV.D.D033 using (lem-L-CCZ-0)
open import Examples.Groups.Clifford+CS.FiveV.D.D034 using (lem-box-cP-at031031 ; lem-tP-at031031)
open import Examples.Groups.Clifford+CS.FiveV.D.D035 using (lem-box-cP-at02132130 ; lem-box-tQ-at021021)
open import Examples.Groups.Clifford+CS.FiveV.D.D036 using (lem-L-CCZ013-0)
open import Examples.Groups.Clifford+CS.FiveV.D.D039 using (lem-L-CCZ-1 ; lem-box-perm-2134-at1221)
open import Examples.Groups.Clifford+CS.FiveV.D.R001 using (lem-comm-CX14-CCZ023)
open import Examples.Groups.Clifford+CS.FiveV.D.R002 using (lem-comm-CSd23-TOFF014 ; lem-comm-CZ14-CCZ023)
open import Examples.Groups.Clifford+CS.FiveV.D.R003 using (lem-comm-CS12-CCZ034 ; lem-comm-CSd04-CCZ123 ; lem-comm-CSd12-CCZ034 ; lem-comm-SWAP13-BOX⟨0·42⟩)
open import Examples.Groups.Clifford+CS.FiveV.D.R004 using (lem-comm-CS04-CCZ123 ; lem-comm-CS23-TOFF014 ; lem-comm-CSd03-TOFF214 ; lem-comm-CSd14-TOFF302 ; lem-comm-CX03-CCZ124 ; lem-comm-CX04-TOFF312 ; lem-comm-CX41-CCZ023 ; lem-comm-CZ02-TOFF314 ; lem-comm-CZ14-TOFF302 ; lem-comm-TOFF203-CSd14 ; lem-comm-TOFF314-CSd02)
open import Examples.Groups.Clifford+CS.FiveV.D.R005 using (lem-comm-CK40-TOFF312 ; lem-comm-CX21-TOFF304 ; lem-comm-CX24-TOFF301 ; lem-comm-CX31-TOFF204)
open import Examples.Groups.Clifford+CS.FiveV.D.R006 using (lem-comm-CX32-TOFF014 ; lem-comm-SWAP13-BOX⟨2·04⟩)
-- nf-toff-ccz@0: 5 steps
lem-nf-toff-cczat0 : Ws → ⟪ (CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ Bx2-0134 ∷ []) ⟫ʷ
lem-nf-toff-cczat0 c4 = run b0
  where
  b0 : Chain (CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ []) (Bx0-1234 ∷ Bx2-0134 ∷ [])
  b0 = at 0 75 (Bx2-0134 ∷ []) (lem-L-CCZ013-0 c4) ▸
       at 1 45 (Bx0-1234 ∷ []) (lem-L-CCZ-1 c4) ▸
       at 1 1 (Bx0-2134 ∷ []) (lem-box-perm-2134 c4) ▸
       at 0 2 (Bx0-2134 ∷ Bx2-0134 ∷ []) (lem-box-box-1-at021021 c4) ▸
       at 0 1 (Bx0-1234 ∷ []) (lem-box-perm-2134-at1221 c4) ▸ done


-- CK-box @033440: 6 steps
lem-CK-box-at033440 : Ws → ⟪ (CK40 ∷ Bx3-1240 ∷ CK40⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ []) ⟫ʷ
lem-CK-box-at033440 c4 = run b0
  where
  b0 : Chain (CK40 ∷ Bx3-1240 ∷ CK40⁻ ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ [])
  b0 = at 1 1 (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ []) (lem-box-tQ-at033440 c4) ▸
       at 0 2 (Toff312 ∷ CK40 ∷ []) (lem-comm-CK40-TOFF312 (lit c4)) ▸
       at 1 2 (Toff034 ∷ CK40 ∷ []) (wp1216 c4) ▸
       at 2 2 (Toff312 ∷ CK40 ∷ []) (lem-comm-CK40-TOFF312 (lit c4)) ▸
       at 3 2 (Toff034 ∷ CK40 ∷ []) (wp1216 c4) ▸
       at 4 2 [] (wp1217 c4) ▸ done


-- L-Toff-0: 4 steps
lem-L-Toff-0 : Ws → ⟪ (CK40 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK40 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ []) ⟫ʷ
lem-L-Toff-0 c4 = run b0
  where
  b0 : Chain (CK40 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK40 ∷ S4 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ [])
  b0 = at 1 45 (Bx3-0124 ∷ []) (lem-L-CCZ-0 c4) ▸
       at 2 2 (CK40⁻ ∷ []) (wp1218 c4) ▸
       at 1 1 (Bx3-1240 ∷ []) (lem-box-perm-2341-at03102132 c4) ▸
       at 0 3 (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ []) (lem-CK-box-at033440 c4) ▸ done


-- box-perm-2134 @021021: 1 steps
lem-box-perm-2134-at021021 : Ws → ⟪ (Bx2-0134 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1034 ∷ []) ⟫ʷ
lem-box-perm-2134-at021021 c4 = run b0
  where
  b0 : Chain (Bx2-0134 ∷ []) (Bx2-1034 ∷ [])
  b0 = at 0 1 (Bx2-1034 ∷ []) (lem-sym-ab-at021021 c4) ▸ done


-- box-perm-1324 @032032: 1 steps
lem-box-perm-1324-at032032 : Ws → ⟪ (Bx3-1024 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1204 ∷ []) ⟫ʷ
lem-box-perm-1324-at032032 c4 = run b0
  where
  b0 : Chain (Bx3-1024 ∷ []) (Bx3-1204 ∷ [])
  b0 = at 0 1 (Bx3-1204 ∷ []) (lem-sym-bc-at032032 c4) ▸ done


-- sym-ab @0330: 18 steps
lem-sym-ab-at0330 : Ws → ⟪ (Bx3-1204 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2104 ∷ []) ⟫ʷ
lem-sym-ab-at0330 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx3-1204 ∷ []) (CCZ123 ∷ Toff312 ∷ CCZ023 ∷ Toff203 ∷ Bx3-24 ∷ Toff203 ∷ CCZ023 ∷ Bx3-24 ∷ Toff312 ∷ CCZ123 ∷ Bx1-304 ∷ [])
  b0 = at 0 1 (CCZ123 ∷ Toff312 ∷ Bx1-304 ∷ Toff312 ∷ CCZ123 ∷ Bx1-304 ∷ []) (refl) ▸
       at 2 1 (CCZ013 ∷ Toff103 ∷ Bx3-14 ∷ Toff103 ∷ CCZ013 ∷ Bx3-14 ∷ []) (refl) ▸
       at 4 1 (CZ14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 2 6 (CCZ034 ∷ []) (wp0008 c4) ▸
       at 2 1 (CCZ023 ∷ Toff203 ∷ CZ24 ∷ Toff203 ∷ CCZ023 ∷ CZ24 ∷ []) (sym (wp0111 c4)) ▸
       at 4 1 (Bx3-24 ∷ []) (refl) ▸
       at 7 1 (Bx3-24 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ123 ∷ Toff312 ∷ CCZ023 ∷ Toff203 ∷ Bx3-24 ∷ Toff203 ∷ CCZ023 ∷ Bx3-24 ∷ Toff312 ∷ CCZ123 ∷ Bx1-304 ∷ []) (CCZ123 ∷ Toff312 ∷ Bx2-304 ∷ Toff312 ∷ CCZ123 ∷ CCZ023 ∷ Toff203 ∷ Bx3-24 ∷ Toff203 ∷ CCZ023 ∷ Bx3-24 ∷ [])
  b1 = at 2 6 (Bx2-304 ∷ []) (refl) ▸
       at 5 1 (CCZ013 ∷ Toff103 ∷ Bx3-14 ∷ Toff103 ∷ CCZ013 ∷ Bx3-14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 10 1 (CZ14 ∷ []) (refl) ▸
       at 5 6 (CCZ034 ∷ []) (wp0008 c4) ▸
       at 5 1 (CCZ023 ∷ Toff203 ∷ CZ24 ∷ Toff203 ∷ CCZ023 ∷ CZ24 ∷ []) (sym (wp0111 c4)) ▸
       at 7 1 (Bx3-24 ∷ []) (refl) ▸
       at 10 1 (Bx3-24 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ123 ∷ Toff312 ∷ Bx2-304 ∷ Toff312 ∷ CCZ123 ∷ CCZ023 ∷ Toff203 ∷ Bx3-24 ∷ Toff203 ∷ CCZ023 ∷ Bx3-24 ∷ []) (Bx3-2104 ∷ [])
  b2 = at 5 6 (Bx2-304 ∷ []) (refl) ▸
       at 0 6 (Bx3-2104 ∷ []) (refl) ▸ done


-- box-perm-3124 @032032: 2 steps
lem-box-perm-3124-at032032 : Ws → ⟪ (Bx3-1024 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2104 ∷ []) ⟫ʷ
lem-box-perm-3124-at032032 c4 = run b0
  where
  b0 : Chain (Bx3-1024 ∷ []) (Bx3-2104 ∷ [])
  b0 = at 0 1 (Bx3-1204 ∷ []) (lem-sym-bc-at032032 c4) ▸
       at 0 1 (Bx3-2104 ∷ []) (lem-sym-ab-at0330 c4) ▸ done


-- sym-ab @022330: 18 steps
lem-sym-ab-at022330 : Ws → ⟪ (Bx2-1304 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3104 ∷ []) ⟫ʷ
lem-sym-ab-at022330 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx2-1304 ∷ []) (CCZ123 ∷ Toff213 ∷ CCZ023 ∷ Toff302 ∷ Bx2-34 ∷ Toff302 ∷ CCZ023 ∷ Bx2-34 ∷ Toff213 ∷ CCZ123 ∷ Bx1-204 ∷ [])
  b0 = at 0 1 (CCZ123 ∷ Toff213 ∷ Bx1-204 ∷ Toff213 ∷ CCZ123 ∷ Bx1-204 ∷ []) (refl) ▸
       at 2 1 (CCZ012 ∷ Toff102 ∷ Bx2-14 ∷ Toff102 ∷ CCZ012 ∷ Bx2-14 ∷ []) (refl) ▸
       at 4 1 (CZ14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 2 6 (CCZ024 ∷ []) (wp0130 c4) ▸
       at 2 1 (CCZ023 ∷ Toff302 ∷ CZ34 ∷ Toff302 ∷ CCZ023 ∷ CZ34 ∷ []) (sym (wp0131 c4)) ▸
       at 4 1 (Bx2-34 ∷ []) (refl) ▸
       at 7 1 (Bx2-34 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ123 ∷ Toff213 ∷ CCZ023 ∷ Toff302 ∷ Bx2-34 ∷ Toff302 ∷ CCZ023 ∷ Bx2-34 ∷ Toff213 ∷ CCZ123 ∷ Bx1-204 ∷ []) (CCZ123 ∷ Toff213 ∷ Bx3-204 ∷ Toff213 ∷ CCZ123 ∷ CCZ023 ∷ Toff302 ∷ Bx2-34 ∷ Toff302 ∷ CCZ023 ∷ Bx2-34 ∷ [])
  b1 = at 2 6 (Bx3-204 ∷ []) (refl) ▸
       at 5 1 (CCZ012 ∷ Toff102 ∷ Bx2-14 ∷ Toff102 ∷ CCZ012 ∷ Bx2-14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 10 1 (CZ14 ∷ []) (refl) ▸
       at 5 6 (CCZ024 ∷ []) (wp0130 c4) ▸
       at 5 1 (CCZ023 ∷ Toff302 ∷ CZ34 ∷ Toff302 ∷ CCZ023 ∷ CZ34 ∷ []) (sym (wp0131 c4)) ▸
       at 7 1 (Bx2-34 ∷ []) (refl) ▸
       at 10 1 (Bx2-34 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ123 ∷ Toff213 ∷ Bx3-204 ∷ Toff213 ∷ CCZ123 ∷ CCZ023 ∷ Toff302 ∷ Bx2-34 ∷ Toff302 ∷ CCZ023 ∷ Bx2-34 ∷ []) (Bx2-3104 ∷ [])
  b2 = at 5 6 (Bx3-204 ∷ []) (refl) ▸
       at 0 6 (Bx2-3104 ∷ []) (refl) ▸ done


-- box-perm-3124 @0220: 2 steps
lem-box-perm-3124-at0220 : Ws → ⟪ (Bx2-1034 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3104 ∷ []) ⟫ʷ
lem-box-perm-3124-at0220 c4 = run b0
  where
  b0 : Chain (Bx2-1034 ∷ []) (Bx2-3104 ∷ [])
  b0 = at 0 1 (Bx2-1304 ∷ []) (lem-sym-bc-at0220 c4) ▸
       at 0 1 (Bx2-3104 ∷ []) (lem-sym-ab-at022330 c4) ▸ done


-- sym-ab @03122130: 18 steps
lem-sym-ab-at03122130 : Ws → ⟪ (Bx3-2104 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1204 ∷ []) ⟫ʷ
lem-sym-ab-at03122130 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx3-2104 ∷ []) (CCZ123 ∷ Toff312 ∷ CCZ013 ∷ Toff103 ∷ Bx3-14 ∷ Toff103 ∷ CCZ013 ∷ Bx3-14 ∷ Toff312 ∷ CCZ123 ∷ Bx2-304 ∷ [])
  b0 = at 0 1 (CCZ123 ∷ Toff312 ∷ Bx2-304 ∷ Toff312 ∷ CCZ123 ∷ Bx2-304 ∷ []) (refl) ▸
       at 2 1 (CCZ023 ∷ Toff203 ∷ Bx3-24 ∷ Toff203 ∷ CCZ023 ∷ Bx3-24 ∷ []) (refl) ▸
       at 4 1 (CZ24 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 2 6 (CCZ034 ∷ []) (wp0111 c4) ▸
       at 2 1 (CCZ013 ∷ Toff103 ∷ CZ14 ∷ Toff103 ∷ CCZ013 ∷ CZ14 ∷ []) (sym (wp0008 c4)) ▸
       at 4 1 (Bx3-14 ∷ []) (refl) ▸
       at 7 1 (Bx3-14 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ123 ∷ Toff312 ∷ CCZ013 ∷ Toff103 ∷ Bx3-14 ∷ Toff103 ∷ CCZ013 ∷ Bx3-14 ∷ Toff312 ∷ CCZ123 ∷ Bx2-304 ∷ []) (CCZ123 ∷ Toff312 ∷ Bx1-304 ∷ Toff312 ∷ CCZ123 ∷ CCZ013 ∷ Toff103 ∷ Bx3-14 ∷ Toff103 ∷ CCZ013 ∷ Bx3-14 ∷ [])
  b1 = at 2 6 (Bx1-304 ∷ []) (refl) ▸
       at 5 1 (CCZ023 ∷ Toff203 ∷ Bx3-24 ∷ Toff203 ∷ CCZ023 ∷ Bx3-24 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 10 1 (CZ24 ∷ []) (refl) ▸
       at 5 6 (CCZ034 ∷ []) (wp0111 c4) ▸
       at 5 1 (CCZ013 ∷ Toff103 ∷ CZ14 ∷ Toff103 ∷ CCZ013 ∷ CZ14 ∷ []) (sym (wp0008 c4)) ▸
       at 7 1 (Bx3-14 ∷ []) (refl) ▸
       at 10 1 (Bx3-14 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ123 ∷ Toff312 ∷ Bx1-304 ∷ Toff312 ∷ CCZ123 ∷ CCZ013 ∷ Toff103 ∷ Bx3-14 ∷ Toff103 ∷ CCZ013 ∷ Bx3-14 ∷ []) (Bx3-1204 ∷ [])
  b2 = at 5 6 (Bx1-304 ∷ []) (refl) ▸
       at 0 6 (Bx3-1204 ∷ []) (refl) ▸ done


-- sym-ab @0310213442: 18 steps
lem-sym-ab-at0310213442 : Ws → ⟪ (Bx3-0142 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1042 ∷ []) ⟫ʷ
lem-sym-ab-at0310213442 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx3-0142 ∷ []) (CCZ013 ∷ Toff301 ∷ CCZ134 ∷ Toff134 ∷ Bx3-12 ∷ Toff134 ∷ CCZ134 ∷ Bx3-12 ∷ Toff301 ∷ CCZ013 ∷ Bx0-342 ∷ [])
  b0 = at 0 1 (CCZ013 ∷ Toff301 ∷ Bx0-342 ∷ Toff301 ∷ CCZ013 ∷ Bx0-342 ∷ []) (refl) ▸
       at 2 1 (CCZ034 ∷ Toff034 ∷ Bx3-02 ∷ Toff034 ∷ CCZ034 ∷ Bx3-02 ∷ []) (refl) ▸
       at 4 1 (CZ02 ∷ []) (refl) ▸
       at 7 1 (CZ02 ∷ []) (refl) ▸
       at 2 6 (CCZ234 ∷ []) (wp1068 c4) ▸
       at 2 1 (CCZ134 ∷ Toff134 ∷ CZ12 ∷ Toff134 ∷ CCZ134 ∷ CZ12 ∷ []) (sym (wl1379 (lit c4))) ▸
       at 4 1 (Bx3-12 ∷ []) (refl) ▸
       at 7 1 (Bx3-12 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ013 ∷ Toff301 ∷ CCZ134 ∷ Toff134 ∷ Bx3-12 ∷ Toff134 ∷ CCZ134 ∷ Bx3-12 ∷ Toff301 ∷ CCZ013 ∷ Bx0-342 ∷ []) (CCZ013 ∷ Toff301 ∷ Bx1-342 ∷ Toff301 ∷ CCZ013 ∷ CCZ134 ∷ Toff134 ∷ Bx3-12 ∷ Toff134 ∷ CCZ134 ∷ Bx3-12 ∷ [])
  b1 = at 2 6 (Bx1-342 ∷ []) (refl) ▸
       at 5 1 (CCZ034 ∷ Toff034 ∷ Bx3-02 ∷ Toff034 ∷ CCZ034 ∷ Bx3-02 ∷ []) (refl) ▸
       at 7 1 (CZ02 ∷ []) (refl) ▸
       at 10 1 (CZ02 ∷ []) (refl) ▸
       at 5 6 (CCZ234 ∷ []) (wp1068 c4) ▸
       at 5 1 (CCZ134 ∷ Toff134 ∷ CZ12 ∷ Toff134 ∷ CCZ134 ∷ CZ12 ∷ []) (sym (wl1379 (lit c4))) ▸
       at 7 1 (Bx3-12 ∷ []) (refl) ▸
       at 10 1 (Bx3-12 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ013 ∷ Toff301 ∷ Bx1-342 ∷ Toff301 ∷ CCZ013 ∷ CCZ134 ∷ Toff134 ∷ Bx3-12 ∷ Toff134 ∷ CCZ134 ∷ Bx3-12 ∷ []) (Bx3-1042 ∷ [])
  b2 = at 5 6 (Bx1-342 ∷ []) (refl) ▸
       at 0 6 (Bx3-1042 ∷ []) (refl) ▸ done


-- box-perm-2341 @03122130: 4 steps
lem-box-perm-2341-at03122130 : Ws → ⟪ (Bx3-2104 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1042 ∷ []) ⟫ʷ
lem-box-perm-2341-at03122130 c4 = run b0
  where
  b0 : Chain (Bx3-2104 ∷ []) (Bx3-1042 ∷ [])
  b0 = at 0 1 (Bx3-1204 ∷ []) (lem-sym-ab-at03122130 c4) ▸
       at 0 1 (Bx3-0412 ∷ []) (lem-pairs-at0330 c4) ▸
       at 0 1 (Bx3-0142 ∷ []) (lem-sym-bc-at0310243142 c4) ▸
       at 0 1 (Bx3-1042 ∷ []) (lem-sym-ab-at0310213442 c4) ▸ done


-- cQ @03203442: 7 steps
lem-cQ-at03203442 : Ws → ⟪ (CCZ013 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ CCZ013 ∷ []) ⟫ʷ
lem-cQ-at03203442 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ013 ∷ [])
  b0 = at 0 1 (CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ []) (wl0477 (lit c4)) ▸
       at 4 2 (CCZ234 ∷ CS13 ∷ []) (sym (wl0433 (lit c4))) ▸
       at 3 2 (CCZ234 ∷ CX10 ∷ []) (c₂ (CX₁₀) (CCZ)) ▸
       at 2 2 (CCZ234 ∷ CS03⁻ ∷ []) (sym (wp0363 c4)) ▸
       at 1 2 (CCZ234 ∷ CX10 ∷ []) (c₂ (CX₁₀) (CCZ)) ▸
       at 0 2 (CCZ234 ∷ CS03 ∷ []) (sym (wp0294 c4)) ▸
       at 1 5 (CCZ013 ∷ []) (sym (wl0477 (lit c4))) ▸ done


-- box-tQ @03203442: 13 steps
lem-box-tQ-at03203442 : Ws → ⟪ (Bx3-1042 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ []) ⟫ʷ
lem-box-tQ-at03203442 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-1042 ∷ []) (CCZ013 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ013 ∷ CCZ134 ∷ Toff134 ∷ CZ12 ∷ Toff134 ∷ CCZ134 ∷ CZ12 ∷ [])
  b0 = at 0 1 (CCZ013 ∷ Toff301 ∷ Bx1-342 ∷ Toff301 ∷ CCZ013 ∷ Bx1-342 ∷ []) (refl) ▸
       at 2 1 (CCZ134 ∷ Toff134 ∷ Bx3-12 ∷ Toff134 ∷ CCZ134 ∷ Bx3-12 ∷ []) (refl) ▸
       at 4 1 (CZ12 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 2 6 (CCZ234 ∷ []) (wl1379 (lit c4)) ▸
       at 5 1 (CCZ134 ∷ Toff134 ∷ Bx3-12 ∷ Toff134 ∷ CCZ134 ∷ Bx3-12 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 10 1 (CZ12 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ013 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ013 ∷ CCZ134 ∷ Toff134 ∷ CZ12 ∷ Toff134 ∷ CCZ134 ∷ CZ12 ∷ []) (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ [])
  b1 = at 5 6 (CCZ234 ∷ []) (wl1379 (lit c4)) ▸
       at 0 2 (Toff301 ∷ CCZ013 ∷ CZ01 ∷ []) (wl0519 (lit c4)) ▸
       at 2 2 (CCZ234 ∷ CZ01 ∷ []) (c₂ (CZ) (CCZ)) ▸
       at 1 2 (CCZ234 ∷ CCZ013 ∷ []) (lem-cQ-at03203442 c4) ▸
       at 2 4 (Toff301 ∷ []) (wl0520 (lit c4)) ▸ done


-- sym-ab @03203442: 18 steps
lem-sym-ab-at03203442 : Ws → ⟪ (Bx3-1042 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0142 ∷ []) ⟫ʷ
lem-sym-ab-at03203442 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx3-1042 ∷ []) (CCZ013 ∷ Toff301 ∷ CCZ034 ∷ Toff034 ∷ Bx3-02 ∷ Toff034 ∷ CCZ034 ∷ Bx3-02 ∷ Toff301 ∷ CCZ013 ∷ Bx1-342 ∷ [])
  b0 = at 0 1 (CCZ013 ∷ Toff301 ∷ Bx1-342 ∷ Toff301 ∷ CCZ013 ∷ Bx1-342 ∷ []) (refl) ▸
       at 2 1 (CCZ134 ∷ Toff134 ∷ Bx3-12 ∷ Toff134 ∷ CCZ134 ∷ Bx3-12 ∷ []) (refl) ▸
       at 4 1 (CZ12 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 2 6 (CCZ234 ∷ []) (wl1379 (lit c4)) ▸
       at 2 1 (CCZ034 ∷ Toff034 ∷ CZ02 ∷ Toff034 ∷ CCZ034 ∷ CZ02 ∷ []) (sym (wp1068 c4)) ▸
       at 4 1 (Bx3-02 ∷ []) (refl) ▸
       at 7 1 (Bx3-02 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ013 ∷ Toff301 ∷ CCZ034 ∷ Toff034 ∷ Bx3-02 ∷ Toff034 ∷ CCZ034 ∷ Bx3-02 ∷ Toff301 ∷ CCZ013 ∷ Bx1-342 ∷ []) (CCZ013 ∷ Toff301 ∷ Bx0-342 ∷ Toff301 ∷ CCZ013 ∷ CCZ034 ∷ Toff034 ∷ Bx3-02 ∷ Toff034 ∷ CCZ034 ∷ Bx3-02 ∷ [])
  b1 = at 2 6 (Bx0-342 ∷ []) (refl) ▸
       at 5 1 (CCZ134 ∷ Toff134 ∷ Bx3-12 ∷ Toff134 ∷ CCZ134 ∷ Bx3-12 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 10 1 (CZ12 ∷ []) (refl) ▸
       at 5 6 (CCZ234 ∷ []) (wl1379 (lit c4)) ▸
       at 5 1 (CCZ034 ∷ Toff034 ∷ CZ02 ∷ Toff034 ∷ CCZ034 ∷ CZ02 ∷ []) (sym (wp1068 c4)) ▸
       at 7 1 (Bx3-02 ∷ []) (refl) ▸
       at 10 1 (Bx3-02 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ013 ∷ Toff301 ∷ Bx0-342 ∷ Toff301 ∷ CCZ013 ∷ CCZ034 ∷ Toff034 ∷ Bx3-02 ∷ Toff034 ∷ CCZ034 ∷ Bx3-02 ∷ []) (Bx3-0142 ∷ [])
  b2 = at 5 6 (Bx0-342 ∷ []) (refl) ▸
       at 0 6 (Bx3-0142 ∷ []) (refl) ▸ done


-- box-perm-4123 @03203442: 4 steps
lem-box-perm-4123-at03203442 : Ws → ⟪ (Bx3-1042 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2104 ∷ []) ⟫ʷ
lem-box-perm-4123-at03203442 c4 = run b0
  where
  b0 : Chain (Bx3-1042 ∷ []) (Bx3-2104 ∷ [])
  b0 = at 0 1 (Bx3-0142 ∷ []) (lem-sym-ab-at03203442 c4) ▸
       at 0 1 (Bx3-0412 ∷ []) (lem-sym-bc-at0310213442 c4) ▸
       at 0 1 (Bx3-1204 ∷ []) (lem-pairs-at0310243142 c4) ▸
       at 0 1 (Bx3-2104 ∷ []) (lem-sym-ab-at0330 c4) ▸ done


-- box-box-1 @03122130: 105 steps
lem-box-box-1-at03122130 : Ws → ⟪ (Bx3-2104 ∷ Bx2-3104 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3104 ∷ Bx3-2104 ∷ []) ⟫ʷ
lem-box-box-1-at03122130 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (run b13)))))))))))))
  where
  b0 : Chain (Bx3-2104 ∷ Bx2-3104 ∷ []) (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ123 ∷ Toff204 ∷ CCZ234 ∷ CS04 ∷ CX30 ∷ CS04⁻ ∷ CCZ123 ∷ CX30 ∷ CS34 ∷ Toff204 ∷ [])
  b0 = at 0 1 (Bx3-1042 ∷ []) (lem-box-perm-2341-at03122130 c4) ▸
       at 0 1 (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ []) (lem-box-tQ-at03203442 c4) ▸
       at 4 1 (CCZ123 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ []) (lem-box-cP-at02132130 c4) ▸
       at 3 2 (CCZ123 ∷ CCZ234 ∷ []) (sym (wl0508 (lit c4))) ▸
       at 4 2 (Toff204 ∷ CCZ234 ∷ CCZ034 ∷ []) (wp0559 c4) ▸
       at 6 1 (CS04 ∷ CX30 ∷ CS04⁻ ∷ CX30 ∷ CS34 ∷ []) (wp1193 c4) ▸
       at 10 2 (CCZ123 ∷ CS34 ∷ []) (sym (wl0492 (lit c4))) ▸
       at 9 2 (CCZ123 ∷ CX30 ∷ []) (sym (wl1324 (lit c4))) ▸ done

  b1 : Chain (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ123 ∷ Toff204 ∷ CCZ234 ∷ CS04 ∷ CX30 ∷ CS04⁻ ∷ CCZ123 ∷ CX30 ∷ CS34 ∷ Toff204 ∷ []) (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ234 ∷ [])
  b1 = at 8 2 (CCZ123 ∷ CS04⁻ ∷ []) (lem-comm-CSd04-CCZ123 (lit c4)) ▸
       at 7 2 (CCZ123 ∷ CX30 ∷ []) (sym (wl1324 (lit c4))) ▸
       at 6 2 (CCZ123 ∷ CS04 ∷ []) (lem-comm-CS04-CCZ123 (lit c4)) ▸
       at 7 5 (CCZ034 ∷ []) (sym (wp1193 c4)) ▸
       at 5 2 (CCZ123 ∷ CCZ234 ∷ []) (sym (wl0508 (lit c4))) ▸
       at 6 3 (Toff204 ∷ CCZ234 ∷ []) (wp1219 c4) ▸
       at 3 4 (Bx2-3104 ∷ []) (sym (lem-box-cP-at02132130 c4)) ▸
       at 3 1 (CCZ123 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ []) (lem-box-cP-at02132130 c4) ▸ done

  b2 : Chain (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ234 ∷ []) (Toff301 ∷ CCZ234 ∷ CCZ123 ∷ K3 ∷ CS01 ∷ Toff204 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ K3⁻ ∷ CCZ012 ∷ CCZ014 ∷ CCZ123 ∷ Toff204 ∷ CCZ234 ∷ [])
  b2 = at 2 2 (CCZ123 ∷ Toff301 ∷ CCZ012 ∷ []) (sym (wl1256 (lit c4))) ▸
       at 4 2 (Toff204 ∷ CCZ012 ∷ CCZ014 ∷ []) (wp1150 c4) ▸
       at 3 1 (K3 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ K3⁻ ∷ []) (sym (wl1380 (lit c4))) ▸
       at 9 2 (Toff204 ∷ K3⁻ ∷ []) (wp1220 c4) ▸
       at 8 2 (Toff204 ∷ CS03 ∷ []) (wp0562 c4) ▸
       at 7 2 (Toff204 ∷ CX31 ∷ []) (lem-comm-CX31-TOFF204 (lit c4)) ▸
       at 6 2 (Toff204 ∷ CS01⁻ ∷ []) (wp1221 c4) ▸
       at 5 2 (Toff204 ∷ CX31 ∷ []) (lem-comm-CX31-TOFF204 (lit c4)) ▸ done

  b3 : Chain (Toff301 ∷ CCZ234 ∷ CCZ123 ∷ K3 ∷ CS01 ∷ Toff204 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ K3⁻ ∷ CCZ012 ∷ CCZ014 ∷ CCZ123 ∷ Toff204 ∷ CCZ234 ∷ []) (Toff301 ∷ CCZ234 ∷ CCZ123 ∷ Toff204 ∷ Toff301 ∷ CCZ012 ∷ CS04 ∷ CCZ123 ∷ CX10 ∷ CS04⁻ ∷ CX10 ∷ CS14 ∷ Toff204 ∷ CCZ234 ∷ [])
  b3 = at 4 2 (Toff204 ∷ CS01 ∷ []) (wp0948 c4) ▸
       at 3 2 (Toff204 ∷ K3 ∷ []) (wp1222 c4) ▸
       at 4 7 (Toff301 ∷ []) (wl1380 (lit c4)) ▸
       at 6 1 (CS04 ∷ CX10 ∷ CS04⁻ ∷ CX10 ∷ CS14 ∷ []) (wp0341 c4) ▸
       at 10 2 (CCZ123 ∷ CS14 ∷ []) (sym (wl0765 (lit c4))) ▸
       at 9 2 (CCZ123 ∷ CX10 ∷ []) (sym (wl0616 (lit c4))) ▸
       at 8 2 (CCZ123 ∷ CS04⁻ ∷ []) (lem-comm-CSd04-CCZ123 (lit c4)) ▸
       at 7 2 (CCZ123 ∷ CX10 ∷ []) (sym (wl0616 (lit c4))) ▸ done

  b4 : Chain (Toff301 ∷ CCZ234 ∷ CCZ123 ∷ Toff204 ∷ Toff301 ∷ CCZ012 ∷ CS04 ∷ CCZ123 ∷ CX10 ∷ CS04⁻ ∷ CX10 ∷ CS14 ∷ Toff204 ∷ CCZ234 ∷ []) (Toff301 ∷ CCZ234 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ K3 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ Toff204 ∷ K3⁻ ∷ CCZ014 ∷ CCZ234 ∷ [])
  b4 = at 6 2 (CCZ123 ∷ CS04 ∷ []) (lem-comm-CS04-CCZ123 (lit c4)) ▸
       at 7 5 (CCZ014 ∷ []) (sym (wp0341 c4)) ▸
       at 5 2 (CCZ123 ∷ CCZ012 ∷ []) (wl0298 (lit c4)) ▸
       at 4 2 (CCZ123 ∷ Toff301 ∷ CCZ012 ∷ []) (sym (wl1256 (lit c4))) ▸
       at 5 3 (Toff301 ∷ []) (wl1347 (lit c4)) ▸
       at 6 2 (Toff204 ∷ CCZ014 ∷ []) (wp1174 c4) ▸
       at 5 1 (K3 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ K3⁻ ∷ []) (sym (wl1380 (lit c4))) ▸
       at 11 2 (Toff204 ∷ K3⁻ ∷ []) (wp1220 c4) ▸ done

  b5 : Chain (Toff301 ∷ CCZ234 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ K3 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ Toff204 ∷ K3⁻ ∷ CCZ014 ∷ CCZ234 ∷ []) (Toff301 ∷ CCZ234 ∷ Bx2-3104 ∷ Toff301 ∷ CCZ014 ∷ CCZ234 ∷ [])
  b5 = at 10 2 (Toff204 ∷ CS03 ∷ []) (wp0562 c4) ▸
       at 9 2 (Toff204 ∷ CX31 ∷ []) (lem-comm-CX31-TOFF204 (lit c4)) ▸
       at 8 2 (Toff204 ∷ CS01⁻ ∷ []) (wp1221 c4) ▸
       at 7 2 (Toff204 ∷ CX31 ∷ []) (lem-comm-CX31-TOFF204 (lit c4)) ▸
       at 6 2 (Toff204 ∷ CS01 ∷ []) (wp0948 c4) ▸
       at 5 2 (Toff204 ∷ K3 ∷ []) (wp1222 c4) ▸
       at 6 7 (Toff301 ∷ []) (wl1380 (lit c4)) ▸
       at 2 4 (Bx2-3104 ∷ []) (sym (lem-box-cP-at02132130 c4)) ▸ done

  b6 : Chain (Toff301 ∷ CCZ234 ∷ Bx2-3104 ∷ Toff301 ∷ CCZ014 ∷ CCZ234 ∷ []) (Toff301 ∷ CCZ123 ∷ Toff204 ∷ CCZ234 ∷ CS04 ∷ CCZ123 ∷ CX30 ∷ CS04⁻ ∷ CX30 ∷ CS34 ∷ Toff204 ∷ Toff301 ∷ CCZ014 ∷ CCZ234 ∷ [])
  b6 = at 2 1 (CCZ123 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ []) (lem-box-cP-at02132130 c4) ▸
       at 1 2 (CCZ123 ∷ CCZ234 ∷ []) (sym (wl0508 (lit c4))) ▸
       at 2 2 (Toff204 ∷ CCZ234 ∷ CCZ034 ∷ []) (wp0559 c4) ▸
       at 4 1 (CS04 ∷ CX30 ∷ CS04⁻ ∷ CX30 ∷ CS34 ∷ []) (wp1193 c4) ▸
       at 8 2 (CCZ123 ∷ CS34 ∷ []) (sym (wl0492 (lit c4))) ▸
       at 7 2 (CCZ123 ∷ CX30 ∷ []) (sym (wl1324 (lit c4))) ▸
       at 6 2 (CCZ123 ∷ CS04⁻ ∷ []) (lem-comm-CSd04-CCZ123 (lit c4)) ▸
       at 5 2 (CCZ123 ∷ CX30 ∷ []) (sym (wl1324 (lit c4))) ▸ done

  b7 : Chain (Toff301 ∷ CCZ123 ∷ Toff204 ∷ CCZ234 ∷ CS04 ∷ CCZ123 ∷ CX30 ∷ CS04⁻ ∷ CX30 ∷ CS34 ∷ Toff204 ∷ Toff301 ∷ CCZ014 ∷ CCZ234 ∷ []) (CCZ123 ∷ Toff301 ∷ Toff204 ∷ CCZ012 ∷ CCZ014 ∷ CCZ123 ∷ Toff204 ∷ CCZ234 ∷ Toff301 ∷ CCZ014 ∷ CCZ234 ∷ [])
  b7 = at 4 2 (CCZ123 ∷ CS04 ∷ []) (lem-comm-CS04-CCZ123 (lit c4)) ▸
       at 5 5 (CCZ034 ∷ []) (sym (wp1193 c4)) ▸
       at 3 2 (CCZ123 ∷ CCZ234 ∷ []) (sym (wl0508 (lit c4))) ▸
       at 4 3 (Toff204 ∷ CCZ234 ∷ []) (wp1219 c4) ▸
       at 1 4 (Bx2-3104 ∷ []) (sym (lem-box-cP-at02132130 c4)) ▸
       at 1 1 (CCZ123 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ []) (lem-box-cP-at02132130 c4) ▸
       at 0 2 (CCZ123 ∷ Toff301 ∷ CCZ012 ∷ []) (sym (wl1256 (lit c4))) ▸
       at 2 2 (Toff204 ∷ CCZ012 ∷ CCZ014 ∷ []) (wp1150 c4) ▸ done

  b8 : Chain (CCZ123 ∷ Toff301 ∷ Toff204 ∷ CCZ012 ∷ CCZ014 ∷ CCZ123 ∷ Toff204 ∷ CCZ234 ∷ Toff301 ∷ CCZ014 ∷ CCZ234 ∷ []) (CCZ123 ∷ Toff204 ∷ K3 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ K3⁻ ∷ CCZ012 ∷ CCZ014 ∷ CCZ123 ∷ Toff204 ∷ CCZ234 ∷ Toff301 ∷ CCZ014 ∷ CCZ234 ∷ [])
  b8 = at 1 1 (K3 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ K3⁻ ∷ []) (sym (wl1380 (lit c4))) ▸
       at 7 2 (Toff204 ∷ K3⁻ ∷ []) (wp1220 c4) ▸
       at 6 2 (Toff204 ∷ CS03 ∷ []) (wp0562 c4) ▸
       at 5 2 (Toff204 ∷ CX31 ∷ []) (lem-comm-CX31-TOFF204 (lit c4)) ▸
       at 4 2 (Toff204 ∷ CS01⁻ ∷ []) (wp1221 c4) ▸
       at 3 2 (Toff204 ∷ CX31 ∷ []) (lem-comm-CX31-TOFF204 (lit c4)) ▸
       at 2 2 (Toff204 ∷ CS01 ∷ []) (wp0948 c4) ▸
       at 1 2 (Toff204 ∷ K3 ∷ []) (wp1222 c4) ▸ done

  b9 : Chain (CCZ123 ∷ Toff204 ∷ K3 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ K3⁻ ∷ CCZ012 ∷ CCZ014 ∷ CCZ123 ∷ Toff204 ∷ CCZ234 ∷ Toff301 ∷ CCZ014 ∷ CCZ234 ∷ []) (CCZ123 ∷ Toff204 ∷ Toff301 ∷ CCZ012 ∷ CCZ123 ∷ CCZ014 ∷ Toff204 ∷ CCZ234 ∷ Toff301 ∷ CCZ014 ∷ CCZ234 ∷ [])
  b9 = at 2 7 (Toff301 ∷ []) (wl1380 (lit c4)) ▸
       at 4 1 (CS04 ∷ CX10 ∷ CS04⁻ ∷ CX10 ∷ CS14 ∷ []) (wp0341 c4) ▸
       at 8 2 (CCZ123 ∷ CS14 ∷ []) (sym (wl0765 (lit c4))) ▸
       at 7 2 (CCZ123 ∷ CX10 ∷ []) (sym (wl0616 (lit c4))) ▸
       at 6 2 (CCZ123 ∷ CS04⁻ ∷ []) (lem-comm-CSd04-CCZ123 (lit c4)) ▸
       at 5 2 (CCZ123 ∷ CX10 ∷ []) (sym (wl0616 (lit c4))) ▸
       at 4 2 (CCZ123 ∷ CS04 ∷ []) (lem-comm-CS04-CCZ123 (lit c4)) ▸
       at 5 5 (CCZ014 ∷ []) (sym (wp0341 c4)) ▸ done

  b10 : Chain (CCZ123 ∷ Toff204 ∷ Toff301 ∷ CCZ012 ∷ CCZ123 ∷ CCZ014 ∷ Toff204 ∷ CCZ234 ∷ Toff301 ∷ CCZ014 ∷ CCZ234 ∷ []) (CCZ123 ∷ Toff204 ∷ CCZ123 ∷ K3 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ Toff204 ∷ CX31 ∷ CS03 ∷ K3⁻ ∷ CCZ014 ∷ CCZ234 ∷ Toff301 ∷ CCZ014 ∷ CCZ234 ∷ [])
  b10 = at 3 2 (CCZ123 ∷ CCZ012 ∷ []) (wl0298 (lit c4)) ▸
       at 2 2 (CCZ123 ∷ Toff301 ∷ CCZ012 ∷ []) (sym (wl1256 (lit c4))) ▸
       at 3 3 (Toff301 ∷ []) (wl1347 (lit c4)) ▸
       at 4 2 (Toff204 ∷ CCZ014 ∷ []) (wp1174 c4) ▸
       at 3 1 (K3 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ K3⁻ ∷ []) (sym (wl1380 (lit c4))) ▸
       at 9 2 (Toff204 ∷ K3⁻ ∷ []) (wp1220 c4) ▸
       at 8 2 (Toff204 ∷ CS03 ∷ []) (wp0562 c4) ▸
       at 7 2 (Toff204 ∷ CX31 ∷ []) (lem-comm-CX31-TOFF204 (lit c4)) ▸ done

  b11 : Chain (CCZ123 ∷ Toff204 ∷ CCZ123 ∷ K3 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ Toff204 ∷ CX31 ∷ CS03 ∷ K3⁻ ∷ CCZ014 ∷ CCZ234 ∷ Toff301 ∷ CCZ014 ∷ CCZ234 ∷ []) (Bx2-3104 ∷ Toff301 ∷ CS04 ∷ CX10 ∷ CS04⁻ ∷ CX10 ∷ CCZ234 ∷ CS14 ∷ Toff301 ∷ CCZ014 ∷ CCZ234 ∷ [])
  b11 = at 6 2 (Toff204 ∷ CS01⁻ ∷ []) (wp1221 c4) ▸
       at 5 2 (Toff204 ∷ CX31 ∷ []) (lem-comm-CX31-TOFF204 (lit c4)) ▸
       at 4 2 (Toff204 ∷ CS01 ∷ []) (wp0948 c4) ▸
       at 3 2 (Toff204 ∷ K3 ∷ []) (wp1222 c4) ▸
       at 4 7 (Toff301 ∷ []) (wl1380 (lit c4)) ▸
       at 0 4 (Bx2-3104 ∷ []) (sym (lem-box-cP-at02132130 c4)) ▸
       at 2 1 (CS04 ∷ CX10 ∷ CS04⁻ ∷ CX10 ∷ CS14 ∷ []) (wp0341 c4) ▸
       at 6 2 (CCZ234 ∷ CS14 ∷ []) (sym (wl0452 (lit c4))) ▸ done

  b12 : Chain (Bx2-3104 ∷ Toff301 ∷ CS04 ∷ CX10 ∷ CS04⁻ ∷ CX10 ∷ CCZ234 ∷ CS14 ∷ Toff301 ∷ CCZ014 ∷ CCZ234 ∷ []) (Bx2-3104 ∷ Bx3-1042 ∷ [])
  b12 = at 5 2 (CCZ234 ∷ CX10 ∷ []) (c₂ (CX₁₀) (CCZ)) ▸
       at 4 2 (CCZ234 ∷ CS04⁻ ∷ []) (sym (wp0342 c4)) ▸
       at 3 2 (CCZ234 ∷ CX10 ∷ []) (c₂ (CX₁₀) (CCZ)) ▸
       at 2 2 (CCZ234 ∷ CS04 ∷ []) (sym (wp0302 c4)) ▸
       at 3 5 (CCZ014 ∷ []) (sym (wp0341 c4)) ▸
       at 3 2 (Toff301 ∷ CCZ014 ∷ []) (wp1173 c4) ▸
       at 4 2 [] (wp0161 c4) ▸
       at 1 4 (Bx3-1042 ∷ []) (sym (lem-box-tQ-at03203442 c4)) ▸ done

  b13 : Chain (Bx2-3104 ∷ Bx3-1042 ∷ []) (Bx2-3104 ∷ Bx3-2104 ∷ [])
  b13 = at 1 1 (Bx3-2104 ∷ []) (lem-box-perm-4123-at03203442 c4) ▸ done


-- sym-ab @02132130: 18 steps
lem-sym-ab-at02132130 : Ws → ⟪ (Bx2-3104 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1304 ∷ []) ⟫ʷ
lem-sym-ab-at02132130 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx2-3104 ∷ []) (CCZ123 ∷ Toff213 ∷ CCZ012 ∷ Toff102 ∷ Bx2-14 ∷ Toff102 ∷ CCZ012 ∷ Bx2-14 ∷ Toff213 ∷ CCZ123 ∷ Bx3-204 ∷ [])
  b0 = at 0 1 (CCZ123 ∷ Toff213 ∷ Bx3-204 ∷ Toff213 ∷ CCZ123 ∷ Bx3-204 ∷ []) (refl) ▸
       at 2 1 (CCZ023 ∷ Toff302 ∷ Bx2-34 ∷ Toff302 ∷ CCZ023 ∷ Bx2-34 ∷ []) (refl) ▸
       at 4 1 (CZ34 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 2 6 (CCZ024 ∷ []) (wp0131 c4) ▸
       at 2 1 (CCZ012 ∷ Toff102 ∷ CZ14 ∷ Toff102 ∷ CCZ012 ∷ CZ14 ∷ []) (sym (wp0130 c4)) ▸
       at 4 1 (Bx2-14 ∷ []) (refl) ▸
       at 7 1 (Bx2-14 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ123 ∷ Toff213 ∷ CCZ012 ∷ Toff102 ∷ Bx2-14 ∷ Toff102 ∷ CCZ012 ∷ Bx2-14 ∷ Toff213 ∷ CCZ123 ∷ Bx3-204 ∷ []) (CCZ123 ∷ Toff213 ∷ Bx1-204 ∷ Toff213 ∷ CCZ123 ∷ CCZ012 ∷ Toff102 ∷ Bx2-14 ∷ Toff102 ∷ CCZ012 ∷ Bx2-14 ∷ [])
  b1 = at 2 6 (Bx1-204 ∷ []) (refl) ▸
       at 5 1 (CCZ023 ∷ Toff302 ∷ Bx2-34 ∷ Toff302 ∷ CCZ023 ∷ Bx2-34 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 10 1 (CZ34 ∷ []) (refl) ▸
       at 5 6 (CCZ024 ∷ []) (wp0131 c4) ▸
       at 5 1 (CCZ012 ∷ Toff102 ∷ CZ14 ∷ Toff102 ∷ CCZ012 ∷ CZ14 ∷ []) (sym (wp0130 c4)) ▸
       at 7 1 (Bx2-14 ∷ []) (refl) ▸
       at 10 1 (Bx2-14 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ123 ∷ Toff213 ∷ Bx1-204 ∷ Toff213 ∷ CCZ123 ∷ CCZ012 ∷ Toff102 ∷ Bx2-14 ∷ Toff102 ∷ CCZ012 ∷ Bx2-14 ∷ []) (Bx2-1304 ∷ [])
  b2 = at 5 6 (Bx1-204 ∷ []) (refl) ▸
       at 0 6 (Bx2-1304 ∷ []) (refl) ▸ done


-- box-perm-2314 @02132130: 2 steps
lem-box-perm-2314-at02132130 : Ws → ⟪ (Bx2-3104 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1034 ∷ []) ⟫ʷ
lem-box-perm-2314-at02132130 c4 = run b0
  where
  b0 : Chain (Bx2-3104 ∷ []) (Bx2-1034 ∷ [])
  b0 = at 0 1 (Bx2-1304 ∷ []) (lem-sym-ab-at02132130 c4) ▸
       at 0 1 (Bx2-1034 ∷ []) (lem-sym-bc-at022330 c4) ▸ done


-- box-perm-2314 @03122130: 2 steps
lem-box-perm-2314-at03122130 : Ws → ⟪ (Bx3-2104 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1024 ∷ []) ⟫ʷ
lem-box-perm-2314-at03122130 c4 = run b0
  where
  b0 : Chain (Bx3-2104 ∷ []) (Bx3-1024 ∷ [])
  b0 = at 0 1 (Bx3-1204 ∷ []) (lem-sym-ab-at03122130 c4) ▸
       at 0 1 (Bx3-1024 ∷ []) (lem-sym-bc-at0330 c4) ▸ done


-- Tu-box @0220: 83 steps
lem-Tu-box-at0220 : Ws → ⟪ (Toff312 ∷ Bx2-1034 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1034 ∷ Bx3-1024 ∷ []) ⟫ʷ
lem-Tu-box-at0220 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (run b10))))))))))
  where
  b0 : Chain (Toff312 ∷ Bx2-1034 ∷ Toff312 ∷ []) (Toff201 ∷ Toff301 ∷ CCZ234 ∷ Toff201 ∷ CS14 ∷ CX24 ∷ CS14⁻ ∷ CX24 ∷ CS12 ∷ Toff301 ∷ CCZ014 ∷ CCZ234 ∷ CCZ124 ∷ [])
  b0 = at 1 1 (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-box-tQ-at0220 c4) ▸
       at 0 2 (Toff201 ∷ Toff301 ∷ Toff312 ∷ []) (sym (wl1381 (lit c4))) ▸
       at 2 2 (CCZ234 ∷ CCZ124 ∷ Toff312 ∷ []) (sym (wl1382 (lit c4))) ▸
       at 4 2 (Toff201 ∷ Toff301 ∷ Toff312 ∷ []) (sym (wl1381 (lit c4))) ▸
       at 6 3 (CCZ234 ∷ CCZ124 ∷ []) (sym (wl1383 (lit c4))) ▸
       at 3 2 (Toff201 ∷ CCZ124 ∷ CCZ014 ∷ []) (wp1223 c4) ▸
       at 5 2 (Toff301 ∷ CCZ014 ∷ []) (wp1173 c4) ▸
       at 4 1 (CS14 ∷ CX24 ∷ CS14⁻ ∷ CX24 ∷ CS12 ∷ []) (wl0644 (lit c4)) ▸ done

  b1 : Chain (Toff201 ∷ Toff301 ∷ CCZ234 ∷ Toff201 ∷ CS14 ∷ CX24 ∷ CS14⁻ ∷ CX24 ∷ CS12 ∷ Toff301 ∷ CCZ014 ∷ CCZ234 ∷ CCZ124 ∷ []) (Toff201 ∷ Toff301 ∷ CCZ234 ∷ Toff201 ∷ Toff301 ∷ CCZ014 ∷ CCZ234 ∷ [])
  b1 = at 8 2 (Toff301 ∷ CS12 ∷ []) (wl1384 (lit c4)) ▸
       at 7 2 (Toff301 ∷ CX24 ∷ []) (lem-comm-CX24-TOFF301 (lit c4)) ▸
       at 6 2 (Toff301 ∷ CS14⁻ ∷ []) (wp1224 c4) ▸
       at 5 2 (Toff301 ∷ CX24 ∷ []) (lem-comm-CX24-TOFF301 (lit c4)) ▸
       at 4 2 (Toff301 ∷ CS14 ∷ []) (wp0379 c4) ▸
       at 5 5 (CCZ124 ∷ []) (sym (wl0644 (lit c4))) ▸
       at 5 2 (CCZ014 ∷ CCZ124 ∷ []) (sym (wp0066 c4)) ▸
       at 6 3 (CCZ234 ∷ []) (wl1385 (lit c4)) ▸ done

  b2 : Chain (Toff201 ∷ Toff301 ∷ CCZ234 ∷ Toff201 ∷ Toff301 ∷ CCZ014 ∷ CCZ234 ∷ []) (Toff201 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ Toff201 ∷ CCZ234 ∷ CCZ014 ∷ [])
  b2 = at 5 1 (CS04 ∷ CX10 ∷ CS04⁻ ∷ CX10 ∷ CS14 ∷ []) (wp0341 c4) ▸
       at 9 2 (CCZ234 ∷ CS14 ∷ []) (sym (wl0452 (lit c4))) ▸
       at 8 2 (CCZ234 ∷ CX10 ∷ []) (c₂ (CX₁₀) (CCZ)) ▸
       at 7 2 (CCZ234 ∷ CS04⁻ ∷ []) (sym (wp0342 c4)) ▸
       at 6 2 (CCZ234 ∷ CX10 ∷ []) (c₂ (CX₁₀) (CCZ)) ▸
       at 5 2 (CCZ234 ∷ CS04 ∷ []) (sym (wp0302 c4)) ▸
       at 6 5 (CCZ014 ∷ []) (sym (wp0341 c4)) ▸
       at 3 2 (Toff301 ∷ Toff201 ∷ []) (wl1386 (lit c4)) ▸ done

  b3 : Chain (Toff201 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ Toff201 ∷ CCZ234 ∷ CCZ014 ∷ []) (CCZ123 ∷ K2 ∷ CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ Toff304 ∷ K2⁻ ∷ CCZ013 ∷ CCZ014 ∷ CCZ123 ∷ Toff304 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ CCZ014 ∷ [])
  b3 = at 4 0 (CCZ234 ∷ CCZ234 ∷ []) (sym (wl0305 (lit c4))) ▸
       at 1 4 (Bx3-1024 ∷ []) (sym (lem-box-tQ-at032032 c4)) ▸
       at 1 1 (Bx3-1204 ∷ []) (lem-box-perm-1324-at032032 c4) ▸
       at 1 1 (CCZ123 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ []) (lem-box-cP-at0330 c4) ▸
       at 0 2 (CCZ123 ∷ Toff201 ∷ CCZ013 ∷ []) (sym (wl0696 (lit c4))) ▸
       at 2 2 (Toff304 ∷ CCZ013 ∷ CCZ014 ∷ []) (wp1159 c4) ▸
       at 1 1 (K2 ∷ CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ K2⁻ ∷ []) (sym (wl1387 (lit c4))) ▸
       at 7 2 (Toff304 ∷ K2⁻ ∷ []) (wp1038 c4) ▸ done

  b4 : Chain (CCZ123 ∷ K2 ∷ CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ Toff304 ∷ K2⁻ ∷ CCZ013 ∷ CCZ014 ∷ CCZ123 ∷ Toff304 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ CCZ014 ∷ []) (CCZ123 ∷ Toff304 ∷ Toff201 ∷ CCZ013 ∷ CS04 ∷ CX10 ∷ CS04⁻ ∷ CX10 ∷ CS14 ∷ CCZ123 ∷ Toff304 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ CCZ014 ∷ [])
  b4 = at 6 2 (Toff304 ∷ CS02 ∷ []) (wp1065 c4) ▸
       at 5 2 (Toff304 ∷ CX21 ∷ []) (lem-comm-CX21-TOFF304 (lit c4)) ▸
       at 4 2 (Toff304 ∷ CS01⁻ ∷ []) (wp1225 c4) ▸
       at 3 2 (Toff304 ∷ CX21 ∷ []) (lem-comm-CX21-TOFF304 (lit c4)) ▸
       at 2 2 (Toff304 ∷ CS01 ∷ []) (wp1058 c4) ▸
       at 1 2 (Toff304 ∷ K2 ∷ []) (wp1035 c4) ▸
       at 2 7 (Toff201 ∷ []) (wl1387 (lit c4)) ▸
       at 4 1 (CS04 ∷ CX10 ∷ CS04⁻ ∷ CX10 ∷ CS14 ∷ []) (wp0341 c4) ▸ done

  b5 : Chain (CCZ123 ∷ Toff304 ∷ Toff201 ∷ CCZ013 ∷ CS04 ∷ CX10 ∷ CS04⁻ ∷ CX10 ∷ CS14 ∷ CCZ123 ∷ Toff304 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ CCZ014 ∷ []) (CCZ123 ∷ Toff304 ∷ CCZ123 ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ CCZ014 ∷ Toff304 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ CCZ014 ∷ [])
  b5 = at 8 2 (CCZ123 ∷ CS14 ∷ []) (sym (wl0765 (lit c4))) ▸
       at 7 2 (CCZ123 ∷ CX10 ∷ []) (sym (wl0616 (lit c4))) ▸
       at 6 2 (CCZ123 ∷ CS04⁻ ∷ []) (lem-comm-CSd04-CCZ123 (lit c4)) ▸
       at 5 2 (CCZ123 ∷ CX10 ∷ []) (sym (wl0616 (lit c4))) ▸
       at 4 2 (CCZ123 ∷ CS04 ∷ []) (lem-comm-CS04-CCZ123 (lit c4)) ▸
       at 5 5 (CCZ014 ∷ []) (sym (wp0341 c4)) ▸
       at 3 2 (CCZ123 ∷ CCZ013 ∷ []) (wl0327 (lit c4)) ▸
       at 2 2 (CCZ123 ∷ Toff201 ∷ CCZ013 ∷ []) (sym (wl0696 (lit c4))) ▸ done

  b6 : Chain (CCZ123 ∷ Toff304 ∷ CCZ123 ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ CCZ014 ∷ Toff304 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ CCZ014 ∷ []) (CCZ123 ∷ Toff304 ∷ CCZ123 ∷ K2 ∷ CS01 ∷ Toff304 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ K2⁻ ∷ CCZ014 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ CCZ014 ∷ [])
  b6 = at 3 3 (Toff201 ∷ []) (wl1366 (lit c4)) ▸
       at 4 2 (Toff304 ∷ CCZ014 ∷ []) (wp0687 c4) ▸
       at 3 1 (K2 ∷ CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ K2⁻ ∷ []) (sym (wl1387 (lit c4))) ▸
       at 9 2 (Toff304 ∷ K2⁻ ∷ []) (wp1038 c4) ▸
       at 8 2 (Toff304 ∷ CS02 ∷ []) (wp1065 c4) ▸
       at 7 2 (Toff304 ∷ CX21 ∷ []) (lem-comm-CX21-TOFF304 (lit c4)) ▸
       at 6 2 (Toff304 ∷ CS01⁻ ∷ []) (wp1225 c4) ▸
       at 5 2 (Toff304 ∷ CX21 ∷ []) (lem-comm-CX21-TOFF304 (lit c4)) ▸ done

  b7 : Chain (CCZ123 ∷ Toff304 ∷ CCZ123 ∷ K2 ∷ CS01 ∷ Toff304 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ K2⁻ ∷ CCZ014 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ CCZ014 ∷ []) (Bx3-1024 ∷ Toff201 ∷ CS04 ∷ CX10 ∷ CS04⁻ ∷ CCZ234 ∷ CX10 ∷ CS14 ∷ Toff201 ∷ CCZ234 ∷ CCZ014 ∷ [])
  b7 = at 4 2 (Toff304 ∷ CS01 ∷ []) (wp1058 c4) ▸
       at 3 2 (Toff304 ∷ K2 ∷ []) (wp1035 c4) ▸
       at 4 7 (Toff201 ∷ []) (wl1387 (lit c4)) ▸
       at 0 4 (Bx3-1204 ∷ []) (sym (lem-box-cP-at0330 c4)) ▸
       at 0 1 (Bx3-1024 ∷ []) (sym (lem-box-perm-1324-at032032 c4)) ▸
       at 2 1 (CS04 ∷ CX10 ∷ CS04⁻ ∷ CX10 ∷ CS14 ∷ []) (wp0341 c4) ▸
       at 6 2 (CCZ234 ∷ CS14 ∷ []) (sym (wl0452 (lit c4))) ▸
       at 5 2 (CCZ234 ∷ CX10 ∷ []) (c₂ (CX₁₀) (CCZ)) ▸ done

  b8 : Chain (Bx3-1024 ∷ Toff201 ∷ CS04 ∷ CX10 ∷ CS04⁻ ∷ CCZ234 ∷ CX10 ∷ CS14 ∷ Toff201 ∷ CCZ234 ∷ CCZ014 ∷ []) (Bx3-1024 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ CS04 ∷ CX10 ∷ CS04⁻ ∷ CCZ234 ∷ CX10 ∷ CS14 ∷ CCZ014 ∷ [])
  b8 = at 4 2 (CCZ234 ∷ CS04⁻ ∷ []) (sym (wp0342 c4)) ▸
       at 3 2 (CCZ234 ∷ CX10 ∷ []) (c₂ (CX₁₀) (CCZ)) ▸
       at 2 2 (CCZ234 ∷ CS04 ∷ []) (sym (wp0302 c4)) ▸
       at 3 5 (CCZ014 ∷ []) (sym (wp0341 c4)) ▸
       at 3 2 (Toff201 ∷ CCZ014 ∷ []) (wp1189 c4) ▸
       at 4 1 (CS04 ∷ CX10 ∷ CS04⁻ ∷ CX10 ∷ CS14 ∷ []) (wp0341 c4) ▸
       at 8 2 (CCZ234 ∷ CS14 ∷ []) (sym (wl0452 (lit c4))) ▸
       at 7 2 (CCZ234 ∷ CX10 ∷ []) (c₂ (CX₁₀) (CCZ)) ▸ done

  b9 : Chain (Bx3-1024 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ CS04 ∷ CX10 ∷ CS04⁻ ∷ CCZ234 ∷ CX10 ∷ CS14 ∷ CCZ014 ∷ []) (Bx3-2104 ∷ Bx2-3104 ∷ [])
  b9 = at 6 2 (CCZ234 ∷ CS04⁻ ∷ []) (sym (wp0342 c4)) ▸
       at 5 2 (CCZ234 ∷ CX10 ∷ []) (c₂ (CX₁₀) (CCZ)) ▸
       at 4 2 (CCZ234 ∷ CS04 ∷ []) (sym (wp0302 c4)) ▸
       at 5 5 (CCZ014 ∷ []) (sym (wp0341 c4)) ▸
       at 5 2 [] (wp0161 c4) ▸
       at 1 4 (Bx2-1034 ∷ []) (sym (lem-box-tQ-at0220 c4)) ▸
       at 0 1 (Bx3-2104 ∷ []) (lem-box-perm-3124-at032032 c4) ▸
       at 1 1 (Bx2-3104 ∷ []) (lem-box-perm-3124-at0220 c4) ▸ done

  b10 : Chain (Bx3-2104 ∷ Bx2-3104 ∷ []) (Bx2-1034 ∷ Bx3-1024 ∷ [])
  b10 = at 0 2 (Bx2-3104 ∷ Bx3-2104 ∷ []) (lem-box-box-1-at03122130 c4) ▸
       at 0 1 (Bx2-1034 ∷ []) (lem-box-perm-2314-at02132130 c4) ▸
       at 1 1 (Bx3-1024 ∷ []) (lem-box-perm-2314-at03122130 c4) ▸ done


-- box-perm-2134 @0220: 1 steps
lem-box-perm-2134-at0220 : Ws → ⟪ (Bx2-1034 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ []) ⟫ʷ
lem-box-perm-2134-at0220 c4 = run b0
  where
  b0 : Chain (Bx2-1034 ∷ []) (Bx2-0134 ∷ [])
  b0 = at 0 1 (Bx2-0134 ∷ []) (lem-sym-ab-at0220 c4) ▸ done


-- sym-ab @031031: 18 steps
lem-sym-ab-at031031 : Ws → ⟪ (Bx3-0214 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2014 ∷ []) ⟫ʷ
lem-sym-ab-at031031 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx3-0214 ∷ []) (CCZ023 ∷ Toff302 ∷ CCZ123 ∷ Toff213 ∷ Bx3-24 ∷ Toff213 ∷ CCZ123 ∷ Bx3-24 ∷ Toff302 ∷ CCZ023 ∷ Bx0-314 ∷ [])
  b0 = at 0 1 (CCZ023 ∷ Toff302 ∷ Bx0-314 ∷ Toff302 ∷ CCZ023 ∷ Bx0-314 ∷ []) (refl) ▸
       at 2 1 (CCZ013 ∷ Toff013 ∷ Bx3-04 ∷ Toff013 ∷ CCZ013 ∷ Bx3-04 ∷ []) (refl) ▸
       at 4 1 (CZ04 ∷ []) (refl) ▸
       at 7 1 (CZ04 ∷ []) (refl) ▸
       at 2 6 (CCZ134 ∷ []) (wp0262 c4) ▸
       at 2 1 (CCZ123 ∷ Toff213 ∷ CZ24 ∷ Toff213 ∷ CCZ123 ∷ CZ24 ∷ []) (sym (wl1303 (lit c4))) ▸
       at 4 1 (Bx3-24 ∷ []) (refl) ▸
       at 7 1 (Bx3-24 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ023 ∷ Toff302 ∷ CCZ123 ∷ Toff213 ∷ Bx3-24 ∷ Toff213 ∷ CCZ123 ∷ Bx3-24 ∷ Toff302 ∷ CCZ023 ∷ Bx0-314 ∷ []) (CCZ023 ∷ Toff302 ∷ Bx2-314 ∷ Toff302 ∷ CCZ023 ∷ CCZ123 ∷ Toff213 ∷ Bx3-24 ∷ Toff213 ∷ CCZ123 ∷ Bx3-24 ∷ [])
  b1 = at 2 6 (Bx2-314 ∷ []) (refl) ▸
       at 5 1 (CCZ013 ∷ Toff013 ∷ Bx3-04 ∷ Toff013 ∷ CCZ013 ∷ Bx3-04 ∷ []) (refl) ▸
       at 7 1 (CZ04 ∷ []) (refl) ▸
       at 10 1 (CZ04 ∷ []) (refl) ▸
       at 5 6 (CCZ134 ∷ []) (wp0262 c4) ▸
       at 5 1 (CCZ123 ∷ Toff213 ∷ CZ24 ∷ Toff213 ∷ CCZ123 ∷ CZ24 ∷ []) (sym (wl1303 (lit c4))) ▸
       at 7 1 (Bx3-24 ∷ []) (refl) ▸
       at 10 1 (Bx3-24 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ023 ∷ Toff302 ∷ Bx2-314 ∷ Toff302 ∷ CCZ023 ∷ CCZ123 ∷ Toff213 ∷ Bx3-24 ∷ Toff213 ∷ CCZ123 ∷ Bx3-24 ∷ []) (Bx3-2014 ∷ [])
  b2 = at 5 6 (Bx2-314 ∷ []) (refl) ▸
       at 0 6 (Bx3-2014 ∷ []) (refl) ▸ done


-- box-perm-3214 @032032: 3 steps
lem-box-perm-3214-at032032 : Ws → ⟪ (Bx3-1024 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2014 ∷ []) ⟫ʷ
lem-box-perm-3214-at032032 c4 = run b0
  where
  b0 : Chain (Bx3-1024 ∷ []) (Bx3-2014 ∷ [])
  b0 = at 0 1 (Bx3-0124 ∷ []) (lem-sym-ab-at032032 c4) ▸
       at 0 1 (Bx3-0214 ∷ []) (lem-sym-bc-at03102132 c4) ▸
       at 0 1 (Bx3-2014 ∷ []) (lem-sym-ab-at031031 c4) ▸ done


-- box-perm-3214 @03122031: 3 steps
lem-box-perm-3214-at03122031 : Ws → ⟪ (Bx3-2014 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1024 ∷ []) ⟫ʷ
lem-box-perm-3214-at03122031 c4 = run b0
  where
  b0 : Chain (Bx3-2014 ∷ []) (Bx3-1024 ∷ [])
  b0 = at 0 1 (Bx3-0214 ∷ []) (lem-sym-ab-at03122031 c4) ▸
       at 0 1 (Bx3-0124 ∷ []) (lem-sym-bc-at031031 c4) ▸
       at 0 1 (Bx3-1024 ∷ []) (lem-sym-ab-at03102132 c4) ▸ done


-- CXbc-box @021021: 17 steps
lem-CXbc-box-at021021 : Ws → ⟪ (CX13 ∷ Bx2-0134 ∷ CX13 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ CCZ014 ∷ []) ⟫ʷ
lem-CXbc-box-at021021 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX13 ∷ Bx2-0134 ∷ CX13 ∷ []) (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CX13 ∷ CCZ124 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CCZ234 ∷ CX01 ∷ CS04 ∷ CX13 ∷ [])
  b0 = at 1 1 (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-box-tQ-at021021 c4) ▸
       at 0 2 (Toff201 ∷ CX13 ∷ []) (wl0958 (lit c4)) ▸
       at 1 2 (CCZ234 ∷ CX13 ∷ CCZ124 ∷ []) (sym (wl1388 (lit c4))) ▸
       at 3 2 (Toff201 ∷ CCZ124 ∷ CCZ014 ∷ []) (wp1223 c4) ▸
       at 2 2 (Toff201 ∷ CX13 ∷ []) (wl0958 (lit c4)) ▸
       at 5 1 (CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ []) (wp0301 c4) ▸
       at 9 2 (CCZ234 ∷ CS04 ∷ []) (sym (wp0302 c4)) ▸
       at 8 2 (CCZ234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (CCZ)) ▸ done

  b1 : Chain (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CX13 ∷ CCZ124 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CCZ234 ∷ CX01 ∷ CS04 ∷ CX13 ∷ []) (Bx2-0134 ∷ CX13 ∷ CCZ014 ∷ CX13 ∷ [])
  b1 = at 7 2 (CCZ234 ∷ CS14⁻ ∷ []) (sym (wl0451 (lit c4))) ▸
       at 6 2 (CCZ234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (CCZ)) ▸
       at 5 2 (CCZ234 ∷ CS14 ∷ []) (sym (wl0452 (lit c4))) ▸
       at 6 5 (CCZ014 ∷ []) (sym (wp0301 c4)) ▸
       at 4 2 (CCZ234 ∷ CCZ124 ∷ []) (wl0527 (lit c4)) ▸
       at 3 2 (CCZ234 ∷ CX13 ∷ CCZ124 ∷ []) (sym (wl1388 (lit c4))) ▸
       at 4 3 (CX13 ∷ []) (wl1389 (lit c4)) ▸
       at 0 4 (Bx2-0134 ∷ []) (sym (lem-box-tQ-at021021 c4)) ▸ done

  b2 : Chain (Bx2-0134 ∷ CX13 ∷ CCZ014 ∷ CX13 ∷ []) (Bx2-0134 ∷ CCZ014 ∷ [])
  b2 = at 1 3 (CCZ014 ∷ []) (sym (wp1226 c4)) ▸ done


-- CXcb-box @021021: 18 steps
lem-CXcb-box-at021021 : Ws → ⟪ (CX31 ∷ Bx2-0134 ∷ CX31 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ CCZ034 ∷ []) ⟫ʷ
lem-CXcb-box-at021021 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX31 ∷ Bx2-0134 ∷ CX31 ∷ []) (Toff201 ∷ CCZ234 ∷ CX31 ∷ Toff203 ∷ CS34 ∷ CX03 ∷ Toff201 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ CCZ234 ∷ CX31 ∷ [])
  b0 = at 1 1 (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-box-tQ-at021021 c4) ▸
       at 0 2 (Toff201 ∷ CX31 ∷ Toff203 ∷ []) (wl1390 (lit c4)) ▸
       at 2 2 (CCZ234 ∷ Toff203 ∷ CCZ034 ∷ []) (sym (wp1227 c4)) ▸
       at 1 2 (CCZ234 ∷ CX31 ∷ []) (sym (wl0336 (lit c4))) ▸
       at 4 1 (CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ []) (wp0231 c4) ▸
       at 8 2 (Toff201 ∷ CS04 ∷ []) (wp1187 c4) ▸
       at 7 2 (Toff201 ∷ CX03 ∷ []) (wl0955 (lit c4)) ▸
       at 6 2 (Toff201 ∷ CS34⁻ ∷ []) (sym (c₃ (Toffᵗ) (CS • CS • CS))) ▸ done

  b1 : Chain (Toff201 ∷ CCZ234 ∷ CX31 ∷ Toff203 ∷ CS34 ∷ CX03 ∷ Toff201 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ CCZ234 ∷ CX31 ∷ []) (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ CX31 ∷ CCZ034 ∷ CX31 ∷ [])
  b1 = at 5 2 (Toff201 ∷ CX03 ∷ []) (wl0955 (lit c4)) ▸
       at 4 2 (Toff201 ∷ CS34 ∷ []) (sym (c₃ (Toffᵗ) (CS))) ▸
       at 5 5 (CCZ034 ∷ []) (sym (wp0231 c4)) ▸
       at 3 2 (Toff201 ∷ Toff203 ∷ []) (sym (wl1391 (lit c4))) ▸
       at 2 2 (Toff201 ∷ CX31 ∷ Toff203 ∷ []) (wl1390 (lit c4)) ▸
       at 3 3 (CX31 ∷ []) (wl1392 (lit c4)) ▸
       at 4 2 (CCZ234 ∷ CCZ034 ∷ []) (wp0129 c4) ▸
       at 3 2 (CCZ234 ∷ CX31 ∷ []) (sym (wl0336 (lit c4))) ▸ done

  b2 : Chain (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ CX31 ∷ CCZ034 ∷ CX31 ∷ []) (Bx2-0134 ∷ CCZ034 ∷ [])
  b2 = at 0 4 (Bx2-0134 ∷ []) (sym (lem-box-tQ-at021021 c4)) ▸
       at 1 3 (CCZ034 ∷ []) (sym (wp1228 c4)) ▸ done


-- SWbc-box @021021: 11 steps
lem-SWbc-box-at021021 : Ws → ⟪ (Sw13 ∷ Bx2-0134 ∷ Sw13 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ []) ⟫ʷ
lem-SWbc-box-at021021 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw13 ∷ Bx2-0134 ∷ Sw13 ∷ []) (CX13 ∷ Bx2-0134 ∷ CX13 ∷ CCZ014 ∷ CCZ034 ∷ CCZ014 ∷ CCZ034 ∷ CCZ014 ∷ [])
  b0 = at 0 1 (CX13 ∷ CX31 ∷ CX13 ∷ []) (sym (wl0278 (lit c4))) ▸
       at 4 1 (CX13 ∷ CX31 ∷ CX13 ∷ []) (sym (wl0278 (lit c4))) ▸
       at 2 3 (Bx2-0134 ∷ CCZ014 ∷ []) (lem-CXbc-box-at021021 c4) ▸
       at 3 2 (CX31 ∷ CCZ034 ∷ CCZ014 ∷ []) (wp1229 c4) ▸
       at 1 3 (Bx2-0134 ∷ CCZ034 ∷ []) (lem-CXcb-box-at021021 c4) ▸
       at 4 2 (CX13 ∷ CCZ014 ∷ []) (wp0795 c4) ▸
       at 3 2 (CX13 ∷ CCZ014 ∷ CCZ034 ∷ []) (wp1230 c4) ▸
       at 2 2 (CX13 ∷ CCZ014 ∷ CCZ034 ∷ []) (wp1230 c4) ▸ done

  b1 : Chain (CX13 ∷ Bx2-0134 ∷ CX13 ∷ CCZ014 ∷ CCZ034 ∷ CCZ014 ∷ CCZ034 ∷ CCZ014 ∷ []) (Bx2-0134 ∷ [])
  b1 = at 3 5 (CCZ014 ∷ []) (wp1231 c4) ▸
       at 0 3 (Bx2-0134 ∷ CCZ014 ∷ []) (lem-CXbc-box-at021021 c4) ▸
       at 1 2 [] (wp0161 c4) ▸ done


-- nat-SWbc @021021: 23 steps
lem-nat-SWbc-at021021 : Ws → ⟪ (Sw13 ∷ Bx2-0134 ∷ Sw13 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0314 ∷ []) ⟫ʷ
lem-nat-SWbc-at021021 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw13 ∷ Bx2-0134 ∷ Sw13 ∷ []) (CCZ023 ∷ Toff203 ∷ CCZ012 ∷ Toff012 ∷ Bx2-04 ∷ Toff012 ∷ Sw13 ∷ CCZ023 ∷ Bx2-04 ∷ Toff201 ∷ CCZ012 ∷ Bx0-234 ∷ Sw13 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff201 ∷ Bx0-234 ∷ Toff201 ∷ CCZ012 ∷ Bx0-234 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw13 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 1 2 (Toff203 ∷ Sw13 ∷ []) (wl0990 (lit c4)) ▸
       at 3 1 (CCZ023 ∷ Toff023 ∷ Bx2-04 ∷ Toff023 ∷ CCZ023 ∷ Bx2-04 ∷ []) (refl) ▸
       at 2 2 (CCZ012 ∷ Sw13 ∷ []) (sym (wl0285 (lit c4))) ▸
       at 3 2 (Toff012 ∷ Sw13 ∷ []) (wl0989 (lit c4)) ▸
       at 4 2 (Bx2-04 ∷ Sw13 ∷ []) (lem-comm-SWAP13-BOX⟨2·04⟩ (lit c4)) ▸
       at 5 2 (Toff012 ∷ Sw13 ∷ []) (wl0989 (lit c4)) ▸ done

  b1 : Chain (CCZ023 ∷ Toff203 ∷ CCZ012 ∷ Toff012 ∷ Bx2-04 ∷ Toff012 ∷ Sw13 ∷ CCZ023 ∷ Bx2-04 ∷ Toff201 ∷ CCZ012 ∷ Bx0-234 ∷ Sw13 ∷ []) (CCZ023 ∷ Toff203 ∷ CCZ012 ∷ Toff012 ∷ Bx2-04 ∷ Toff012 ∷ CCZ012 ∷ Bx2-04 ∷ Toff203 ∷ CCZ023 ∷ CCZ012 ∷ Toff012 ∷ Bx2-04 ∷ Sw13 ∷ Toff023 ∷ CCZ023 ∷ Bx2-04 ∷ Sw13 ∷ [])
  b1 = at 6 2 (CCZ012 ∷ Sw13 ∷ []) (sym (wl0285 (lit c4))) ▸
       at 7 2 (Bx2-04 ∷ Sw13 ∷ []) (lem-comm-SWAP13-BOX⟨2·04⟩ (lit c4)) ▸
       at 8 2 (Toff203 ∷ Sw13 ∷ []) (wl0990 (lit c4)) ▸
       at 9 2 (CCZ023 ∷ Sw13 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 1 (CCZ023 ∷ Toff023 ∷ Bx2-04 ∷ Toff023 ∷ CCZ023 ∷ Bx2-04 ∷ []) (refl) ▸
       at 10 2 (CCZ012 ∷ Sw13 ∷ []) (sym (wl0285 (lit c4))) ▸
       at 11 2 (Toff012 ∷ Sw13 ∷ []) (wl0989 (lit c4)) ▸
       at 12 2 (Bx2-04 ∷ Sw13 ∷ []) (lem-comm-SWAP13-BOX⟨2·04⟩ (lit c4)) ▸ done

  b2 : Chain (CCZ023 ∷ Toff203 ∷ CCZ012 ∷ Toff012 ∷ Bx2-04 ∷ Toff012 ∷ CCZ012 ∷ Bx2-04 ∷ Toff203 ∷ CCZ023 ∷ CCZ012 ∷ Toff012 ∷ Bx2-04 ∷ Sw13 ∷ Toff023 ∷ CCZ023 ∷ Bx2-04 ∷ Sw13 ∷ []) (Bx2-0314 ∷ [])
  b2 = at 13 2 (Toff012 ∷ Sw13 ∷ []) (wl0989 (lit c4)) ▸
       at 14 2 (CCZ012 ∷ Sw13 ∷ []) (sym (wl0285 (lit c4))) ▸
       at 15 2 (Bx2-04 ∷ Sw13 ∷ []) (lem-comm-SWAP13-BOX⟨2·04⟩ (lit c4)) ▸
       at 16 2 [] (wl0287 (lit c4)) ▸
       at 2 6 (Bx0-214 ∷ []) (refl) ▸
       at 5 6 (Bx0-214 ∷ []) (refl) ▸
       at 0 6 (Bx2-0314 ∷ []) (refl) ▸ done


-- sym-bc @021021: 2 steps
lem-sym-bc-at021021 : Ws → ⟪ (Bx2-0134 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0314 ∷ []) ⟫ʷ
lem-sym-bc-at021021 c4 = run b0
  where
  b0 : Chain (Bx2-0134 ∷ []) (Bx2-0314 ∷ [])
  b0 = at 0 1 (Sw13 ∷ Bx2-0134 ∷ Sw13 ∷ []) (sym (lem-SWbc-box-at021021 c4)) ▸
       at 0 3 (Bx2-0314 ∷ []) (lem-nat-SWbc-at021021 c4) ▸ done


-- box-perm-1324 @021021: 1 steps
lem-box-perm-1324-at021021 : Ws → ⟪ (Bx2-0134 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0314 ∷ []) ⟫ʷ
lem-box-perm-1324-at021021 c4 = run b0
  where
  b0 : Chain (Bx2-0134 ∷ []) (Bx2-0314 ∷ [])
  b0 = at 0 1 (Bx2-0314 ∷ []) (lem-sym-bc-at021021 c4) ▸ done


-- cQ @02102331: 7 steps
lem-cQ-at02102331 : Ws → ⟪ (CCZ023 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ CCZ023 ∷ []) ⟫ʷ
lem-cQ-at02102331 c4 = run b0
  where
  b0 : Chain (CCZ023 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ023 ∷ [])
  b0 = at 0 1 (CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ []) (wl0637 (lit c4)) ▸
       at 4 2 (CCZ124 ∷ CS02 ∷ []) (sym (wp0515 c4)) ▸
       at 3 2 (CCZ124 ∷ CX03 ∷ []) (lem-comm-CX03-CCZ124 (lit c4)) ▸
       at 2 2 (CCZ124 ∷ CS23⁻ ∷ []) (sym (wl0638 (lit c4))) ▸
       at 1 2 (CCZ124 ∷ CX03 ∷ []) (lem-comm-CX03-CCZ124 (lit c4)) ▸
       at 0 2 (CCZ124 ∷ CS23 ∷ []) (sym (wl0639 (lit c4))) ▸
       at 1 5 (CCZ023 ∷ []) (sym (wl0637 (lit c4))) ▸ done


-- tP @02102331: 7 steps
lem-tP-at02102331 : Ws → ⟪ (Toff203 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ Toff203 ∷ []) ⟫ʷ
lem-tP-at02102331 c4 = run b0
  where
  b0 : Chain (Toff203 ∷ Toff214 ∷ []) (Toff214 ∷ Toff203 ∷ [])
  b0 = at 0 1 (K2 ∷ CCZ023 ∷ K2⁻ ∷ []) (sym (wl0625 (lit c4))) ▸
       at 3 1 (K2 ∷ CCZ124 ∷ K2⁻ ∷ []) (sym (wl0624 (lit c4))) ▸
       at 2 2 [] (wl0175 (lit c4)) ▸
       at 1 2 (CCZ124 ∷ CCZ023 ∷ []) (lem-cQ-at02102331 c4) ▸
       at 2 0 (K2⁻ ∷ K2 ∷ []) (sym (wl0175 (lit c4))) ▸
       at 0 3 (Toff214 ∷ []) (wl0624 (lit c4)) ▸
       at 1 3 (Toff203 ∷ []) (wl0625 (lit c4)) ▸ done


-- VPQ @02102331: 14 steps
lem-VPQ-at02102331 : Ws → ⟪ (Toff203 ∷ CCZ023 ∷ Toff214 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CCZ124 ∷ Toff203 ∷ CCZ023 ∷ []) ⟫ʷ
lem-VPQ-at02102331 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff203 ∷ CCZ023 ∷ Toff214 ∷ CCZ124 ∷ []) (CS14⁻ ∷ CS03⁻ ∷ S2 ∷ Toff214 ∷ Toff203 ∷ S2⁻ ∷ [])
  b0 = at 0 2 (CS03⁻ ∷ S2 ∷ Toff203 ∷ S2⁻ ∷ []) (sym (wl0630 (lit c4))) ▸
       at 4 2 (CS14⁻ ∷ S2 ∷ Toff214 ∷ S2⁻ ∷ []) (sym (wl0629 (lit c4))) ▸
       at 3 2 (CS14⁻ ∷ S2⁻ ∷ []) (sym (wl0634 (lit c4))) ▸
       at 2 2 (CS14⁻ ∷ Toff203 ∷ []) (lem-comm-TOFF203-CSd14 (lit c4)) ▸
       at 1 2 (CS14⁻ ∷ S2 ∷ []) (sym (wl0633 (lit c4))) ▸
       at 0 2 (CS14⁻ ∷ CS03⁻ ∷ []) (wp0514 c4) ▸
       at 4 2 [] (wl0179 (lit c4)) ▸
       at 3 2 (Toff214 ∷ Toff203 ∷ []) (lem-tP-at02102331 c4) ▸ done

  b1 : Chain (CS14⁻ ∷ CS03⁻ ∷ S2 ∷ Toff214 ∷ Toff203 ∷ S2⁻ ∷ []) (Toff214 ∷ CCZ124 ∷ Toff203 ∷ CCZ023 ∷ [])
  b1 = at 4 0 (S2⁻ ∷ S2 ∷ []) (sym (wl0179 (lit c4))) ▸
       at 1 2 (S2 ∷ CS03⁻ ∷ []) (wl0632 (lit c4)) ▸
       at 2 2 (Toff214 ∷ CS03⁻ ∷ []) (lem-comm-CSd03-TOFF214 (lit c4)) ▸
       at 3 2 (S2⁻ ∷ CS03⁻ ∷ []) (wl0631 (lit c4)) ▸
       at 0 4 (Toff214 ∷ CCZ124 ∷ []) (wl0629 (lit c4)) ▸
       at 2 4 (Toff203 ∷ CCZ023 ∷ []) (wl0630 (lit c4)) ▸ done


-- QVQ @02102331: 3 steps
lem-QVQ-at02102331 : Ws → ⟪ (CCZ124 ∷ Toff203 ∷ CCZ023 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ Toff203 ∷ CCZ023 ∷ Toff214 ∷ []) ⟫ʷ
lem-QVQ-at02102331 c4 = run b0
  where
  b0 : Chain (CCZ124 ∷ Toff203 ∷ CCZ023 ∷ CCZ124 ∷ []) (Toff214 ∷ Toff203 ∷ CCZ023 ∷ Toff214 ∷ [])
  b0 = at 0 0 (Toff214 ∷ Toff214 ∷ []) (sym (wl0636 (lit c4))) ▸
       at 1 4 (Toff203 ∷ CCZ023 ∷ Toff214 ∷ CCZ124 ∷ []) (sym (lem-VPQ-at02102331 c4)) ▸
       at 4 2 [] (wl0263 (lit c4)) ▸ done


-- box-cP @02102331: 12 steps
lem-box-cP-at02102331 : Ws → ⟪ (Bx2-0314 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ []) ⟫ʷ
lem-box-cP-at02102331 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx2-0314 ∷ []) (CCZ023 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ023 ∷ CCZ012 ∷ Toff012 ∷ CZ04 ∷ Toff012 ∷ CCZ012 ∷ CZ04 ∷ [])
  b0 = at 0 1 (CCZ023 ∷ Toff203 ∷ Bx0-214 ∷ Toff203 ∷ CCZ023 ∷ Bx0-214 ∷ []) (refl) ▸
       at 2 1 (CCZ012 ∷ Toff012 ∷ Bx2-04 ∷ Toff012 ∷ CCZ012 ∷ Bx2-04 ∷ []) (refl) ▸
       at 4 1 (CZ04 ∷ []) (refl) ▸
       at 7 1 (CZ04 ∷ []) (refl) ▸
       at 2 6 (CCZ124 ∷ []) (wp1232 c4) ▸
       at 5 1 (CCZ012 ∷ Toff012 ∷ Bx2-04 ∷ Toff012 ∷ CCZ012 ∷ Bx2-04 ∷ []) (refl) ▸
       at 7 1 (CZ04 ∷ []) (refl) ▸
       at 10 1 (CZ04 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ023 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ023 ∷ CCZ012 ∷ Toff012 ∷ CZ04 ∷ Toff012 ∷ CCZ012 ∷ CZ04 ∷ []) (CCZ023 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ [])
  b1 = at 5 6 (CCZ124 ∷ []) (wp1232 c4) ▸
       at 2 4 (Toff214 ∷ Toff203 ∷ CCZ023 ∷ Toff214 ∷ []) (lem-QVQ-at02102331 c4) ▸
       at 1 2 (Toff214 ∷ Toff203 ∷ []) (lem-tP-at02102331 c4) ▸
       at 2 2 [] (wl0635 (lit c4)) ▸ done


-- P-box @031031: 8 steps
lem-P-box-at031031 : Ws → ⟪ (Toff314 ∷ Bx3-0214 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0214 ∷ []) ⟫ʷ
lem-P-box-at031031 c4 = run b0
  where
  b0 : Chain (Toff314 ∷ Bx3-0214 ∷ Toff314 ∷ []) (Bx3-0214 ∷ [])
  b0 = at 1 1 (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ []) (lem-box-tQ-at031031 c4) ▸
       at 0 2 (Toff302 ∷ Toff314 ∷ []) (sym (lem-tP-at031031 c4)) ▸
       at 1 2 (CCZ134 ∷ CZ14 ∷ Toff314 ∷ []) (sym (wl1253 (lit c4))) ▸
       at 3 2 (Toff302 ∷ Toff314 ∷ []) (sym (lem-tP-at031031 c4)) ▸
       at 4 3 (CCZ134 ∷ CZ14 ∷ []) (sym (wl1254 (lit c4))) ▸
       at 2 2 (Toff302 ∷ CZ14 ∷ []) (lem-comm-CZ14-TOFF302 (lit c4)) ▸
       at 3 3 (CCZ134 ∷ []) (sym (wl1255 (lit c4))) ▸
       at 0 4 (Bx3-0214 ∷ []) (sym (lem-box-tQ-at031031 c4)) ▸ done


-- cQ @03243042: 7 steps
lem-cQ-at03243042 : Ws → ⟪ (CCZ134 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ CCZ134 ∷ []) ⟫ʷ
lem-cQ-at03243042 c4 = run b0
  where
  b0 : Chain (CCZ134 ∷ CCZ023 ∷ []) (CCZ023 ∷ CCZ134 ∷ [])
  b0 = at 0 1 (CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ []) (wl0698 (lit c4)) ▸
       at 4 2 (CCZ023 ∷ CS13 ∷ []) (sym (wl0670 (lit c4))) ▸
       at 3 2 (CCZ023 ∷ CX14 ∷ []) (lem-comm-CX14-CCZ023 (lit c4)) ▸
       at 2 2 (CCZ023 ∷ CS34⁻ ∷ []) (sym (wp0574 c4)) ▸
       at 1 2 (CCZ023 ∷ CX14 ∷ []) (lem-comm-CX14-CCZ023 (lit c4)) ▸
       at 0 2 (CCZ023 ∷ CS34 ∷ []) (sym (wp0543 c4)) ▸
       at 1 5 (CCZ134 ∷ []) (sym (wl0698 (lit c4))) ▸ done


-- box-tQ @03243042: 13 steps
lem-box-tQ-at03243042 : Ws → ⟪ (Bx3-1402 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ []) ⟫ʷ
lem-box-tQ-at03243042 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-1402 ∷ []) (CCZ134 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ CCZ013 ∷ Toff103 ∷ CZ12 ∷ Toff103 ∷ CCZ013 ∷ CZ12 ∷ [])
  b0 = at 0 1 (CCZ134 ∷ Toff314 ∷ Bx1-302 ∷ Toff314 ∷ CCZ134 ∷ Bx1-302 ∷ []) (refl) ▸
       at 2 1 (CCZ013 ∷ Toff103 ∷ Bx3-12 ∷ Toff103 ∷ CCZ013 ∷ Bx3-12 ∷ []) (refl) ▸
       at 4 1 (CZ12 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 2 6 (CCZ023 ∷ []) (wl0344 (lit c4)) ▸
       at 5 1 (CCZ013 ∷ Toff103 ∷ Bx3-12 ∷ Toff103 ∷ CCZ013 ∷ Bx3-12 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 10 1 (CZ12 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ134 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ CCZ013 ∷ Toff103 ∷ CZ12 ∷ Toff103 ∷ CCZ013 ∷ CZ12 ∷ []) (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ [])
  b1 = at 5 6 (CCZ023 ∷ []) (wl0344 (lit c4)) ▸
       at 0 2 (Toff314 ∷ CCZ134 ∷ CZ14 ∷ []) (wl0749 (lit c4)) ▸
       at 2 2 (CCZ023 ∷ CZ14 ∷ []) (lem-comm-CZ14-CCZ023 (lit c4)) ▸
       at 1 2 (CCZ023 ∷ CCZ134 ∷ []) (lem-cQ-at03243042 c4) ▸
       at 2 4 (Toff314 ∷ []) (wl0750 (lit c4)) ▸ done


-- pairs @031031: 4 steps
lem-pairs-at031031 : Ws → ⟪ (Bx3-0214 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1402 ∷ []) ⟫ʷ
lem-pairs-at031031 c4 = run b0
  where
  b0 : Chain (Bx3-0214 ∷ []) (Bx3-1402 ∷ [])
  b0 = at 0 1 (Toff314 ∷ Bx3-0214 ∷ Toff314 ∷ []) (sym (lem-P-box-at031031 c4)) ▸
       at 1 1 (CCZ023 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ []) (lem-box-cP-at031031 c4) ▸
       at 4 2 [] (wl0788 (lit c4)) ▸
       at 0 4 (Bx3-1402 ∷ []) (sym (lem-box-tQ-at03243042 c4)) ▸ done


-- sym-ab @03243042: 18 steps
lem-sym-ab-at03243042 : Ws → ⟪ (Bx3-1402 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4102 ∷ []) ⟫ʷ
lem-sym-ab-at03243042 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx3-1402 ∷ []) (CCZ134 ∷ Toff314 ∷ CCZ034 ∷ Toff403 ∷ Bx3-42 ∷ Toff403 ∷ CCZ034 ∷ Bx3-42 ∷ Toff314 ∷ CCZ134 ∷ Bx1-302 ∷ [])
  b0 = at 0 1 (CCZ134 ∷ Toff314 ∷ Bx1-302 ∷ Toff314 ∷ CCZ134 ∷ Bx1-302 ∷ []) (refl) ▸
       at 2 1 (CCZ013 ∷ Toff103 ∷ Bx3-12 ∷ Toff103 ∷ CCZ013 ∷ Bx3-12 ∷ []) (refl) ▸
       at 4 1 (CZ12 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 2 6 (CCZ023 ∷ []) (wl0344 (lit c4)) ▸
       at 2 1 (CCZ034 ∷ Toff403 ∷ CZ24 ∷ Toff403 ∷ CCZ034 ∷ CZ24 ∷ []) (wp0661 c4) ▸
       at 4 1 (Bx3-42 ∷ []) (refl) ▸
       at 7 1 (Bx3-42 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ134 ∷ Toff314 ∷ CCZ034 ∷ Toff403 ∷ Bx3-42 ∷ Toff403 ∷ CCZ034 ∷ Bx3-42 ∷ Toff314 ∷ CCZ134 ∷ Bx1-302 ∷ []) (CCZ134 ∷ Toff314 ∷ Bx4-302 ∷ Toff314 ∷ CCZ134 ∷ CCZ034 ∷ Toff403 ∷ Bx3-42 ∷ Toff403 ∷ CCZ034 ∷ Bx3-42 ∷ [])
  b1 = at 2 6 (Bx4-302 ∷ []) (refl) ▸
       at 5 1 (CCZ013 ∷ Toff103 ∷ Bx3-12 ∷ Toff103 ∷ CCZ013 ∷ Bx3-12 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 10 1 (CZ12 ∷ []) (refl) ▸
       at 5 6 (CCZ023 ∷ []) (wl0344 (lit c4)) ▸
       at 5 1 (CCZ034 ∷ Toff403 ∷ CZ24 ∷ Toff403 ∷ CCZ034 ∷ CZ24 ∷ []) (wp0661 c4) ▸
       at 7 1 (Bx3-42 ∷ []) (refl) ▸
       at 10 1 (Bx3-42 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ134 ∷ Toff314 ∷ Bx4-302 ∷ Toff314 ∷ CCZ134 ∷ CCZ034 ∷ Toff403 ∷ Bx3-42 ∷ Toff403 ∷ CCZ034 ∷ Bx3-42 ∷ []) (Bx3-4102 ∷ [])
  b2 = at 5 6 (Bx4-302 ∷ []) (refl) ▸
       at 0 6 (Bx3-4102 ∷ []) (refl) ▸ done


-- box-perm-4123 @032032: 4 steps
lem-box-perm-4123-at032032 : Ws → ⟪ (Bx3-1024 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4102 ∷ []) ⟫ʷ
lem-box-perm-4123-at032032 c4 = run b0
  where
  b0 : Chain (Bx3-1024 ∷ []) (Bx3-4102 ∷ [])
  b0 = at 0 1 (Bx3-0124 ∷ []) (lem-sym-ab-at032032 c4) ▸
       at 0 1 (Bx3-0214 ∷ []) (lem-sym-bc-at03102132 c4) ▸
       at 0 1 (Bx3-1402 ∷ []) (lem-pairs-at031031 c4) ▸
       at 0 1 (Bx3-4102 ∷ []) (lem-sym-ab-at03243042 c4) ▸ done


-- cQ @142142: 7 steps
lem-cQ-at142142 : Ws → ⟪ (CCZ014 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ CCZ014 ∷ []) ⟫ʷ
lem-cQ-at142142 c4 = run b0
  where
  b0 : Chain (CCZ014 ∷ CCZ023 ∷ []) (CCZ023 ∷ CCZ014 ∷ [])
  b0 = at 0 1 (CS01 ∷ CX41 ∷ CS01⁻ ∷ CX41 ∷ CS04 ∷ []) (wp0540 c4) ▸
       at 4 2 (CCZ023 ∷ CS04 ∷ []) (sym (wp0048 c4)) ▸
       at 3 2 (CCZ023 ∷ CX41 ∷ []) (lem-comm-CX41-CCZ023 (lit c4)) ▸
       at 2 2 (CCZ023 ∷ CS01⁻ ∷ []) (sym (wl0667 (lit c4))) ▸
       at 1 2 (CCZ023 ∷ CX41 ∷ []) (lem-comm-CX41-CCZ023 (lit c4)) ▸
       at 0 2 (CCZ023 ∷ CS01 ∷ []) (sym (wl0199 (lit c4))) ▸
       at 1 5 (CCZ014 ∷ []) (sym (wp0540 c4)) ▸ done


-- box-tQ @142142: 13 steps
lem-box-tQ-at142142 : Ws → ⟪ (Bx0-4132 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) ⟫ʷ
lem-box-tQ-at142142 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-4132 ∷ []) (CCZ014 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ CCZ034 ∷ Toff403 ∷ CZ24 ∷ Toff403 ∷ CCZ034 ∷ CZ24 ∷ [])
  b0 = at 0 1 (CCZ014 ∷ Toff014 ∷ Bx4-032 ∷ Toff014 ∷ CCZ014 ∷ Bx4-032 ∷ []) (refl) ▸
       at 2 1 (CCZ034 ∷ Toff403 ∷ Bx0-42 ∷ Toff403 ∷ CCZ034 ∷ Bx0-42 ∷ []) (refl) ▸
       at 4 1 (CZ24 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 2 6 (CCZ023 ∷ []) (sym (wp0661 c4)) ▸
       at 5 1 (CCZ034 ∷ Toff403 ∷ Bx0-42 ∷ Toff403 ∷ CCZ034 ∷ Bx0-42 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 10 1 (CZ24 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ014 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ CCZ034 ∷ Toff403 ∷ CZ24 ∷ Toff403 ∷ CCZ034 ∷ CZ24 ∷ []) (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ [])
  b1 = at 5 6 (CCZ023 ∷ []) (sym (wp0661 c4)) ▸
       at 0 2 (Toff014 ∷ CCZ014 ∷ CZ14 ∷ []) (wp0056 c4) ▸
       at 2 2 (CCZ023 ∷ CZ14 ∷ []) (lem-comm-CZ14-CCZ023 (lit c4)) ▸
       at 1 2 (CCZ023 ∷ CCZ014 ∷ []) (lem-cQ-at142142 c4) ▸
       at 2 4 (Toff014 ∷ []) (wp0057 c4) ▸ done


-- CXbc-box @142142: 17 steps
lem-CXbc-box-at142142 : Ws → ⟪ (CX13 ∷ Bx0-4132 ∷ CX13 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4132 ∷ CCZ124 ∷ []) ⟫ʷ
lem-CXbc-box-at142142 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX13 ∷ Bx0-4132 ∷ CX13 ∷ []) (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CX13 ∷ CCZ012 ∷ CS12 ∷ CX41 ∷ CS12⁻ ∷ CCZ023 ∷ CX41 ∷ CS24 ∷ CX13 ∷ [])
  b0 = at 1 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-box-tQ-at142142 c4) ▸
       at 0 2 (Toff014 ∷ CX13 ∷ []) (wp0963 c4) ▸
       at 1 2 (CCZ023 ∷ CX13 ∷ CCZ012 ∷ []) (sym (wl1393 (lit c4))) ▸
       at 3 2 (Toff014 ∷ CCZ012 ∷ CCZ124 ∷ []) (wp1233 c4) ▸
       at 2 2 (Toff014 ∷ CX13 ∷ []) (wp0963 c4) ▸
       at 5 1 (CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ []) (wl0334 (lit c4)) ▸
       at 9 2 (CCZ023 ∷ CS24 ∷ []) (sym (wp0513 c4)) ▸
       at 8 2 (CCZ023 ∷ CX41 ∷ []) (lem-comm-CX41-CCZ023 (lit c4)) ▸ done

  b1 : Chain (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CX13 ∷ CCZ012 ∷ CS12 ∷ CX41 ∷ CS12⁻ ∷ CCZ023 ∷ CX41 ∷ CS24 ∷ CX13 ∷ []) (Bx0-4132 ∷ CX13 ∷ CCZ124 ∷ CX13 ∷ [])
  b1 = at 7 2 (CCZ023 ∷ CS12⁻ ∷ []) (sym (wl0620 (lit c4))) ▸
       at 6 2 (CCZ023 ∷ CX41 ∷ []) (lem-comm-CX41-CCZ023 (lit c4)) ▸
       at 5 2 (CCZ023 ∷ CS12 ∷ []) (sym (wl0621 (lit c4))) ▸
       at 6 5 (CCZ124 ∷ []) (sym (wl0334 (lit c4))) ▸
       at 4 2 (CCZ023 ∷ CCZ012 ∷ []) (wl0332 (lit c4)) ▸
       at 3 2 (CCZ023 ∷ CX13 ∷ CCZ012 ∷ []) (sym (wl1393 (lit c4))) ▸
       at 4 3 (CX13 ∷ []) (wl1394 (lit c4)) ▸
       at 0 4 (Bx0-4132 ∷ []) (sym (lem-box-tQ-at142142 c4)) ▸ done

  b2 : Chain (Bx0-4132 ∷ CX13 ∷ CCZ124 ∷ CX13 ∷ []) (Bx0-4132 ∷ CCZ124 ∷ [])
  b2 = at 1 3 (CCZ124 ∷ []) (sym (wl0272 (lit c4))) ▸ done


-- CXcb-box @142142: 18 steps
lem-CXcb-box-at142142 : Ws → ⟪ (CX31 ∷ Bx0-4132 ∷ CX31 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4132 ∷ CCZ234 ∷ []) ⟫ʷ
lem-CXcb-box-at142142 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX31 ∷ Bx0-4132 ∷ CX31 ∷ []) (Toff014 ∷ CCZ023 ∷ CX31 ∷ Toff034 ∷ CS23 ∷ CX43 ∷ Toff014 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ CCZ023 ∷ CX31 ∷ [])
  b0 = at 1 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-box-tQ-at142142 c4) ▸
       at 0 2 (Toff014 ∷ CX31 ∷ Toff034 ∷ []) (wp1234 c4) ▸
       at 2 2 (CCZ023 ∷ Toff034 ∷ CCZ234 ∷ []) (sym (wp1235 c4)) ▸
       at 1 2 (CCZ023 ∷ CX31 ∷ []) (sym (wl1343 (lit c4))) ▸
       at 4 1 (CS23 ∷ CX43 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ []) (wl0330 (lit c4)) ▸
       at 8 2 (Toff014 ∷ CS24 ∷ []) (wp0817 c4) ▸
       at 7 2 (Toff014 ∷ CX43 ∷ []) (wp0960 c4) ▸
       at 6 2 (Toff014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-TOFF014 (lit c4)) ▸ done

  b1 : Chain (Toff014 ∷ CCZ023 ∷ CX31 ∷ Toff034 ∷ CS23 ∷ CX43 ∷ Toff014 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ CCZ023 ∷ CX31 ∷ []) (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ CX31 ∷ CCZ234 ∷ CX31 ∷ [])
  b1 = at 5 2 (Toff014 ∷ CX43 ∷ []) (wp0960 c4) ▸
       at 4 2 (Toff014 ∷ CS23 ∷ []) (lem-comm-CS23-TOFF014 (lit c4)) ▸
       at 5 5 (CCZ234 ∷ []) (sym (wl0330 (lit c4))) ▸
       at 3 2 (Toff014 ∷ Toff034 ∷ []) (sym (wp0203 c4)) ▸
       at 2 2 (Toff014 ∷ CX31 ∷ Toff034 ∷ []) (wp1234 c4) ▸
       at 3 3 (CX31 ∷ []) (wp1236 c4) ▸
       at 4 2 (CCZ023 ∷ CCZ234 ∷ []) (sym (wp0550 c4)) ▸
       at 3 2 (CCZ023 ∷ CX31 ∷ []) (sym (wl1343 (lit c4))) ▸ done

  b2 : Chain (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ CX31 ∷ CCZ234 ∷ CX31 ∷ []) (Bx0-4132 ∷ CCZ234 ∷ [])
  b2 = at 0 4 (Bx0-4132 ∷ []) (sym (lem-box-tQ-at142142 c4)) ▸
       at 1 3 (CCZ234 ∷ []) (sym (wl0277 (lit c4))) ▸ done


-- SWbc-box @142142: 11 steps
lem-SWbc-box-at142142 : Ws → ⟪ (Sw13 ∷ Bx0-4132 ∷ Sw13 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4132 ∷ []) ⟫ʷ
lem-SWbc-box-at142142 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw13 ∷ Bx0-4132 ∷ Sw13 ∷ []) (CX13 ∷ Bx0-4132 ∷ CX13 ∷ CCZ124 ∷ CCZ234 ∷ CCZ124 ∷ CCZ234 ∷ CCZ124 ∷ [])
  b0 = at 0 1 (CX13 ∷ CX31 ∷ CX13 ∷ []) (sym (wl0278 (lit c4))) ▸
       at 4 1 (CX13 ∷ CX31 ∷ CX13 ∷ []) (sym (wl0278 (lit c4))) ▸
       at 2 3 (Bx0-4132 ∷ CCZ124 ∷ []) (lem-CXbc-box-at142142 c4) ▸
       at 3 2 (CX31 ∷ CCZ234 ∷ CCZ124 ∷ []) (wl0279 (lit c4)) ▸
       at 1 3 (Bx0-4132 ∷ CCZ234 ∷ []) (lem-CXcb-box-at142142 c4) ▸
       at 4 2 (CX13 ∷ CCZ124 ∷ []) (wl0280 (lit c4)) ▸
       at 3 2 (CX13 ∷ CCZ124 ∷ CCZ234 ∷ []) (wl0281 (lit c4)) ▸
       at 2 2 (CX13 ∷ CCZ124 ∷ CCZ234 ∷ []) (wl0281 (lit c4)) ▸ done

  b1 : Chain (CX13 ∷ Bx0-4132 ∷ CX13 ∷ CCZ124 ∷ CCZ234 ∷ CCZ124 ∷ CCZ234 ∷ CCZ124 ∷ []) (Bx0-4132 ∷ [])
  b1 = at 3 5 (CCZ124 ∷ []) (wl0282 (lit c4)) ▸
       at 0 3 (Bx0-4132 ∷ CCZ124 ∷ []) (lem-CXbc-box-at142142 c4) ▸
       at 1 2 [] (wl0263 (lit c4)) ▸ done


-- nat-SWbc @142142: 23 steps
lem-nat-SWbc-at142142 : Ws → ⟪ (Sw13 ∷ Bx0-4132 ∷ Sw13 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4312 ∷ []) ⟫ʷ
lem-nat-SWbc-at142142 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw13 ∷ Bx0-4132 ∷ Sw13 ∷ []) (CCZ034 ∷ Toff034 ∷ CCZ014 ∷ Toff401 ∷ Bx0-42 ∷ Toff401 ∷ Sw13 ∷ CCZ034 ∷ Bx0-42 ∷ Toff014 ∷ CCZ014 ∷ Bx4-032 ∷ Sw13 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff014 ∷ Bx4-032 ∷ Toff014 ∷ CCZ014 ∷ Bx4-032 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw13 ∷ []) (sym (wp0208 c4)) ▸
       at 1 2 (Toff034 ∷ Sw13 ∷ []) (wp1237 c4) ▸
       at 3 1 (CCZ034 ∷ Toff403 ∷ Bx0-42 ∷ Toff403 ∷ CCZ034 ∷ Bx0-42 ∷ []) (refl) ▸
       at 2 2 (CCZ014 ∷ Sw13 ∷ []) (sym (wp0206 c4)) ▸
       at 3 2 (Toff401 ∷ Sw13 ∷ []) (wp1238 c4) ▸
       at 4 2 (Bx0-42 ∷ Sw13 ∷ []) (lem-comm-SWAP13-BOX⟨0·42⟩ (lit c4)) ▸
       at 5 2 (Toff401 ∷ Sw13 ∷ []) (wp1238 c4) ▸ done

  b1 : Chain (CCZ034 ∷ Toff034 ∷ CCZ014 ∷ Toff401 ∷ Bx0-42 ∷ Toff401 ∷ Sw13 ∷ CCZ034 ∷ Bx0-42 ∷ Toff014 ∷ CCZ014 ∷ Bx4-032 ∷ Sw13 ∷ []) (CCZ034 ∷ Toff034 ∷ CCZ014 ∷ Toff401 ∷ Bx0-42 ∷ Toff401 ∷ CCZ014 ∷ Bx0-42 ∷ Toff034 ∷ CCZ034 ∷ CCZ014 ∷ Toff401 ∷ Bx0-42 ∷ Sw13 ∷ Toff403 ∷ CCZ034 ∷ Bx0-42 ∷ Sw13 ∷ [])
  b1 = at 6 2 (CCZ014 ∷ Sw13 ∷ []) (sym (wp0206 c4)) ▸
       at 7 2 (Bx0-42 ∷ Sw13 ∷ []) (lem-comm-SWAP13-BOX⟨0·42⟩ (lit c4)) ▸
       at 8 2 (Toff034 ∷ Sw13 ∷ []) (wp1237 c4) ▸
       at 9 2 (CCZ034 ∷ Sw13 ∷ []) (sym (wp0208 c4)) ▸
       at 11 1 (CCZ034 ∷ Toff403 ∷ Bx0-42 ∷ Toff403 ∷ CCZ034 ∷ Bx0-42 ∷ []) (refl) ▸
       at 10 2 (CCZ014 ∷ Sw13 ∷ []) (sym (wp0206 c4)) ▸
       at 11 2 (Toff401 ∷ Sw13 ∷ []) (wp1238 c4) ▸
       at 12 2 (Bx0-42 ∷ Sw13 ∷ []) (lem-comm-SWAP13-BOX⟨0·42⟩ (lit c4)) ▸ done

  b2 : Chain (CCZ034 ∷ Toff034 ∷ CCZ014 ∷ Toff401 ∷ Bx0-42 ∷ Toff401 ∷ CCZ014 ∷ Bx0-42 ∷ Toff034 ∷ CCZ034 ∷ CCZ014 ∷ Toff401 ∷ Bx0-42 ∷ Sw13 ∷ Toff403 ∷ CCZ034 ∷ Bx0-42 ∷ Sw13 ∷ []) (Bx0-4312 ∷ [])
  b2 = at 13 2 (Toff401 ∷ Sw13 ∷ []) (wp1238 c4) ▸
       at 14 2 (CCZ014 ∷ Sw13 ∷ []) (sym (wp0206 c4)) ▸
       at 15 2 (Bx0-42 ∷ Sw13 ∷ []) (lem-comm-SWAP13-BOX⟨0·42⟩ (lit c4)) ▸
       at 16 2 [] (wl0287 (lit c4)) ▸
       at 2 6 (Bx4-012 ∷ []) (refl) ▸
       at 5 6 (Bx4-012 ∷ []) (refl) ▸
       at 0 6 (Bx0-4312 ∷ []) (refl) ▸ done


-- sym-bc @142142: 2 steps
lem-sym-bc-at142142 : Ws → ⟪ (Bx0-4132 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4312 ∷ []) ⟫ʷ
lem-sym-bc-at142142 c4 = run b0
  where
  b0 : Chain (Bx0-4132 ∷ []) (Bx0-4312 ∷ [])
  b0 = at 0 1 (Sw13 ∷ Bx0-4132 ∷ Sw13 ∷ []) (sym (lem-SWbc-box-at142142 c4)) ▸
       at 0 3 (Bx0-4312 ∷ []) (lem-nat-SWbc-at142142 c4) ▸ done


-- box-perm-1324 @142142: 1 steps
lem-box-perm-1324-at142142 : Ws → ⟪ (Bx0-4132 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4312 ∷ []) ⟫ʷ
lem-box-perm-1324-at142142 c4 = run b0
  where
  b0 : Chain (Bx0-4132 ∷ []) (Bx0-4312 ∷ [])
  b0 = at 0 1 (Bx0-4312 ∷ []) (lem-sym-bc-at142142 c4) ▸ done


-- box-perm-3124 @142142: 2 steps
lem-box-perm-3124-at142142 : Ws → ⟪ (Bx0-4132 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3412 ∷ []) ⟫ʷ
lem-box-perm-3124-at142142 c4 = run b0
  where
  b0 : Chain (Bx0-4132 ∷ []) (Bx0-3412 ∷ [])
  b0 = at 0 1 (Bx0-4312 ∷ []) (lem-sym-bc-at142142 c4) ▸
       at 0 1 (Bx0-3412 ∷ []) (lem-sym-ab-at14233142 c4) ▸ done


-- box-perm-2341 @13243142: 4 steps
lem-box-perm-2341-at13243142 : Ws → ⟪ (Bx0-3412 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4123 ∷ []) ⟫ʷ
lem-box-perm-2341-at13243142 c4 = run b0
  where
  b0 : Chain (Bx0-3412 ∷ []) (Bx0-4123 ∷ [])
  b0 = at 0 1 (Bx0-4312 ∷ []) (lem-sym-ab-at13243142 c4) ▸
       at 0 1 (Bx0-1243 ∷ []) (lem-pairs-at14233142 c4) ▸
       at 0 1 (Bx0-1423 ∷ []) (lem-sym-bc-at3443 c4) ▸
       at 0 1 (Bx0-4123 ∷ []) (lem-sym-ab-at243243 c4) ▸ done


-- box-perm-4123 @14213243: 4 steps
lem-box-perm-4123-at14213243 : Ws → ⟪ (Bx0-4123 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3412 ∷ []) ⟫ʷ
lem-box-perm-4123-at14213243 c4 = run b0
  where
  b0 : Chain (Bx0-4123 ∷ []) (Bx0-3412 ∷ [])
  b0 = at 0 1 (Bx0-1423 ∷ []) (lem-sym-ab-at14213243 c4) ▸
       at 0 1 (Bx0-1243 ∷ []) (lem-sym-bc-at243243 c4) ▸
       at 0 1 (Bx0-4312 ∷ []) (lem-pairs-at3443 c4) ▸
       at 0 1 (Bx0-3412 ∷ []) (lem-sym-ab-at14233142 c4) ▸ done


-- box-box-1 @13243142: 105 steps
lem-box-box-1-at13243142 : Ws → ⟪ (Bx0-3412 ∷ Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ Bx0-3412 ∷ []) ⟫ʷ
lem-box-box-1-at13243142 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (run b13)))))))))))))
  where
  b0 : Chain (Bx0-3412 ∷ Bx3-0412 ∷ []) (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ034 ∷ Toff312 ∷ CCZ023 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CCZ034 ∷ CX01 ∷ CS02 ∷ Toff312 ∷ [])
  b0 = at 0 1 (Bx0-4123 ∷ []) (lem-box-perm-2341-at13243142 c4) ▸
       at 0 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-box-tQ-at14213243 c4) ▸
       at 4 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 3 2 (CCZ034 ∷ CCZ023 ∷ []) (wp0575 c4) ▸
       at 4 2 (Toff312 ∷ CCZ023 ∷ CCZ012 ∷ []) (wl1213 (lit c4)) ▸
       at 6 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wl0348 (lit c4)) ▸
       at 10 2 (CCZ034 ∷ CS02 ∷ []) (sym (wp0003 c4)) ▸
       at 9 2 (CCZ034 ∷ CX01 ∷ []) (sym (wp0221 c4)) ▸ done

  b1 : Chain (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ034 ∷ Toff312 ∷ CCZ023 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CCZ034 ∷ CX01 ∷ CS02 ∷ Toff312 ∷ []) (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ023 ∷ [])
  b1 = at 8 2 (CCZ034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-CCZ034 (lit c4)) ▸
       at 7 2 (CCZ034 ∷ CX01 ∷ []) (sym (wp0221 c4)) ▸
       at 6 2 (CCZ034 ∷ CS12 ∷ []) (lem-comm-CS12-CCZ034 (lit c4)) ▸
       at 7 5 (CCZ012 ∷ []) (sym (wl0348 (lit c4))) ▸
       at 5 2 (CCZ034 ∷ CCZ023 ∷ []) (wp0575 c4) ▸
       at 6 3 (Toff312 ∷ CCZ023 ∷ []) (wl1395 (lit c4)) ▸
       at 3 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 3 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸ done

  b2 : Chain (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ023 ∷ []) (Toff014 ∷ CCZ023 ∷ CCZ034 ∷ K0 ∷ CS14 ∷ Toff312 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ K0⁻ ∷ CCZ134 ∷ CCZ124 ∷ CCZ034 ∷ Toff312 ∷ CCZ023 ∷ [])
  b2 = at 2 2 (CCZ034 ∷ Toff014 ∷ CCZ134 ∷ []) (sym (wp1114 c4)) ▸
       at 4 2 (Toff312 ∷ CCZ134 ∷ CCZ124 ∷ []) (wl1356 (lit c4)) ▸
       at 3 1 (K0 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ K0⁻ ∷ []) (sym (wp1239 c4)) ▸
       at 9 2 (Toff312 ∷ K0⁻ ∷ []) (c₁ (K • iI) (Toffᵗ)) ▸
       at 8 2 (Toff312 ∷ CS01 ∷ []) (wl0501 (lit c4)) ▸
       at 7 2 (Toff312 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF312 (lit c4)) ▸
       at 6 2 (Toff312 ∷ CS14⁻ ∷ []) (wl0778 (lit c4)) ▸
       at 5 2 (Toff312 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF312 (lit c4)) ▸ done

  b3 : Chain (Toff014 ∷ CCZ023 ∷ CCZ034 ∷ K0 ∷ CS14 ∷ Toff312 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ K0⁻ ∷ CCZ134 ∷ CCZ124 ∷ CCZ034 ∷ Toff312 ∷ CCZ023 ∷ []) (Toff014 ∷ CCZ023 ∷ CCZ034 ∷ Toff312 ∷ Toff014 ∷ CCZ134 ∷ CS12 ∷ CCZ034 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ Toff312 ∷ CCZ023 ∷ [])
  b3 = at 4 2 (Toff312 ∷ CS14 ∷ []) (wl0499 (lit c4)) ▸
       at 3 2 (Toff312 ∷ K0 ∷ []) (c₁ (K) (Toffᵗ)) ▸
       at 4 7 (Toff014 ∷ []) (wp1239 c4) ▸
       at 6 1 (CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ []) (wl0334 (lit c4)) ▸
       at 10 2 (CCZ034 ∷ CS24 ∷ []) (sym (wp0108 c4)) ▸
       at 9 2 (CCZ034 ∷ CX41 ∷ []) (sym (wp0357 c4)) ▸
       at 8 2 (CCZ034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-CCZ034 (lit c4)) ▸
       at 7 2 (CCZ034 ∷ CX41 ∷ []) (sym (wp0357 c4)) ▸ done

  b4 : Chain (Toff014 ∷ CCZ023 ∷ CCZ034 ∷ Toff312 ∷ Toff014 ∷ CCZ134 ∷ CS12 ∷ CCZ034 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ Toff312 ∷ CCZ023 ∷ []) (Toff014 ∷ CCZ023 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ K0 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ Toff312 ∷ K0⁻ ∷ CCZ124 ∷ CCZ023 ∷ [])
  b4 = at 6 2 (CCZ034 ∷ CS12 ∷ []) (lem-comm-CS12-CCZ034 (lit c4)) ▸
       at 7 5 (CCZ124 ∷ []) (sym (wl0334 (lit c4))) ▸
       at 5 2 (CCZ034 ∷ CCZ134 ∷ []) (sym (wp0103 c4)) ▸
       at 4 2 (CCZ034 ∷ Toff014 ∷ CCZ134 ∷ []) (sym (wp1114 c4)) ▸
       at 5 3 (Toff014 ∷ []) (wp1240 c4) ▸
       at 6 2 (Toff312 ∷ CCZ124 ∷ []) (wl0871 (lit c4)) ▸
       at 5 1 (K0 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ K0⁻ ∷ []) (sym (wp1239 c4)) ▸
       at 11 2 (Toff312 ∷ K0⁻ ∷ []) (c₁ (K • iI) (Toffᵗ)) ▸ done

  b5 : Chain (Toff014 ∷ CCZ023 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ K0 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ Toff312 ∷ K0⁻ ∷ CCZ124 ∷ CCZ023 ∷ []) (Toff014 ∷ CCZ023 ∷ Bx3-0412 ∷ Toff014 ∷ CCZ124 ∷ CCZ023 ∷ [])
  b5 = at 10 2 (Toff312 ∷ CS01 ∷ []) (wl0501 (lit c4)) ▸
       at 9 2 (Toff312 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF312 (lit c4)) ▸
       at 8 2 (Toff312 ∷ CS14⁻ ∷ []) (wl0778 (lit c4)) ▸
       at 7 2 (Toff312 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF312 (lit c4)) ▸
       at 6 2 (Toff312 ∷ CS14 ∷ []) (wl0499 (lit c4)) ▸
       at 5 2 (Toff312 ∷ K0 ∷ []) (c₁ (K) (Toffᵗ)) ▸
       at 6 7 (Toff014 ∷ []) (wp1239 c4) ▸
       at 2 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸ done

  b6 : Chain (Toff014 ∷ CCZ023 ∷ Bx3-0412 ∷ Toff014 ∷ CCZ124 ∷ CCZ023 ∷ []) (Toff014 ∷ CCZ034 ∷ Toff312 ∷ CCZ023 ∷ CS12 ∷ CCZ034 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Toff312 ∷ Toff014 ∷ CCZ124 ∷ CCZ023 ∷ [])
  b6 = at 2 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 1 2 (CCZ034 ∷ CCZ023 ∷ []) (wp0575 c4) ▸
       at 2 2 (Toff312 ∷ CCZ023 ∷ CCZ012 ∷ []) (wl1213 (lit c4)) ▸
       at 4 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wl0348 (lit c4)) ▸
       at 8 2 (CCZ034 ∷ CS02 ∷ []) (sym (wp0003 c4)) ▸
       at 7 2 (CCZ034 ∷ CX01 ∷ []) (sym (wp0221 c4)) ▸
       at 6 2 (CCZ034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-CCZ034 (lit c4)) ▸
       at 5 2 (CCZ034 ∷ CX01 ∷ []) (sym (wp0221 c4)) ▸ done

  b7 : Chain (Toff014 ∷ CCZ034 ∷ Toff312 ∷ CCZ023 ∷ CS12 ∷ CCZ034 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Toff312 ∷ Toff014 ∷ CCZ124 ∷ CCZ023 ∷ []) (CCZ034 ∷ Toff014 ∷ Toff312 ∷ CCZ134 ∷ CCZ124 ∷ CCZ034 ∷ Toff312 ∷ CCZ023 ∷ Toff014 ∷ CCZ124 ∷ CCZ023 ∷ [])
  b7 = at 4 2 (CCZ034 ∷ CS12 ∷ []) (lem-comm-CS12-CCZ034 (lit c4)) ▸
       at 5 5 (CCZ012 ∷ []) (sym (wl0348 (lit c4))) ▸
       at 3 2 (CCZ034 ∷ CCZ023 ∷ []) (wp0575 c4) ▸
       at 4 3 (Toff312 ∷ CCZ023 ∷ []) (wl1395 (lit c4)) ▸
       at 1 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 1 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 0 2 (CCZ034 ∷ Toff014 ∷ CCZ134 ∷ []) (sym (wp1114 c4)) ▸
       at 2 2 (Toff312 ∷ CCZ134 ∷ CCZ124 ∷ []) (wl1356 (lit c4)) ▸ done

  b8 : Chain (CCZ034 ∷ Toff014 ∷ Toff312 ∷ CCZ134 ∷ CCZ124 ∷ CCZ034 ∷ Toff312 ∷ CCZ023 ∷ Toff014 ∷ CCZ124 ∷ CCZ023 ∷ []) (CCZ034 ∷ Toff312 ∷ K0 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ K0⁻ ∷ CCZ134 ∷ CCZ124 ∷ CCZ034 ∷ Toff312 ∷ CCZ023 ∷ Toff014 ∷ CCZ124 ∷ CCZ023 ∷ [])
  b8 = at 1 1 (K0 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ K0⁻ ∷ []) (sym (wp1239 c4)) ▸
       at 7 2 (Toff312 ∷ K0⁻ ∷ []) (c₁ (K • iI) (Toffᵗ)) ▸
       at 6 2 (Toff312 ∷ CS01 ∷ []) (wl0501 (lit c4)) ▸
       at 5 2 (Toff312 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF312 (lit c4)) ▸
       at 4 2 (Toff312 ∷ CS14⁻ ∷ []) (wl0778 (lit c4)) ▸
       at 3 2 (Toff312 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF312 (lit c4)) ▸
       at 2 2 (Toff312 ∷ CS14 ∷ []) (wl0499 (lit c4)) ▸
       at 1 2 (Toff312 ∷ K0 ∷ []) (c₁ (K) (Toffᵗ)) ▸ done

  b9 : Chain (CCZ034 ∷ Toff312 ∷ K0 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ K0⁻ ∷ CCZ134 ∷ CCZ124 ∷ CCZ034 ∷ Toff312 ∷ CCZ023 ∷ Toff014 ∷ CCZ124 ∷ CCZ023 ∷ []) (CCZ034 ∷ Toff312 ∷ Toff014 ∷ CCZ134 ∷ CCZ034 ∷ CCZ124 ∷ Toff312 ∷ CCZ023 ∷ Toff014 ∷ CCZ124 ∷ CCZ023 ∷ [])
  b9 = at 2 7 (Toff014 ∷ []) (wp1239 c4) ▸
       at 4 1 (CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ []) (wl0334 (lit c4)) ▸
       at 8 2 (CCZ034 ∷ CS24 ∷ []) (sym (wp0108 c4)) ▸
       at 7 2 (CCZ034 ∷ CX41 ∷ []) (sym (wp0357 c4)) ▸
       at 6 2 (CCZ034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-CCZ034 (lit c4)) ▸
       at 5 2 (CCZ034 ∷ CX41 ∷ []) (sym (wp0357 c4)) ▸
       at 4 2 (CCZ034 ∷ CS12 ∷ []) (lem-comm-CS12-CCZ034 (lit c4)) ▸
       at 5 5 (CCZ124 ∷ []) (sym (wl0334 (lit c4))) ▸ done

  b10 : Chain (CCZ034 ∷ Toff312 ∷ Toff014 ∷ CCZ134 ∷ CCZ034 ∷ CCZ124 ∷ Toff312 ∷ CCZ023 ∷ Toff014 ∷ CCZ124 ∷ CCZ023 ∷ []) (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ K0 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ Toff312 ∷ CX04 ∷ CS01 ∷ K0⁻ ∷ CCZ124 ∷ CCZ023 ∷ Toff014 ∷ CCZ124 ∷ CCZ023 ∷ [])
  b10 = at 3 2 (CCZ034 ∷ CCZ134 ∷ []) (sym (wp0103 c4)) ▸
       at 2 2 (CCZ034 ∷ Toff014 ∷ CCZ134 ∷ []) (sym (wp1114 c4)) ▸
       at 3 3 (Toff014 ∷ []) (wp1240 c4) ▸
       at 4 2 (Toff312 ∷ CCZ124 ∷ []) (wl0871 (lit c4)) ▸
       at 3 1 (K0 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ K0⁻ ∷ []) (sym (wp1239 c4)) ▸
       at 9 2 (Toff312 ∷ K0⁻ ∷ []) (c₁ (K • iI) (Toffᵗ)) ▸
       at 8 2 (Toff312 ∷ CS01 ∷ []) (wl0501 (lit c4)) ▸
       at 7 2 (Toff312 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF312 (lit c4)) ▸ done

  b11 : Chain (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ K0 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ Toff312 ∷ CX04 ∷ CS01 ∷ K0⁻ ∷ CCZ124 ∷ CCZ023 ∷ Toff014 ∷ CCZ124 ∷ CCZ023 ∷ []) (Bx3-0412 ∷ Toff014 ∷ CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CCZ023 ∷ CS24 ∷ Toff014 ∷ CCZ124 ∷ CCZ023 ∷ [])
  b11 = at 6 2 (Toff312 ∷ CS14⁻ ∷ []) (wl0778 (lit c4)) ▸
       at 5 2 (Toff312 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF312 (lit c4)) ▸
       at 4 2 (Toff312 ∷ CS14 ∷ []) (wl0499 (lit c4)) ▸
       at 3 2 (Toff312 ∷ K0 ∷ []) (c₁ (K) (Toffᵗ)) ▸
       at 4 7 (Toff014 ∷ []) (wp1239 c4) ▸
       at 0 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 2 1 (CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ []) (wl0334 (lit c4)) ▸
       at 6 2 (CCZ023 ∷ CS24 ∷ []) (sym (wp0513 c4)) ▸ done

  b12 : Chain (Bx3-0412 ∷ Toff014 ∷ CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CCZ023 ∷ CS24 ∷ Toff014 ∷ CCZ124 ∷ CCZ023 ∷ []) (Bx3-0412 ∷ Bx0-4123 ∷ [])
  b12 = at 5 2 (CCZ023 ∷ CX41 ∷ []) (lem-comm-CX41-CCZ023 (lit c4)) ▸
       at 4 2 (CCZ023 ∷ CS12⁻ ∷ []) (sym (wl0620 (lit c4))) ▸
       at 3 2 (CCZ023 ∷ CX41 ∷ []) (lem-comm-CX41-CCZ023 (lit c4)) ▸
       at 2 2 (CCZ023 ∷ CS12 ∷ []) (sym (wl0621 (lit c4))) ▸
       at 3 5 (CCZ124 ∷ []) (sym (wl0334 (lit c4))) ▸
       at 3 2 (Toff014 ∷ CCZ124 ∷ []) (wp0822 c4) ▸
       at 4 2 [] (wl0263 (lit c4)) ▸
       at 1 4 (Bx0-4123 ∷ []) (sym (lem-box-tQ-at14213243 c4)) ▸ done

  b13 : Chain (Bx3-0412 ∷ Bx0-4123 ∷ []) (Bx3-0412 ∷ Bx0-3412 ∷ [])
  b13 = at 1 1 (Bx0-3412 ∷ []) (lem-box-perm-4123-at14213243 c4) ▸ done


-- box-perm-2314 @13243142: 2 steps
lem-box-perm-2314-at13243142 : Ws → ⟪ (Bx0-3412 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4132 ∷ []) ⟫ʷ
lem-box-perm-2314-at13243142 c4 = run b0
  where
  b0 : Chain (Bx0-3412 ∷ []) (Bx0-4132 ∷ [])
  b0 = at 0 1 (Bx0-4312 ∷ []) (lem-sym-ab-at13243142 c4) ▸
       at 0 1 (Bx0-4132 ∷ []) (lem-sym-bc-at14233142 c4) ▸ done


-- Tu-box @0314213042: 83 steps
lem-Tu-box-at0314213042 : Ws → ⟪ (Toff034 ∷ Bx3-4102 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4102 ∷ Bx0-4132 ∷ []) ⟫ʷ
lem-Tu-box-at0314213042 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (run b10))))))))))
  where
  b0 : Chain (Toff034 ∷ Bx3-4102 ∷ Toff034 ∷ []) (Toff314 ∷ Toff014 ∷ CCZ023 ∷ Toff314 ∷ CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ Toff014 ∷ CCZ124 ∷ CCZ023 ∷ CCZ234 ∷ [])
  b0 = at 1 1 (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ []) (lem-box-tQ-at0314213042 c4) ▸
       at 0 2 (Toff314 ∷ Toff014 ∷ Toff034 ∷ []) (wp1241 c4) ▸
       at 2 2 (CCZ023 ∷ CCZ234 ∷ Toff034 ∷ []) (sym (wp1242 c4)) ▸
       at 4 2 (Toff314 ∷ Toff014 ∷ Toff034 ∷ []) (wp1241 c4) ▸
       at 6 3 (CCZ023 ∷ CCZ234 ∷ []) (sym (wp1243 c4)) ▸
       at 3 2 (Toff314 ∷ CCZ234 ∷ CCZ124 ∷ []) (wl1396 (lit c4)) ▸
       at 5 2 (Toff014 ∷ CCZ124 ∷ []) (wp0822 c4) ▸
       at 4 1 (CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ []) (wl0829 (lit c4)) ▸ done

  b1 : Chain (Toff314 ∷ Toff014 ∷ CCZ023 ∷ Toff314 ∷ CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ Toff014 ∷ CCZ124 ∷ CCZ023 ∷ CCZ234 ∷ []) (Toff314 ∷ Toff014 ∷ CCZ023 ∷ Toff314 ∷ Toff014 ∷ CCZ124 ∷ CCZ023 ∷ [])
  b1 = at 8 2 (Toff014 ∷ CS34 ∷ []) (wp0546 c4) ▸
       at 7 2 (Toff014 ∷ CX32 ∷ []) (lem-comm-CX32-TOFF014 (lit c4)) ▸
       at 6 2 (Toff014 ∷ CS24⁻ ∷ []) (wp1244 c4) ▸
       at 5 2 (Toff014 ∷ CX32 ∷ []) (lem-comm-CX32-TOFF014 (lit c4)) ▸
       at 4 2 (Toff014 ∷ CS24 ∷ []) (wp0817 c4) ▸
       at 5 5 (CCZ234 ∷ []) (sym (wl0829 (lit c4))) ▸
       at 5 2 (CCZ124 ∷ CCZ234 ∷ []) (sym (wl0527 (lit c4))) ▸
       at 6 3 (CCZ023 ∷ []) (sym (wp1245 c4)) ▸ done

  b2 : Chain (Toff314 ∷ Toff014 ∷ CCZ023 ∷ Toff314 ∷ Toff014 ∷ CCZ124 ∷ CCZ023 ∷ []) (Toff314 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ Toff314 ∷ CCZ023 ∷ CCZ124 ∷ [])
  b2 = at 5 1 (CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ []) (wl0334 (lit c4)) ▸
       at 9 2 (CCZ023 ∷ CS24 ∷ []) (sym (wp0513 c4)) ▸
       at 8 2 (CCZ023 ∷ CX41 ∷ []) (lem-comm-CX41-CCZ023 (lit c4)) ▸
       at 7 2 (CCZ023 ∷ CS12⁻ ∷ []) (sym (wl0620 (lit c4))) ▸
       at 6 2 (CCZ023 ∷ CX41 ∷ []) (lem-comm-CX41-CCZ023 (lit c4)) ▸
       at 5 2 (CCZ023 ∷ CS12 ∷ []) (sym (wl0621 (lit c4))) ▸
       at 6 5 (CCZ124 ∷ []) (sym (wl0334 (lit c4))) ▸
       at 3 2 (Toff014 ∷ Toff314 ∷ []) (sym (wp1246 c4)) ▸ done

  b3 : Chain (Toff314 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ Toff314 ∷ CCZ023 ∷ CCZ124 ∷ []) (CCZ034 ∷ K3 ∷ CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ Toff012 ∷ K3⁻ ∷ CCZ014 ∷ CCZ124 ∷ CCZ034 ∷ Toff012 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ CCZ124 ∷ [])
  b3 = at 4 0 (CCZ023 ∷ CCZ023 ∷ []) (sym (wl0204 (lit c4))) ▸
       at 1 4 (Bx0-4132 ∷ []) (sym (lem-box-tQ-at142142 c4)) ▸
       at 1 1 (Bx0-4312 ∷ []) (lem-box-perm-1324-at142142 c4) ▸
       at 1 1 (CCZ034 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ []) (lem-box-cP-at14233142 c4) ▸
       at 0 2 (CCZ034 ∷ Toff314 ∷ CCZ014 ∷ []) (sym (wp0702 c4)) ▸
       at 2 2 (Toff012 ∷ CCZ014 ∷ CCZ124 ∷ []) (wp0122 c4) ▸
       at 1 1 (K3 ∷ CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ K3⁻ ∷ []) (sym (wl1397 (lit c4))) ▸
       at 7 2 (Toff012 ∷ K3⁻ ∷ []) (sym (c₃ (Toff) (K • iI))) ▸ done

  b4 : Chain (CCZ034 ∷ K3 ∷ CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ Toff012 ∷ K3⁻ ∷ CCZ014 ∷ CCZ124 ∷ CCZ034 ∷ Toff012 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ CCZ124 ∷ []) (CCZ034 ∷ Toff012 ∷ Toff314 ∷ CCZ014 ∷ CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ CCZ034 ∷ Toff012 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ CCZ124 ∷ [])
  b4 = at 6 2 (Toff012 ∷ CS13 ∷ []) (wl1284 (lit c4)) ▸
       at 5 2 (Toff012 ∷ CX34 ∷ []) (sym (c₃ (Toff) (CX₀₁))) ▸
       at 4 2 (Toff012 ∷ CS14⁻ ∷ []) (wp1247 c4) ▸
       at 3 2 (Toff012 ∷ CX34 ∷ []) (sym (c₃ (Toff) (CX₀₁))) ▸
       at 2 2 (Toff012 ∷ CS14 ∷ []) (wp0102 c4) ▸
       at 1 2 (Toff012 ∷ K3 ∷ []) (sym (c₃ (Toff) (K))) ▸
       at 2 7 (Toff314 ∷ []) (wl1397 (lit c4)) ▸
       at 4 1 (CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ []) (wl0334 (lit c4)) ▸ done

  b5 : Chain (CCZ034 ∷ Toff012 ∷ Toff314 ∷ CCZ014 ∷ CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ CCZ034 ∷ Toff012 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ CCZ124 ∷ []) (CCZ034 ∷ Toff012 ∷ CCZ034 ∷ Toff314 ∷ CCZ014 ∷ CCZ014 ∷ CCZ124 ∷ Toff012 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ CCZ124 ∷ [])
  b5 = at 8 2 (CCZ034 ∷ CS24 ∷ []) (sym (wp0108 c4)) ▸
       at 7 2 (CCZ034 ∷ CX41 ∷ []) (sym (wp0357 c4)) ▸
       at 6 2 (CCZ034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-CCZ034 (lit c4)) ▸
       at 5 2 (CCZ034 ∷ CX41 ∷ []) (sym (wp0357 c4)) ▸
       at 4 2 (CCZ034 ∷ CS12 ∷ []) (lem-comm-CS12-CCZ034 (lit c4)) ▸
       at 5 5 (CCZ124 ∷ []) (sym (wl0334 (lit c4))) ▸
       at 3 2 (CCZ034 ∷ CCZ014 ∷ []) (wp0124 c4) ▸
       at 2 2 (CCZ034 ∷ Toff314 ∷ CCZ014 ∷ []) (sym (wp0702 c4)) ▸ done

  b6 : Chain (CCZ034 ∷ Toff012 ∷ CCZ034 ∷ Toff314 ∷ CCZ014 ∷ CCZ014 ∷ CCZ124 ∷ Toff012 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ CCZ124 ∷ []) (CCZ034 ∷ Toff012 ∷ CCZ034 ∷ K3 ∷ CS14 ∷ Toff012 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ K3⁻ ∷ CCZ124 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ CCZ124 ∷ [])
  b6 = at 3 3 (Toff314 ∷ []) (wp1248 c4) ▸
       at 4 2 (Toff012 ∷ CCZ124 ∷ []) (wp0300 c4) ▸
       at 3 1 (K3 ∷ CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ K3⁻ ∷ []) (sym (wl1397 (lit c4))) ▸
       at 9 2 (Toff012 ∷ K3⁻ ∷ []) (sym (c₃ (Toff) (K • iI))) ▸
       at 8 2 (Toff012 ∷ CS13 ∷ []) (wl1284 (lit c4)) ▸
       at 7 2 (Toff012 ∷ CX34 ∷ []) (sym (c₃ (Toff) (CX₀₁))) ▸
       at 6 2 (Toff012 ∷ CS14⁻ ∷ []) (wp1247 c4) ▸
       at 5 2 (Toff012 ∷ CX34 ∷ []) (sym (c₃ (Toff) (CX₀₁))) ▸ done

  b7 : Chain (CCZ034 ∷ Toff012 ∷ CCZ034 ∷ K3 ∷ CS14 ∷ Toff012 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ K3⁻ ∷ CCZ124 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ CCZ124 ∷ []) (Bx0-4132 ∷ Toff314 ∷ CS12 ∷ CX41 ∷ CS12⁻ ∷ CCZ023 ∷ CX41 ∷ CS24 ∷ Toff314 ∷ CCZ023 ∷ CCZ124 ∷ [])
  b7 = at 4 2 (Toff012 ∷ CS14 ∷ []) (wp0102 c4) ▸
       at 3 2 (Toff012 ∷ K3 ∷ []) (sym (c₃ (Toff) (K))) ▸
       at 4 7 (Toff314 ∷ []) (wl1397 (lit c4)) ▸
       at 0 4 (Bx0-4312 ∷ []) (sym (lem-box-cP-at14233142 c4)) ▸
       at 0 1 (Bx0-4132 ∷ []) (sym (lem-box-perm-1324-at142142 c4)) ▸
       at 2 1 (CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ []) (wl0334 (lit c4)) ▸
       at 6 2 (CCZ023 ∷ CS24 ∷ []) (sym (wp0513 c4)) ▸
       at 5 2 (CCZ023 ∷ CX41 ∷ []) (lem-comm-CX41-CCZ023 (lit c4)) ▸ done

  b8 : Chain (Bx0-4132 ∷ Toff314 ∷ CS12 ∷ CX41 ∷ CS12⁻ ∷ CCZ023 ∷ CX41 ∷ CS24 ∷ Toff314 ∷ CCZ023 ∷ CCZ124 ∷ []) (Bx0-4132 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ CS12 ∷ CX41 ∷ CS12⁻ ∷ CCZ023 ∷ CX41 ∷ CS24 ∷ CCZ124 ∷ [])
  b8 = at 4 2 (CCZ023 ∷ CS12⁻ ∷ []) (sym (wl0620 (lit c4))) ▸
       at 3 2 (CCZ023 ∷ CX41 ∷ []) (lem-comm-CX41-CCZ023 (lit c4)) ▸
       at 2 2 (CCZ023 ∷ CS12 ∷ []) (sym (wl0621 (lit c4))) ▸
       at 3 5 (CCZ124 ∷ []) (sym (wl0334 (lit c4))) ▸
       at 3 2 (Toff314 ∷ CCZ124 ∷ []) (wl0974 (lit c4)) ▸
       at 4 1 (CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ []) (wl0334 (lit c4)) ▸
       at 8 2 (CCZ023 ∷ CS24 ∷ []) (sym (wp0513 c4)) ▸
       at 7 2 (CCZ023 ∷ CX41 ∷ []) (lem-comm-CX41-CCZ023 (lit c4)) ▸ done

  b9 : Chain (Bx0-4132 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ CS12 ∷ CX41 ∷ CS12⁻ ∷ CCZ023 ∷ CX41 ∷ CS24 ∷ CCZ124 ∷ []) (Bx0-3412 ∷ Bx3-0412 ∷ [])
  b9 = at 6 2 (CCZ023 ∷ CS12⁻ ∷ []) (sym (wl0620 (lit c4))) ▸
       at 5 2 (CCZ023 ∷ CX41 ∷ []) (lem-comm-CX41-CCZ023 (lit c4)) ▸
       at 4 2 (CCZ023 ∷ CS12 ∷ []) (sym (wl0621 (lit c4))) ▸
       at 5 5 (CCZ124 ∷ []) (sym (wl0334 (lit c4))) ▸
       at 5 2 [] (wl0263 (lit c4)) ▸
       at 1 4 (Bx3-4102 ∷ []) (sym (lem-box-tQ-at0314213042 c4)) ▸
       at 0 1 (Bx0-3412 ∷ []) (lem-box-perm-3124-at142142 c4) ▸
       at 1 1 (Bx3-0412 ∷ []) (lem-box-perm-3124-at0314213042 c4) ▸ done

  b10 : Chain (Bx0-3412 ∷ Bx3-0412 ∷ []) (Bx3-4102 ∷ Bx0-4132 ∷ [])
  b10 = at 0 2 (Bx3-0412 ∷ Bx0-3412 ∷ []) (lem-box-box-1-at13243142 c4) ▸
       at 0 1 (Bx3-4102 ∷ []) (lem-box-perm-2314-at0310243142 c4) ▸
       at 1 1 (Bx0-4132 ∷ []) (lem-box-perm-2314-at13243142 c4) ▸ done


-- sym-ab @0314213042: 18 steps
lem-sym-ab-at0314213042 : Ws → ⟪ (Bx3-4102 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1402 ∷ []) ⟫ʷ
lem-sym-ab-at0314213042 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx3-4102 ∷ []) (CCZ134 ∷ Toff314 ∷ CCZ013 ∷ Toff103 ∷ Bx3-12 ∷ Toff103 ∷ CCZ013 ∷ Bx3-12 ∷ Toff314 ∷ CCZ134 ∷ Bx4-302 ∷ [])
  b0 = at 0 1 (CCZ134 ∷ Toff314 ∷ Bx4-302 ∷ Toff314 ∷ CCZ134 ∷ Bx4-302 ∷ []) (refl) ▸
       at 2 1 (CCZ034 ∷ Toff403 ∷ Bx3-42 ∷ Toff403 ∷ CCZ034 ∷ Bx3-42 ∷ []) (refl) ▸
       at 4 1 (CZ24 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 2 6 (CCZ023 ∷ []) (sym (wp0661 c4)) ▸
       at 2 1 (CCZ013 ∷ Toff103 ∷ CZ12 ∷ Toff103 ∷ CCZ013 ∷ CZ12 ∷ []) (sym (wl0344 (lit c4))) ▸
       at 4 1 (Bx3-12 ∷ []) (refl) ▸
       at 7 1 (Bx3-12 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ134 ∷ Toff314 ∷ CCZ013 ∷ Toff103 ∷ Bx3-12 ∷ Toff103 ∷ CCZ013 ∷ Bx3-12 ∷ Toff314 ∷ CCZ134 ∷ Bx4-302 ∷ []) (CCZ134 ∷ Toff314 ∷ Bx1-302 ∷ Toff314 ∷ CCZ134 ∷ CCZ013 ∷ Toff103 ∷ Bx3-12 ∷ Toff103 ∷ CCZ013 ∷ Bx3-12 ∷ [])
  b1 = at 2 6 (Bx1-302 ∷ []) (refl) ▸
       at 5 1 (CCZ034 ∷ Toff403 ∷ Bx3-42 ∷ Toff403 ∷ CCZ034 ∷ Bx3-42 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 10 1 (CZ24 ∷ []) (refl) ▸
       at 5 6 (CCZ023 ∷ []) (sym (wp0661 c4)) ▸
       at 5 1 (CCZ013 ∷ Toff103 ∷ CZ12 ∷ Toff103 ∷ CCZ013 ∷ CZ12 ∷ []) (sym (wl0344 (lit c4))) ▸
       at 7 1 (Bx3-12 ∷ []) (refl) ▸
       at 10 1 (Bx3-12 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ134 ∷ Toff314 ∷ Bx1-302 ∷ Toff314 ∷ CCZ134 ∷ CCZ013 ∷ Toff103 ∷ Bx3-12 ∷ Toff103 ∷ CCZ013 ∷ Bx3-12 ∷ []) (Bx3-1402 ∷ [])
  b2 = at 5 6 (Bx1-302 ∷ []) (refl) ▸
       at 0 6 (Bx3-1402 ∷ []) (refl) ▸ done


-- tP @03243042: 7 steps
lem-tP-at03243042 : Ws → ⟪ (Toff314 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ Toff314 ∷ []) ⟫ʷ
lem-tP-at03243042 c4 = run b0
  where
  b0 : Chain (Toff314 ∷ Toff302 ∷ []) (Toff302 ∷ Toff314 ∷ [])
  b0 = at 0 1 (K3 ∷ CCZ134 ∷ K3⁻ ∷ []) (sym (wl0781 (lit c4))) ▸
       at 3 1 (K3 ∷ CCZ023 ∷ K3⁻ ∷ []) (sym (wl0782 (lit c4))) ▸
       at 2 2 [] (wl0436 (lit c4)) ▸
       at 1 2 (CCZ023 ∷ CCZ134 ∷ []) (lem-cQ-at03243042 c4) ▸
       at 2 0 (K3⁻ ∷ K3 ∷ []) (sym (wl0436 (lit c4))) ▸
       at 0 3 (Toff302 ∷ []) (wl0782 (lit c4)) ▸
       at 1 3 (Toff314 ∷ []) (wl0781 (lit c4)) ▸ done


-- P-box @03243042: 8 steps
lem-P-box-at03243042 : Ws → ⟪ (Toff302 ∷ Bx3-1402 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1402 ∷ []) ⟫ʷ
lem-P-box-at03243042 c4 = run b0
  where
  b0 : Chain (Toff302 ∷ Bx3-1402 ∷ Toff302 ∷ []) (Bx3-1402 ∷ [])
  b0 = at 1 1 (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ []) (lem-box-tQ-at03243042 c4) ▸
       at 0 2 (Toff314 ∷ Toff302 ∷ []) (sym (lem-tP-at03243042 c4)) ▸
       at 1 2 (CCZ023 ∷ CZ02 ∷ Toff302 ∷ []) (sym (wl1235 (lit c4))) ▸
       at 3 2 (Toff314 ∷ Toff302 ∷ []) (sym (lem-tP-at03243042 c4)) ▸
       at 4 3 (CCZ023 ∷ CZ02 ∷ []) (sym (wl1236 (lit c4))) ▸
       at 2 2 (Toff314 ∷ CZ02 ∷ []) (lem-comm-CZ02-TOFF314 (lit c4)) ▸
       at 3 3 (CCZ023 ∷ []) (sym (wl0774 (lit c4))) ▸
       at 0 4 (Bx3-1402 ∷ []) (sym (lem-box-tQ-at03243042 c4)) ▸ done


-- VPQ @03243042: 14 steps
lem-VPQ-at03243042 : Ws → ⟪ (Toff314 ∷ CCZ134 ∷ Toff302 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ []) ⟫ʷ
lem-VPQ-at03243042 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff314 ∷ CCZ134 ∷ Toff302 ∷ CCZ023 ∷ []) (CS02⁻ ∷ CS14⁻ ∷ S3 ∷ Toff302 ∷ Toff314 ∷ S3⁻ ∷ [])
  b0 = at 0 2 (CS14⁻ ∷ S3 ∷ Toff314 ∷ S3⁻ ∷ []) (sym (wl0783 (lit c4))) ▸
       at 4 2 (CS02⁻ ∷ S3 ∷ Toff302 ∷ S3⁻ ∷ []) (sym (wl0784 (lit c4))) ▸
       at 3 2 (CS02⁻ ∷ S3⁻ ∷ []) (sym (c₃ (Swap ↑ • (CS • CS • CS) • Swap ↑) (S • S • S))) ▸
       at 2 2 (CS02⁻ ∷ Toff314 ∷ []) (lem-comm-TOFF314-CSd02 (lit c4)) ▸
       at 1 2 (CS02⁻ ∷ S3 ∷ []) (sym (c₃ (Swap ↑ • (CS • CS • CS) • Swap ↑) (S))) ▸
       at 0 2 (CS02⁻ ∷ CS14⁻ ∷ []) (sym (wp0703 c4)) ▸
       at 4 2 [] (wl0441 (lit c4)) ▸
       at 3 2 (Toff302 ∷ Toff314 ∷ []) (lem-tP-at03243042 c4) ▸ done

  b1 : Chain (CS02⁻ ∷ CS14⁻ ∷ S3 ∷ Toff302 ∷ Toff314 ∷ S3⁻ ∷ []) (Toff302 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ [])
  b1 = at 4 0 (S3⁻ ∷ S3 ∷ []) (sym (wl0441 (lit c4))) ▸
       at 1 2 (S3 ∷ CS14⁻ ∷ []) (wl0785 (lit c4)) ▸
       at 2 2 (Toff302 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-TOFF302 (lit c4)) ▸
       at 3 2 (S3⁻ ∷ CS14⁻ ∷ []) (wl0786 (lit c4)) ▸
       at 0 4 (Toff302 ∷ CCZ023 ∷ []) (wl0784 (lit c4)) ▸
       at 2 4 (Toff314 ∷ CCZ134 ∷ []) (wl0783 (lit c4)) ▸ done


-- QVQ @03243042: 3 steps
lem-QVQ-at03243042 : Ws → ⟪ (CCZ023 ∷ Toff314 ∷ CCZ134 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ Toff314 ∷ CCZ134 ∷ Toff302 ∷ []) ⟫ʷ
lem-QVQ-at03243042 c4 = run b0
  where
  b0 : Chain (CCZ023 ∷ Toff314 ∷ CCZ134 ∷ CCZ023 ∷ []) (Toff302 ∷ Toff314 ∷ CCZ134 ∷ Toff302 ∷ [])
  b0 = at 0 0 (Toff302 ∷ Toff302 ∷ []) (sym (wl0787 (lit c4))) ▸
       at 1 4 (Toff314 ∷ CCZ134 ∷ Toff302 ∷ CCZ023 ∷ []) (sym (lem-VPQ-at03243042 c4)) ▸
       at 4 2 [] (wl0204 (lit c4)) ▸ done


-- box-cP @03243042: 12 steps
lem-box-cP-at03243042 : Ws → ⟪ (Bx3-1402 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) ⟫ʷ
lem-box-cP-at03243042 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-1402 ∷ []) (CCZ134 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ CCZ013 ∷ Toff103 ∷ CZ12 ∷ Toff103 ∷ CCZ013 ∷ CZ12 ∷ [])
  b0 = at 0 1 (CCZ134 ∷ Toff314 ∷ Bx1-302 ∷ Toff314 ∷ CCZ134 ∷ Bx1-302 ∷ []) (refl) ▸
       at 2 1 (CCZ013 ∷ Toff103 ∷ Bx3-12 ∷ Toff103 ∷ CCZ013 ∷ Bx3-12 ∷ []) (refl) ▸
       at 4 1 (CZ12 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 2 6 (CCZ023 ∷ []) (wl0344 (lit c4)) ▸
       at 5 1 (CCZ013 ∷ Toff103 ∷ Bx3-12 ∷ Toff103 ∷ CCZ013 ∷ Bx3-12 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 10 1 (CZ12 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ134 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ CCZ013 ∷ Toff103 ∷ CZ12 ∷ Toff103 ∷ CCZ013 ∷ CZ12 ∷ []) (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ [])
  b1 = at 5 6 (CCZ023 ∷ []) (wl0344 (lit c4)) ▸
       at 2 4 (Toff302 ∷ Toff314 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-QVQ-at03243042 c4) ▸
       at 1 2 (Toff302 ∷ Toff314 ∷ []) (lem-tP-at03243042 c4) ▸
       at 2 2 [] (wl0788 (lit c4)) ▸ done


-- pairs @03243042: 4 steps
lem-pairs-at03243042 : Ws → ⟪ (Bx3-1402 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0214 ∷ []) ⟫ʷ
lem-pairs-at03243042 c4 = run b0
  where
  b0 : Chain (Bx3-1402 ∷ []) (Bx3-0214 ∷ [])
  b0 = at 0 1 (Toff302 ∷ Bx3-1402 ∷ Toff302 ∷ []) (sym (lem-P-box-at03243042 c4)) ▸
       at 1 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at03243042 c4) ▸
       at 4 2 [] (wl0787 (lit c4)) ▸
       at 0 4 (Bx3-0214 ∷ []) (sym (lem-box-tQ-at031031 c4)) ▸ done


-- box-perm-2341 @0314213042: 4 steps
lem-box-perm-2341-at0314213042 : Ws → ⟪ (Bx3-4102 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1024 ∷ []) ⟫ʷ
lem-box-perm-2341-at0314213042 c4 = run b0
  where
  b0 : Chain (Bx3-4102 ∷ []) (Bx3-1024 ∷ [])
  b0 = at 0 1 (Bx3-1402 ∷ []) (lem-sym-ab-at0314213042 c4) ▸
       at 0 1 (Bx3-0214 ∷ []) (lem-pairs-at03243042 c4) ▸
       at 0 1 (Bx3-0124 ∷ []) (lem-sym-bc-at031031 c4) ▸
       at 0 1 (Bx3-1024 ∷ []) (lem-sym-ab-at03102132 c4) ▸ done


-- box-perm-2134 @032032: 1 steps
lem-box-perm-2134-at032032 : Ws → ⟪ (Bx3-1024 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ []) ⟫ʷ
lem-box-perm-2134-at032032 c4 = run b0
  where
  b0 : Chain (Bx3-1024 ∷ []) (Bx3-0124 ∷ [])
  b0 = at 0 1 (Bx3-0124 ∷ []) (lem-sym-ab-at032032 c4) ▸ done


-- sym-ab @142142: 18 steps
lem-sym-ab-at142142 : Ws → ⟪ (Bx0-4132 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1432 ∷ []) ⟫ʷ
lem-sym-ab-at142142 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx0-4132 ∷ []) (CCZ014 ∷ Toff014 ∷ CCZ013 ∷ Toff103 ∷ Bx0-12 ∷ Toff103 ∷ CCZ013 ∷ Bx0-12 ∷ Toff014 ∷ CCZ014 ∷ Bx4-032 ∷ [])
  b0 = at 0 1 (CCZ014 ∷ Toff014 ∷ Bx4-032 ∷ Toff014 ∷ CCZ014 ∷ Bx4-032 ∷ []) (refl) ▸
       at 2 1 (CCZ034 ∷ Toff403 ∷ Bx0-42 ∷ Toff403 ∷ CCZ034 ∷ Bx0-42 ∷ []) (refl) ▸
       at 4 1 (CZ24 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 2 6 (CCZ023 ∷ []) (sym (wp0661 c4)) ▸
       at 2 1 (CCZ013 ∷ Toff103 ∷ CZ12 ∷ Toff103 ∷ CCZ013 ∷ CZ12 ∷ []) (sym (wl0344 (lit c4))) ▸
       at 4 1 (Bx0-12 ∷ []) (refl) ▸
       at 7 1 (Bx0-12 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ014 ∷ Toff014 ∷ CCZ013 ∷ Toff103 ∷ Bx0-12 ∷ Toff103 ∷ CCZ013 ∷ Bx0-12 ∷ Toff014 ∷ CCZ014 ∷ Bx4-032 ∷ []) (CCZ014 ∷ Toff014 ∷ Bx1-032 ∷ Toff014 ∷ CCZ014 ∷ CCZ013 ∷ Toff103 ∷ Bx0-12 ∷ Toff103 ∷ CCZ013 ∷ Bx0-12 ∷ [])
  b1 = at 2 6 (Bx1-032 ∷ []) (refl) ▸
       at 5 1 (CCZ034 ∷ Toff403 ∷ Bx0-42 ∷ Toff403 ∷ CCZ034 ∷ Bx0-42 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 10 1 (CZ24 ∷ []) (refl) ▸
       at 5 6 (CCZ023 ∷ []) (sym (wp0661 c4)) ▸
       at 5 1 (CCZ013 ∷ Toff103 ∷ CZ12 ∷ Toff103 ∷ CCZ013 ∷ CZ12 ∷ []) (sym (wl0344 (lit c4))) ▸
       at 7 1 (Bx0-12 ∷ []) (refl) ▸
       at 10 1 (Bx0-12 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ014 ∷ Toff014 ∷ Bx1-032 ∷ Toff014 ∷ CCZ014 ∷ CCZ013 ∷ Toff103 ∷ Bx0-12 ∷ Toff103 ∷ CCZ013 ∷ Bx0-12 ∷ []) (Bx0-1432 ∷ [])
  b2 = at 5 6 (Bx1-032 ∷ []) (refl) ▸
       at 0 6 (Bx0-1432 ∷ []) (refl) ▸ done

