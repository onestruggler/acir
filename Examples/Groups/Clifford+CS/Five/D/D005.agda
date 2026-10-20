{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D005 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0006 ; wl0245 ; wl0306 ; wl0324 ; wl0326 ; wl0617 ; wl0621 ; wl0675 ; wl1167 ; wp0034 ; wp0035 ; wp0036 ; wp0062 ; wp0063 ; wp0064 ; wp0081 ; wp0092 ; wp0185 ; wp0194 ; wp0196 ; wp0312 ; wp0314 ; wp0513 ; wp0551 ; wp0553 ; wp0569 ; wp0570 ; wp0734 ; wp0972 ; wp0973 ; wl0003 ; wl0037 ; wl0038 ; wl0044 ; wl0045 ; wl0084 ; wl0085 ; wl0199 ; wl0434 ; wl0435 ; wl0436 ; wl0667 ; wl0669 ; wl0670 ; wl0698 ; wp0048 ; wp0087 ; wp0540 ; wp0543 ; wp0574 ; wp0594 ; wp0596 ; wp0986 ; wp0987 ; wp1003 ; wl0171 ; wl0173 ; wl0256 ; wl0322 ; wl0458 ; wl0490 ; wl0491 ; wl0492 ; wl0519 ; wl0520 ; wl0790 ; wl1220 ; wl1221 ; wl1237 ; wp0149 ; wp0151 ; wp0288 ; wp0289 ; wp0352 ; wp0706 ; wp1068 ; wl1270 ; wp0106 ; wp0107 ; wp0108 ; wp0150 ; wp0152 ; wp0184 ; wp0704 ; wp1089 ; wp1090 ; wp1091 ; wp1092 ; wp1093 ; wp1103 ; wp1104 ; wl0274 ; wp0582 ; wp0584 ; wp1116 ; wp1117 ; wl0838 ; wl0840 ; wl0876 ; wl0877 ; wp0296 ; wl0175 ; wl0288 ; wl0297 ; wl0416 ; wl0417 ; wl0485 ; wl0495 ; wl0611 ; wl0831 ; wl0928 ; wl0936 ; wl0937 ; wp0162 ; wp0195 ; wp0197 ; wp0320 ; wp0496 ; wp0746 ; wp1146 ; wp1147 ; wp1148 ; wp1149 ; wp1155 ; wp1156 ; wp1157 ; wp1158 ; wp1162 ; wp1163 ; wp1180 ; wp1181 ; wp1193 ; wl0271 ; wl0471 ; wl0639 ; wl0757 ; wl0930 ; wl0931 ; wp0123 ; wp0280 ; wp0318 ; wp0384 ; wp0450 ; wp0515 ; wp0679 ; wl0166 ; wl0283 ; wl0285 ; wl0287 ; wl0334 ; wl0620 ; wl0637 ; wl0638 ; wl0829 ; wl0989 ; wl0990 ; wl1379 ; wp0206 ; wp0208 ; wp0231 ; wp1237 ; wp1238 ; wl0284 ; wl0286 ; wl1399 ; wp1206 ; wl1669 ; wl1670 ; wl1671 ; wl1672 ; wl1680 ; wl1681 ; wp0722)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-cQ-at021021 ; lem-sym-ab-at0210243143 ; lem-sym-ab-at032032 ; lem-sym-ab-at1221)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-cQ-at0213243041 ; lem-cQ-at0214233041 ; lem-cQ-at0310213442 ; lem-sym-ab-at021021 ; lem-sym-ab-at0220)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-cQ-at03203442)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CX02-CCZ134 ; lem-comm-CX04-CCZ123 ; lem-comm-CX12-CCZ034 ; lem-comm-CX13-CCZ024 ; lem-comm-CX14-CCZ023 ; lem-comm-CX21-CCZ034 ; lem-comm-CX23-CCZ014 ; lem-comm-CX24-CCZ013 ; lem-comm-CX31-CCZ024 ; lem-comm-CX32-CCZ014 ; lem-comm-CX42-CCZ013 ; lem-comm-SWAP13-BOX⟨0·42⟩ ; lem-comm-SWAP14-BOX⟨0·23⟩)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-CX03-CCZ124 ; lem-comm-CX30-CCZ124 ; lem-comm-CX40-CCZ123 ; lem-comm-CX41-CCZ023 ; lem-comm-SWAP12-BOX⟨3·04⟩ ; lem-comm-SWAP12-BOX⟨3·40⟩ ; lem-comm-SWAP14-BOX⟨2·03⟩ ; lem-comm-SWAP23-BOX⟨0·41⟩ ; lem-comm-SWAP24-BOX⟨0·13⟩)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-CX20-CCZ134 ; lem-comm-SWAP02-BOX⟨3·41⟩ ; lem-comm-SWAP03-BOX⟨4·21⟩ ; lem-comm-SWAP04-BOX⟨3·21⟩ ; lem-comm-SWAP12-BOX⟨4·03⟩ ; lem-comm-SWAP13-BOX⟨2·04⟩ ; lem-comm-SWAP14-BOX⟨3·02⟩)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-comm-SWAP12-BOX⟨4·30⟩ ; lem-comm-SWAP13-BOX⟨4·20⟩)

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

-- nat-SWbc @0310213442: 23 steps
lem-nat-SWbc-at0310213442 : Ws → ⟪ (Sw14 ∷ Bx3-0142 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ []) ⟫ʷ
lem-nat-SWbc-at0310213442 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw14 ∷ Bx3-0142 ∷ Sw14 ∷ []) (CCZ034 ∷ Toff304 ∷ CCZ013 ∷ Toff013 ∷ Bx3-02 ∷ Toff013 ∷ Sw14 ∷ CCZ034 ∷ Bx3-02 ∷ Toff301 ∷ CCZ013 ∷ Bx0-342 ∷ Sw14 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff301 ∷ Bx0-342 ∷ Toff301 ∷ CCZ013 ∷ Bx0-342 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw14 ∷ []) (sym (wp0151 c4)) ▸
       at 1 2 (Toff304 ∷ Sw14 ∷ []) (wp0152 c4) ▸
       at 3 1 (CCZ034 ∷ Toff034 ∷ Bx3-02 ∷ Toff034 ∷ CCZ034 ∷ Bx3-02 ∷ []) (refl) ▸
       at 2 2 (CCZ013 ∷ Sw14 ∷ []) (sym (wp0149 c4)) ▸
       at 3 2 (Toff013 ∷ Sw14 ∷ []) (wp0150 c4) ▸
       at 4 2 (Bx3-02 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨3·02⟩ (lit c4)) ▸
       at 5 2 (Toff013 ∷ Sw14 ∷ []) (wp0150 c4) ▸ done

  b1 : Chain (CCZ034 ∷ Toff304 ∷ CCZ013 ∷ Toff013 ∷ Bx3-02 ∷ Toff013 ∷ Sw14 ∷ CCZ034 ∷ Bx3-02 ∷ Toff301 ∷ CCZ013 ∷ Bx0-342 ∷ Sw14 ∷ []) (CCZ034 ∷ Toff304 ∷ CCZ013 ∷ Toff013 ∷ Bx3-02 ∷ Toff013 ∷ CCZ013 ∷ Bx3-02 ∷ Toff304 ∷ CCZ034 ∷ CCZ013 ∷ Toff013 ∷ Bx3-02 ∷ Sw14 ∷ Toff034 ∷ CCZ034 ∷ Bx3-02 ∷ Sw14 ∷ [])
  b1 = at 6 2 (CCZ013 ∷ Sw14 ∷ []) (sym (wp0149 c4)) ▸
       at 7 2 (Bx3-02 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨3·02⟩ (lit c4)) ▸
       at 8 2 (Toff304 ∷ Sw14 ∷ []) (wp0152 c4) ▸
       at 9 2 (CCZ034 ∷ Sw14 ∷ []) (sym (wp0151 c4)) ▸
       at 11 1 (CCZ034 ∷ Toff034 ∷ Bx3-02 ∷ Toff034 ∷ CCZ034 ∷ Bx3-02 ∷ []) (refl) ▸
       at 10 2 (CCZ013 ∷ Sw14 ∷ []) (sym (wp0149 c4)) ▸
       at 11 2 (Toff013 ∷ Sw14 ∷ []) (wp0150 c4) ▸
       at 12 2 (Bx3-02 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨3·02⟩ (lit c4)) ▸ done

  b2 : Chain (CCZ034 ∷ Toff304 ∷ CCZ013 ∷ Toff013 ∷ Bx3-02 ∷ Toff013 ∷ CCZ013 ∷ Bx3-02 ∷ Toff304 ∷ CCZ034 ∷ CCZ013 ∷ Toff013 ∷ Bx3-02 ∷ Sw14 ∷ Toff034 ∷ CCZ034 ∷ Bx3-02 ∷ Sw14 ∷ []) (Bx3-0412 ∷ [])
  b2 = at 13 2 (Toff013 ∷ Sw14 ∷ []) (wp0150 c4) ▸
       at 14 2 (CCZ013 ∷ Sw14 ∷ []) (sym (wp0149 c4)) ▸
       at 15 2 (Bx3-02 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨3·02⟩ (lit c4)) ▸
       at 16 2 [] (wl0306 (lit c4)) ▸
       at 2 6 (Bx0-312 ∷ []) (refl) ▸
       at 5 6 (Bx0-312 ∷ []) (refl) ▸
       at 0 6 (Bx3-0412 ∷ []) (refl) ▸ done

-- cQ @0312203441: 7 steps
lem-cQ-at0312203441 : Ws → ⟪ (CCZ023 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ CCZ023 ∷ []) ⟫ʷ
lem-cQ-at0312203441 c4 = run b0
  where
  b0 : Chain (CCZ023 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ023 ∷ [])
  b0 = at 0 1 (CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ []) (wl1270 (lit c4)) ▸
       at 4 2 (CCZ134 ∷ CS23 ∷ []) (sym (wl0790 (lit c4))) ▸
       at 3 2 (CCZ134 ∷ CX20 ∷ []) (lem-comm-CX20-CCZ134 (lit c4)) ▸
       at 2 2 (CCZ134 ∷ CS03⁻ ∷ []) (sym (wp0704 c4)) ▸
       at 1 2 (CCZ134 ∷ CX20 ∷ []) (lem-comm-CX20-CCZ134 (lit c4)) ▸
       at 0 2 (CCZ134 ∷ CS03 ∷ []) (sym (wp0706 c4)) ▸
       at 1 5 (CCZ023 ∷ []) (sym (wl1270 (lit c4))) ▸ done

-- nat-SWbc @0312203441: 23 steps
lem-nat-SWbc-at0312203441 : Ws → ⟪ (Sw04 ∷ Bx3-2041 ∷ Sw04 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2401 ∷ []) ⟫ʷ
lem-nat-SWbc-at0312203441 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw04 ∷ Bx3-2041 ∷ Sw04 ∷ []) (CCZ234 ∷ Toff324 ∷ CCZ023 ∷ Toff203 ∷ Bx3-21 ∷ Toff203 ∷ Sw04 ∷ CCZ234 ∷ Bx3-21 ∷ Toff302 ∷ CCZ023 ∷ Bx2-341 ∷ Sw04 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff302 ∷ Bx2-341 ∷ Toff302 ∷ CCZ023 ∷ Bx2-341 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw04 ∷ []) (sym (wp1089 c4)) ▸
       at 1 2 (Toff324 ∷ Sw04 ∷ []) (wp1090 c4) ▸
       at 3 1 (CCZ234 ∷ Toff234 ∷ Bx3-21 ∷ Toff234 ∷ CCZ234 ∷ Bx3-21 ∷ []) (refl) ▸
       at 2 2 (CCZ023 ∷ Sw04 ∷ []) (sym (wp1091 c4)) ▸
       at 3 2 (Toff203 ∷ Sw04 ∷ []) (wp1092 c4) ▸
       at 4 2 (Bx3-21 ∷ Sw04 ∷ []) (lem-comm-SWAP04-BOX⟨3·21⟩ (lit c4)) ▸
       at 5 2 (Toff203 ∷ Sw04 ∷ []) (wp1092 c4) ▸ done

  b1 : Chain (CCZ234 ∷ Toff324 ∷ CCZ023 ∷ Toff203 ∷ Bx3-21 ∷ Toff203 ∷ Sw04 ∷ CCZ234 ∷ Bx3-21 ∷ Toff302 ∷ CCZ023 ∷ Bx2-341 ∷ Sw04 ∷ []) (CCZ234 ∷ Toff324 ∷ CCZ023 ∷ Toff203 ∷ Bx3-21 ∷ Toff203 ∷ CCZ023 ∷ Bx3-21 ∷ Toff324 ∷ CCZ234 ∷ CCZ023 ∷ Toff203 ∷ Bx3-21 ∷ Sw04 ∷ Toff234 ∷ CCZ234 ∷ Bx3-21 ∷ Sw04 ∷ [])
  b1 = at 6 2 (CCZ023 ∷ Sw04 ∷ []) (sym (wp1091 c4)) ▸
       at 7 2 (Bx3-21 ∷ Sw04 ∷ []) (lem-comm-SWAP04-BOX⟨3·21⟩ (lit c4)) ▸
       at 8 2 (Toff324 ∷ Sw04 ∷ []) (wp1090 c4) ▸
       at 9 2 (CCZ234 ∷ Sw04 ∷ []) (sym (wp1089 c4)) ▸
       at 11 1 (CCZ234 ∷ Toff234 ∷ Bx3-21 ∷ Toff234 ∷ CCZ234 ∷ Bx3-21 ∷ []) (refl) ▸
       at 10 2 (CCZ023 ∷ Sw04 ∷ []) (sym (wp1091 c4)) ▸
       at 11 2 (Toff203 ∷ Sw04 ∷ []) (wp1092 c4) ▸
       at 12 2 (Bx3-21 ∷ Sw04 ∷ []) (lem-comm-SWAP04-BOX⟨3·21⟩ (lit c4)) ▸ done

  b2 : Chain (CCZ234 ∷ Toff324 ∷ CCZ023 ∷ Toff203 ∷ Bx3-21 ∷ Toff203 ∷ CCZ023 ∷ Bx3-21 ∷ Toff324 ∷ CCZ234 ∷ CCZ023 ∷ Toff203 ∷ Bx3-21 ∷ Sw04 ∷ Toff234 ∷ CCZ234 ∷ Bx3-21 ∷ Sw04 ∷ []) (Bx3-2401 ∷ [])
  b2 = at 13 2 (Toff203 ∷ Sw04 ∷ []) (wp1092 c4) ▸
       at 14 2 (CCZ023 ∷ Sw04 ∷ []) (sym (wp1091 c4)) ▸
       at 15 2 (Bx3-21 ∷ Sw04 ∷ []) (lem-comm-SWAP04-BOX⟨3·21⟩ (lit c4)) ▸
       at 16 2 [] (wp1093 c4) ▸
       at 2 6 (Bx2-301 ∷ []) (refl) ▸
       at 5 6 (Bx2-301 ∷ []) (refl) ▸
       at 0 6 (Bx3-2401 ∷ []) (refl) ▸ done

-- cQ @0312243041: 7 steps
lem-cQ-at0312243041 : Ws → ⟪ (CCZ234 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ CCZ234 ∷ []) ⟫ʷ
lem-cQ-at0312243041 c4 = run b0
  where
  b0 : Chain (CCZ234 ∷ CCZ013 ∷ []) (CCZ013 ∷ CCZ234 ∷ [])
  b0 = at 0 1 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (wl0245 (lit c4)) ▸
       at 4 2 (CCZ013 ∷ CS23 ∷ []) (sym (wl0324 (lit c4))) ▸
       at 3 2 (CCZ013 ∷ CX24 ∷ []) (lem-comm-CX24-CCZ013 (lit c4)) ▸
       at 2 2 (CCZ013 ∷ CS34⁻ ∷ []) (sym (wp0184 c4)) ▸
       at 1 2 (CCZ013 ∷ CX24 ∷ []) (lem-comm-CX24-CCZ013 (lit c4)) ▸
       at 0 2 (CCZ013 ∷ CS34 ∷ []) (sym (wp0185 c4)) ▸
       at 1 5 (CCZ234 ∷ []) (sym (wl0245 (lit c4))) ▸ done

-- nat-SWbc @0312243041: 23 steps
lem-nat-SWbc-at0312243041 : Ws → ⟪ (Sw04 ∷ Bx3-2401 ∷ Sw04 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2041 ∷ []) ⟫ʷ
lem-nat-SWbc-at0312243041 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw04 ∷ Bx3-2401 ∷ Sw04 ∷ []) (CCZ023 ∷ Toff302 ∷ CCZ234 ∷ Toff234 ∷ Bx3-21 ∷ Toff234 ∷ Sw04 ∷ CCZ023 ∷ Bx3-21 ∷ Toff324 ∷ CCZ234 ∷ Bx2-301 ∷ Sw04 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff324 ∷ Bx2-301 ∷ Toff324 ∷ CCZ234 ∷ Bx2-301 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw04 ∷ []) (sym (wp1091 c4)) ▸
       at 1 2 (Toff302 ∷ Sw04 ∷ []) (wp1103 c4) ▸
       at 3 1 (CCZ023 ∷ Toff203 ∷ Bx3-21 ∷ Toff203 ∷ CCZ023 ∷ Bx3-21 ∷ []) (refl) ▸
       at 2 2 (CCZ234 ∷ Sw04 ∷ []) (sym (wp1089 c4)) ▸
       at 3 2 (Toff234 ∷ Sw04 ∷ []) (wp1104 c4) ▸
       at 4 2 (Bx3-21 ∷ Sw04 ∷ []) (lem-comm-SWAP04-BOX⟨3·21⟩ (lit c4)) ▸
       at 5 2 (Toff234 ∷ Sw04 ∷ []) (wp1104 c4) ▸ done

  b1 : Chain (CCZ023 ∷ Toff302 ∷ CCZ234 ∷ Toff234 ∷ Bx3-21 ∷ Toff234 ∷ Sw04 ∷ CCZ023 ∷ Bx3-21 ∷ Toff324 ∷ CCZ234 ∷ Bx2-301 ∷ Sw04 ∷ []) (CCZ023 ∷ Toff302 ∷ CCZ234 ∷ Toff234 ∷ Bx3-21 ∷ Toff234 ∷ CCZ234 ∷ Bx3-21 ∷ Toff302 ∷ CCZ023 ∷ CCZ234 ∷ Toff234 ∷ Bx3-21 ∷ Sw04 ∷ Toff203 ∷ CCZ023 ∷ Bx3-21 ∷ Sw04 ∷ [])
  b1 = at 6 2 (CCZ234 ∷ Sw04 ∷ []) (sym (wp1089 c4)) ▸
       at 7 2 (Bx3-21 ∷ Sw04 ∷ []) (lem-comm-SWAP04-BOX⟨3·21⟩ (lit c4)) ▸
       at 8 2 (Toff302 ∷ Sw04 ∷ []) (wp1103 c4) ▸
       at 9 2 (CCZ023 ∷ Sw04 ∷ []) (sym (wp1091 c4)) ▸
       at 11 1 (CCZ023 ∷ Toff203 ∷ Bx3-21 ∷ Toff203 ∷ CCZ023 ∷ Bx3-21 ∷ []) (refl) ▸
       at 10 2 (CCZ234 ∷ Sw04 ∷ []) (sym (wp1089 c4)) ▸
       at 11 2 (Toff234 ∷ Sw04 ∷ []) (wp1104 c4) ▸
       at 12 2 (Bx3-21 ∷ Sw04 ∷ []) (lem-comm-SWAP04-BOX⟨3·21⟩ (lit c4)) ▸ done

  b2 : Chain (CCZ023 ∷ Toff302 ∷ CCZ234 ∷ Toff234 ∷ Bx3-21 ∷ Toff234 ∷ CCZ234 ∷ Bx3-21 ∷ Toff302 ∷ CCZ023 ∷ CCZ234 ∷ Toff234 ∷ Bx3-21 ∷ Sw04 ∷ Toff203 ∷ CCZ023 ∷ Bx3-21 ∷ Sw04 ∷ []) (Bx3-2041 ∷ [])
  b2 = at 13 2 (Toff234 ∷ Sw04 ∷ []) (wp1104 c4) ▸
       at 14 2 (CCZ234 ∷ Sw04 ∷ []) (sym (wp1089 c4)) ▸
       at 15 2 (Bx3-21 ∷ Sw04 ∷ []) (lem-comm-SWAP04-BOX⟨3·21⟩ (lit c4)) ▸
       at 16 2 [] (wp1093 c4) ▸
       at 2 6 (Bx2-341 ∷ []) (refl) ▸
       at 5 6 (Bx2-341 ∷ []) (refl) ▸
       at 0 6 (Bx3-2041 ∷ []) (refl) ▸ done

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

-- cQ @03122031: 7 steps
lem-cQ-at03122031 : Ws → ⟪ (CCZ023 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ CCZ023 ∷ []) ⟫ʷ
lem-cQ-at03122031 c4 = run b0
  where
  b0 : Chain (CCZ023 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ023 ∷ [])
  b0 = at 0 1 (CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ []) (wl1270 (lit c4)) ▸
       at 4 2 (CCZ134 ∷ CS23 ∷ []) (sym (wl0790 (lit c4))) ▸
       at 3 2 (CCZ134 ∷ CX20 ∷ []) (lem-comm-CX20-CCZ134 (lit c4)) ▸
       at 2 2 (CCZ134 ∷ CS03⁻ ∷ []) (sym (wp0704 c4)) ▸
       at 1 2 (CCZ134 ∷ CX20 ∷ []) (lem-comm-CX20-CCZ134 (lit c4)) ▸
       at 0 2 (CCZ134 ∷ CS03 ∷ []) (sym (wp0706 c4)) ▸
       at 1 5 (CCZ023 ∷ []) (sym (wl1270 (lit c4))) ▸ done

-- cQ @031031: 7 steps
lem-cQ-at031031 : Ws → ⟪ (CCZ023 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ CCZ023 ∷ []) ⟫ʷ
lem-cQ-at031031 c4 = run b0
  where
  b0 : Chain (CCZ023 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ023 ∷ [])
  b0 = at 0 1 (CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ []) (wl0458 (lit c4)) ▸
       at 4 2 (CCZ134 ∷ CS03 ∷ []) (sym (wp0706 c4)) ▸
       at 3 2 (CCZ134 ∷ CX02 ∷ []) (lem-comm-CX02-CCZ134 (lit c4)) ▸
       at 2 2 (CCZ134 ∷ CS23⁻ ∷ []) (sym (wl1237 (lit c4))) ▸
       at 1 2 (CCZ134 ∷ CX02 ∷ []) (lem-comm-CX02-CCZ134 (lit c4)) ▸
       at 0 2 (CCZ134 ∷ CS23 ∷ []) (sym (wl0790 (lit c4))) ▸
       at 1 5 (CCZ023 ∷ []) (sym (wl0458 (lit c4))) ▸ done

-- nat-SWbc @031031: 23 steps
lem-nat-SWbc-at031031 : Ws → ⟪ (Sw12 ∷ Bx3-0214 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ []) ⟫ʷ
lem-nat-SWbc-at031031 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw12 ∷ Bx3-0214 ∷ Sw12 ∷ []) (CCZ013 ∷ Toff301 ∷ CCZ023 ∷ Toff023 ∷ Bx3-04 ∷ Toff023 ∷ Sw12 ∷ CCZ013 ∷ Bx3-04 ∷ Toff302 ∷ CCZ023 ∷ Bx0-314 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff302 ∷ Bx0-314 ∷ Toff302 ∷ CCZ023 ∷ Bx0-314 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw12 ∷ []) (sym (wl0838 (lit c4))) ▸
       at 1 2 (Toff301 ∷ Sw12 ∷ []) (wl0877 (lit c4)) ▸
       at 3 1 (CCZ013 ∷ Toff013 ∷ Bx3-04 ∷ Toff013 ∷ CCZ013 ∷ Bx3-04 ∷ []) (refl) ▸
       at 2 2 (CCZ023 ∷ Sw12 ∷ []) (sym (wl0840 (lit c4))) ▸
       at 3 2 (Toff023 ∷ Sw12 ∷ []) (wl0876 (lit c4)) ▸
       at 4 2 (Bx3-04 ∷ Sw12 ∷ []) (lem-comm-SWAP12-BOX⟨3·04⟩ (lit c4)) ▸
       at 5 2 (Toff023 ∷ Sw12 ∷ []) (wl0876 (lit c4)) ▸ done

  b1 : Chain (CCZ013 ∷ Toff301 ∷ CCZ023 ∷ Toff023 ∷ Bx3-04 ∷ Toff023 ∷ Sw12 ∷ CCZ013 ∷ Bx3-04 ∷ Toff302 ∷ CCZ023 ∷ Bx0-314 ∷ Sw12 ∷ []) (CCZ013 ∷ Toff301 ∷ CCZ023 ∷ Toff023 ∷ Bx3-04 ∷ Toff023 ∷ CCZ023 ∷ Bx3-04 ∷ Toff301 ∷ CCZ013 ∷ CCZ023 ∷ Toff023 ∷ Bx3-04 ∷ Sw12 ∷ Toff013 ∷ CCZ013 ∷ Bx3-04 ∷ Sw12 ∷ [])
  b1 = at 6 2 (CCZ023 ∷ Sw12 ∷ []) (sym (wl0840 (lit c4))) ▸
       at 7 2 (Bx3-04 ∷ Sw12 ∷ []) (lem-comm-SWAP12-BOX⟨3·04⟩ (lit c4)) ▸
       at 8 2 (Toff301 ∷ Sw12 ∷ []) (wl0877 (lit c4)) ▸
       at 9 2 (CCZ013 ∷ Sw12 ∷ []) (sym (wl0838 (lit c4))) ▸
       at 11 1 (CCZ013 ∷ Toff013 ∷ Bx3-04 ∷ Toff013 ∷ CCZ013 ∷ Bx3-04 ∷ []) (refl) ▸
       at 10 2 (CCZ023 ∷ Sw12 ∷ []) (sym (wl0840 (lit c4))) ▸
       at 11 2 (Toff023 ∷ Sw12 ∷ []) (wl0876 (lit c4)) ▸
       at 12 2 (Bx3-04 ∷ Sw12 ∷ []) (lem-comm-SWAP12-BOX⟨3·04⟩ (lit c4)) ▸ done

  b2 : Chain (CCZ013 ∷ Toff301 ∷ CCZ023 ∷ Toff023 ∷ Bx3-04 ∷ Toff023 ∷ CCZ023 ∷ Bx3-04 ∷ Toff301 ∷ CCZ013 ∷ CCZ023 ∷ Toff023 ∷ Bx3-04 ∷ Sw12 ∷ Toff013 ∷ CCZ013 ∷ Bx3-04 ∷ Sw12 ∷ []) (Bx3-0124 ∷ [])
  b2 = at 13 2 (Toff023 ∷ Sw12 ∷ []) (wl0876 (lit c4)) ▸
       at 14 2 (CCZ023 ∷ Sw12 ∷ []) (sym (wl0840 (lit c4))) ▸
       at 15 2 (Bx3-04 ∷ Sw12 ∷ []) (lem-comm-SWAP12-BOX⟨3·04⟩ (lit c4)) ▸
       at 16 2 [] (wl0006 (lit c4)) ▸
       at 2 6 (Bx0-324 ∷ []) (refl) ▸
       at 5 6 (Bx0-324 ∷ []) (refl) ▸
       at 0 6 (Bx3-0124 ∷ []) (refl) ▸ done

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

-- cQ @02132031: 7 steps
lem-cQ-at02132031 : Ws → ⟪ (CCZ023 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ CCZ023 ∷ []) ⟫ʷ
lem-cQ-at02132031 c4 = run b0
  where
  b0 : Chain (CCZ023 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ023 ∷ [])
  b0 = at 0 1 (CS02 ∷ CX30 ∷ CS02⁻ ∷ CX30 ∷ CS23 ∷ []) (wl0757 (lit c4)) ▸
       at 4 2 (CCZ124 ∷ CS23 ∷ []) (sym (wl0639 (lit c4))) ▸
       at 3 2 (CCZ124 ∷ CX30 ∷ []) (lem-comm-CX30-CCZ124 (lit c4)) ▸
       at 2 2 (CCZ124 ∷ CS02⁻ ∷ []) (sym (wp0679 c4)) ▸
       at 1 2 (CCZ124 ∷ CX30 ∷ []) (lem-comm-CX30-CCZ124 (lit c4)) ▸
       at 0 2 (CCZ124 ∷ CS02 ∷ []) (sym (wp0515 c4)) ▸
       at 1 5 (CCZ023 ∷ []) (sym (wl0757 (lit c4))) ▸ done

-- tP @0310213442: 7 steps
lem-tP-at0310213442 : Ws → ⟪ (Toff301 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ Toff301 ∷ []) ⟫ʷ
lem-tP-at0310213442 c4 = run b0
  where
  b0 : Chain (Toff301 ∷ Toff324 ∷ []) (Toff324 ∷ Toff301 ∷ [])
  b0 = at 0 1 (K3 ∷ CCZ013 ∷ K3⁻ ∷ []) (sym (wl0434 (lit c4))) ▸
       at 3 1 (K3 ∷ CCZ234 ∷ K3⁻ ∷ []) (sym (wl0435 (lit c4))) ▸
       at 2 2 [] (wl0436 (lit c4)) ▸
       at 1 2 (CCZ234 ∷ CCZ013 ∷ []) (lem-cQ-at0310213442 c4) ▸
       at 2 0 (K3⁻ ∷ K3 ∷ []) (sym (wl0436 (lit c4))) ▸
       at 0 3 (Toff324 ∷ []) (wl0435 (lit c4)) ▸
       at 1 3 (Toff301 ∷ []) (wl0434 (lit c4)) ▸ done

-- tP @0213243041: 7 steps
lem-tP-at0213243041 : Ws → ⟪ (Toff234 ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ Toff234 ∷ []) ⟫ʷ
lem-tP-at0213243041 c4 = run b0
  where
  b0 : Chain (Toff234 ∷ Toff201 ∷ []) (Toff201 ∷ Toff234 ∷ [])
  b0 = at 0 1 (K2 ∷ CCZ234 ∷ K2⁻ ∷ []) (sym (wl0417 (lit c4))) ▸
       at 3 1 (K2 ∷ CCZ012 ∷ K2⁻ ∷ []) (sym (wl0416 (lit c4))) ▸
       at 2 2 [] (wl0175 (lit c4)) ▸
       at 1 2 (CCZ012 ∷ CCZ234 ∷ []) (lem-cQ-at0213243041 c4) ▸
       at 2 0 (K2⁻ ∷ K2 ∷ []) (sym (wl0175 (lit c4))) ▸
       at 0 3 (Toff201 ∷ []) (wl0416 (lit c4)) ▸
       at 1 3 (Toff234 ∷ []) (wl0417 (lit c4)) ▸ done

-- box-tQ @0213243041: 13 steps
lem-box-tQ-at0213243041 : Ws → ⟪ (Bx2-3401 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ CCZ012 ∷ Toff234 ∷ CCZ012 ∷ []) ⟫ʷ
lem-box-tQ-at0213243041 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx2-3401 ∷ []) (CCZ234 ∷ Toff234 ∷ CCZ012 ∷ Toff234 ∷ CCZ234 ∷ CCZ023 ∷ Toff302 ∷ CZ13 ∷ Toff302 ∷ CCZ023 ∷ CZ13 ∷ [])
  b0 = at 0 1 (CCZ234 ∷ Toff234 ∷ Bx3-201 ∷ Toff234 ∷ CCZ234 ∷ Bx3-201 ∷ []) (refl) ▸
       at 2 1 (CCZ023 ∷ Toff302 ∷ Bx2-31 ∷ Toff302 ∷ CCZ023 ∷ Bx2-31 ∷ []) (refl) ▸
       at 4 1 (CZ13 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 2 6 (CCZ012 ∷ []) (sym (wl0288 (lit c4))) ▸
       at 5 1 (CCZ023 ∷ Toff302 ∷ Bx2-31 ∷ Toff302 ∷ CCZ023 ∷ Bx2-31 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 10 1 (CZ13 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ234 ∷ Toff234 ∷ CCZ012 ∷ Toff234 ∷ CCZ234 ∷ CCZ023 ∷ Toff302 ∷ CZ13 ∷ Toff302 ∷ CCZ023 ∷ CZ13 ∷ []) (Toff234 ∷ CCZ012 ∷ Toff234 ∷ CCZ012 ∷ [])
  b1 = at 5 6 (CCZ012 ∷ []) (sym (wl0288 (lit c4))) ▸
       at 0 2 (Toff234 ∷ CCZ234 ∷ CZ34 ∷ []) (wl0936 (lit c4)) ▸
       at 2 2 (CCZ012 ∷ CZ34 ∷ []) (sym (c₃ (CCZ) (CZ))) ▸
       at 1 2 (CCZ012 ∷ CCZ234 ∷ []) (lem-cQ-at0213243041 c4) ▸
       at 2 4 (Toff234 ∷ []) (wl0937 (lit c4)) ▸ done

-- box-tQ @021021: 13 steps
lem-box-tQ-at021021 : Ws → ⟪ (Bx2-0134 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) ⟫ʷ
lem-box-tQ-at021021 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx2-0134 ∷ []) (CCZ012 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ012 ∷ CCZ023 ∷ Toff023 ∷ CZ04 ∷ Toff023 ∷ CCZ023 ∷ CZ04 ∷ [])
  b0 = at 0 1 (CCZ012 ∷ Toff201 ∷ Bx0-234 ∷ Toff201 ∷ CCZ012 ∷ Bx0-234 ∷ []) (refl) ▸
       at 2 1 (CCZ023 ∷ Toff023 ∷ Bx2-04 ∷ Toff023 ∷ CCZ023 ∷ Bx2-04 ∷ []) (refl) ▸
       at 4 1 (CZ04 ∷ []) (refl) ▸
       at 7 1 (CZ04 ∷ []) (refl) ▸
       at 2 6 (CCZ234 ∷ []) (wp0280 c4) ▸
       at 5 1 (CCZ023 ∷ Toff023 ∷ Bx2-04 ∷ Toff023 ∷ CCZ023 ∷ Bx2-04 ∷ []) (refl) ▸
       at 7 1 (CZ04 ∷ []) (refl) ▸
       at 10 1 (CZ04 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ012 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ012 ∷ CCZ023 ∷ Toff023 ∷ CZ04 ∷ Toff023 ∷ CCZ023 ∷ CZ04 ∷ []) (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ [])
  b1 = at 5 6 (CCZ234 ∷ []) (wp0280 c4) ▸
       at 0 2 (Toff201 ∷ CCZ012 ∷ CZ01 ∷ []) (wl0930 (lit c4)) ▸
       at 2 2 (CCZ234 ∷ CZ01 ∷ []) (c₂ (CZ) (CCZ)) ▸
       at 1 2 (CCZ234 ∷ CCZ012 ∷ []) (lem-cQ-at021021 c4) ▸
       at 2 4 (Toff201 ∷ []) (wl0931 (lit c4)) ▸ done

-- cQ @03122130: 7 steps
lem-cQ-at03122130 : Ws → ⟪ (CCZ123 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ CCZ123 ∷ []) ⟫ʷ
lem-cQ-at03122130 c4 = run b0
  where
  b0 : Chain (CCZ123 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ123 ∷ [])
  b0 = at 0 1 (CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ []) (wl0326 (lit c4)) ▸
       at 4 2 (CCZ034 ∷ CS23 ∷ []) (sym (wp0314 c4)) ▸
       at 3 2 (CCZ034 ∷ CX21 ∷ []) (lem-comm-CX21-CCZ034 (lit c4)) ▸
       at 2 2 (CCZ034 ∷ CS13⁻ ∷ []) (sym (wp0734 c4)) ▸
       at 1 2 (CCZ034 ∷ CX21 ∷ []) (lem-comm-CX21-CCZ034 (lit c4)) ▸
       at 0 2 (CCZ034 ∷ CS13 ∷ []) (sym (wp0312 c4)) ▸
       at 1 5 (CCZ123 ∷ []) (sym (wl0326 (lit c4))) ▸ done

-- box-perm-2134 @1221: 1 steps
lem-box-perm-2134-at1221 : Ws → ⟪ (Bx0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-box-perm-2134-at1221 c4 = run b0
  where
  b0 : Chain (Bx0-2134 ∷ []) (Bx0-1234 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ []) (lem-sym-ab-at1221 c4) ▸ done

-- box-perm-2134 @021021: 1 steps
lem-box-perm-2134-at021021 : Ws → ⟪ (Bx2-0134 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1034 ∷ []) ⟫ʷ
lem-box-perm-2134-at021021 c4 = run b0
  where
  b0 : Chain (Bx2-0134 ∷ []) (Bx2-1034 ∷ [])
  b0 = at 0 1 (Bx2-1034 ∷ []) (lem-sym-ab-at021021 c4) ▸ done

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

-- box-perm-2134 @0220: 1 steps
lem-box-perm-2134-at0220 : Ws → ⟪ (Bx2-1034 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ []) ⟫ʷ
lem-box-perm-2134-at0220 c4 = run b0
  where
  b0 : Chain (Bx2-1034 ∷ []) (Bx2-0134 ∷ [])
  b0 = at 0 1 (Bx2-0134 ∷ []) (lem-sym-ab-at0220 c4) ▸ done

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

-- box-perm-2134 @032032: 1 steps
lem-box-perm-2134-at032032 : Ws → ⟪ (Bx3-1024 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ []) ⟫ʷ
lem-box-perm-2134-at032032 c4 = run b0
  where
  b0 : Chain (Bx3-1024 ∷ []) (Bx3-0124 ∷ [])
  b0 = at 0 1 (Bx3-0124 ∷ []) (lem-sym-ab-at032032 c4) ▸ done

-- nat-SWbc @02102331: 23 steps
lem-nat-SWbc-at02102331 : Ws → ⟪ (Sw13 ∷ Bx2-0314 ∷ Sw13 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ []) ⟫ʷ
lem-nat-SWbc-at02102331 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw13 ∷ Bx2-0314 ∷ Sw13 ∷ []) (CCZ012 ∷ Toff201 ∷ CCZ023 ∷ Toff023 ∷ Bx2-04 ∷ Toff023 ∷ Sw13 ∷ CCZ012 ∷ Bx2-04 ∷ Toff203 ∷ CCZ023 ∷ Bx0-214 ∷ Sw13 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff203 ∷ Bx0-214 ∷ Toff203 ∷ CCZ023 ∷ Bx0-214 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw13 ∷ []) (sym (wl0285 (lit c4))) ▸
       at 1 2 (Toff201 ∷ Sw13 ∷ []) (wl0286 (lit c4)) ▸
       at 3 1 (CCZ012 ∷ Toff012 ∷ Bx2-04 ∷ Toff012 ∷ CCZ012 ∷ Bx2-04 ∷ []) (refl) ▸
       at 2 2 (CCZ023 ∷ Sw13 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 3 2 (Toff023 ∷ Sw13 ∷ []) (wl0284 (lit c4)) ▸
       at 4 2 (Bx2-04 ∷ Sw13 ∷ []) (lem-comm-SWAP13-BOX⟨2·04⟩ (lit c4)) ▸
       at 5 2 (Toff023 ∷ Sw13 ∷ []) (wl0284 (lit c4)) ▸ done

  b1 : Chain (CCZ012 ∷ Toff201 ∷ CCZ023 ∷ Toff023 ∷ Bx2-04 ∷ Toff023 ∷ Sw13 ∷ CCZ012 ∷ Bx2-04 ∷ Toff203 ∷ CCZ023 ∷ Bx0-214 ∷ Sw13 ∷ []) (CCZ012 ∷ Toff201 ∷ CCZ023 ∷ Toff023 ∷ Bx2-04 ∷ Toff023 ∷ CCZ023 ∷ Bx2-04 ∷ Toff201 ∷ CCZ012 ∷ CCZ023 ∷ Toff023 ∷ Bx2-04 ∷ Sw13 ∷ Toff012 ∷ CCZ012 ∷ Bx2-04 ∷ Sw13 ∷ [])
  b1 = at 6 2 (CCZ023 ∷ Sw13 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 7 2 (Bx2-04 ∷ Sw13 ∷ []) (lem-comm-SWAP13-BOX⟨2·04⟩ (lit c4)) ▸
       at 8 2 (Toff201 ∷ Sw13 ∷ []) (wl0286 (lit c4)) ▸
       at 9 2 (CCZ012 ∷ Sw13 ∷ []) (sym (wl0285 (lit c4))) ▸
       at 11 1 (CCZ012 ∷ Toff012 ∷ Bx2-04 ∷ Toff012 ∷ CCZ012 ∷ Bx2-04 ∷ []) (refl) ▸
       at 10 2 (CCZ023 ∷ Sw13 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 2 (Toff023 ∷ Sw13 ∷ []) (wl0284 (lit c4)) ▸
       at 12 2 (Bx2-04 ∷ Sw13 ∷ []) (lem-comm-SWAP13-BOX⟨2·04⟩ (lit c4)) ▸ done

  b2 : Chain (CCZ012 ∷ Toff201 ∷ CCZ023 ∷ Toff023 ∷ Bx2-04 ∷ Toff023 ∷ CCZ023 ∷ Bx2-04 ∷ Toff201 ∷ CCZ012 ∷ CCZ023 ∷ Toff023 ∷ Bx2-04 ∷ Sw13 ∷ Toff012 ∷ CCZ012 ∷ Bx2-04 ∷ Sw13 ∷ []) (Bx2-0134 ∷ [])
  b2 = at 13 2 (Toff023 ∷ Sw13 ∷ []) (wl0284 (lit c4)) ▸
       at 14 2 (CCZ023 ∷ Sw13 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 15 2 (Bx2-04 ∷ Sw13 ∷ []) (lem-comm-SWAP13-BOX⟨2·04⟩ (lit c4)) ▸
       at 16 2 [] (wl0287 (lit c4)) ▸
       at 2 6 (Bx0-234 ∷ []) (refl) ▸
       at 5 6 (Bx0-234 ∷ []) (refl) ▸
       at 0 6 (Bx2-0134 ∷ []) (refl) ▸ done

-- box-perm-2134 @0210243143: 1 steps
lem-box-perm-2134-at0210243143 : Ws → ⟪ (Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4013 ∷ []) ⟫ʷ
lem-box-perm-2134-at0210243143 c4 = run b0
  where
  b0 : Chain (Bx2-0413 ∷ []) (Bx2-4013 ∷ [])
  b0 = at 0 1 (Bx2-4013 ∷ []) (lem-sym-ab-at0210243143 c4) ▸ done

-- cQ @04122041: 7 steps
lem-cQ-at04122041 : Ws → ⟪ (CCZ024 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ CCZ024 ∷ []) ⟫ʷ
lem-cQ-at04122041 c4 = run b0
  where
  b0 : Chain (CCZ024 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ024 ∷ [])
  b0 = at 0 1 (CS04 ∷ CX20 ∷ CS04⁻ ∷ CX20 ∷ CS24 ∷ []) (wp0450 c4) ▸
       at 4 2 (CCZ134 ∷ CS24 ∷ []) (sym (wl1220 (lit c4))) ▸
       at 3 2 (CCZ134 ∷ CX20 ∷ []) (lem-comm-CX20-CCZ134 (lit c4)) ▸
       at 2 2 (CCZ134 ∷ CS04⁻ ∷ []) (sym (wp1206 c4)) ▸
       at 1 2 (CCZ134 ∷ CX20 ∷ []) (lem-comm-CX20-CCZ134 (lit c4)) ▸
       at 0 2 (CCZ134 ∷ CS04 ∷ []) (sym (wp1003 c4)) ▸
       at 1 5 (CCZ024 ∷ []) (sym (wp0450 c4)) ▸ done

-- nat-SWbc @04122041: 23 steps
lem-nat-SWbc-at04122041 : Ws → ⟪ (Sw03 ∷ Bx4-2031 ∷ Sw03 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2301 ∷ []) ⟫ʷ
lem-nat-SWbc-at04122041 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw03 ∷ Bx4-2031 ∷ Sw03 ∷ []) (CCZ234 ∷ Toff423 ∷ CCZ024 ∷ Toff204 ∷ Bx4-21 ∷ Toff204 ∷ Sw03 ∷ CCZ234 ∷ Bx4-21 ∷ Toff402 ∷ CCZ024 ∷ Bx2-431 ∷ Sw03 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff402 ∷ Bx2-431 ∷ Toff402 ∷ CCZ024 ∷ Bx2-431 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw03 ∷ []) (sym (wp1155 c4)) ▸
       at 1 2 (Toff423 ∷ Sw03 ∷ []) (wp1181 c4) ▸
       at 3 1 (CCZ234 ∷ Toff234 ∷ Bx4-21 ∷ Toff234 ∷ CCZ234 ∷ Bx4-21 ∷ []) (refl) ▸
       at 2 2 (CCZ024 ∷ Sw03 ∷ []) (sym (wp1157 c4)) ▸
       at 3 2 (Toff204 ∷ Sw03 ∷ []) (wp1180 c4) ▸
       at 4 2 (Bx4-21 ∷ Sw03 ∷ []) (lem-comm-SWAP03-BOX⟨4·21⟩ (lit c4)) ▸
       at 5 2 (Toff204 ∷ Sw03 ∷ []) (wp1180 c4) ▸ done

  b1 : Chain (CCZ234 ∷ Toff423 ∷ CCZ024 ∷ Toff204 ∷ Bx4-21 ∷ Toff204 ∷ Sw03 ∷ CCZ234 ∷ Bx4-21 ∷ Toff402 ∷ CCZ024 ∷ Bx2-431 ∷ Sw03 ∷ []) (CCZ234 ∷ Toff423 ∷ CCZ024 ∷ Toff204 ∷ Bx4-21 ∷ Toff204 ∷ CCZ024 ∷ Bx4-21 ∷ Toff423 ∷ CCZ234 ∷ CCZ024 ∷ Toff204 ∷ Bx4-21 ∷ Sw03 ∷ Toff234 ∷ CCZ234 ∷ Bx4-21 ∷ Sw03 ∷ [])
  b1 = at 6 2 (CCZ024 ∷ Sw03 ∷ []) (sym (wp1157 c4)) ▸
       at 7 2 (Bx4-21 ∷ Sw03 ∷ []) (lem-comm-SWAP03-BOX⟨4·21⟩ (lit c4)) ▸
       at 8 2 (Toff423 ∷ Sw03 ∷ []) (wp1181 c4) ▸
       at 9 2 (CCZ234 ∷ Sw03 ∷ []) (sym (wp1155 c4)) ▸
       at 11 1 (CCZ234 ∷ Toff234 ∷ Bx4-21 ∷ Toff234 ∷ CCZ234 ∷ Bx4-21 ∷ []) (refl) ▸
       at 10 2 (CCZ024 ∷ Sw03 ∷ []) (sym (wp1157 c4)) ▸
       at 11 2 (Toff204 ∷ Sw03 ∷ []) (wp1180 c4) ▸
       at 12 2 (Bx4-21 ∷ Sw03 ∷ []) (lem-comm-SWAP03-BOX⟨4·21⟩ (lit c4)) ▸ done

  b2 : Chain (CCZ234 ∷ Toff423 ∷ CCZ024 ∷ Toff204 ∷ Bx4-21 ∷ Toff204 ∷ CCZ024 ∷ Bx4-21 ∷ Toff423 ∷ CCZ234 ∷ CCZ024 ∷ Toff204 ∷ Bx4-21 ∷ Sw03 ∷ Toff234 ∷ CCZ234 ∷ Bx4-21 ∷ Sw03 ∷ []) (Bx4-2301 ∷ [])
  b2 = at 13 2 (Toff204 ∷ Sw03 ∷ []) (wp1180 c4) ▸
       at 14 2 (CCZ024 ∷ Sw03 ∷ []) (sym (wp1157 c4)) ▸
       at 15 2 (Bx4-21 ∷ Sw03 ∷ []) (lem-comm-SWAP03-BOX⟨4·21⟩ (lit c4)) ▸
       at 16 2 [] (wl0928 (lit c4)) ▸
       at 2 6 (Bx2-401 ∷ []) (refl) ▸
       at 5 6 (Bx2-401 ∷ []) (refl) ▸
       at 0 6 (Bx4-2301 ∷ []) (refl) ▸ done

-- cQ @0412233041: 7 steps
lem-cQ-at0412233041 : Ws → ⟪ (CCZ234 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ CCZ234 ∷ []) ⟫ʷ
lem-cQ-at0412233041 c4 = run b0
  where
  b0 : Chain (CCZ234 ∷ CCZ014 ∷ []) (CCZ014 ∷ CCZ234 ∷ [])
  b0 = at 0 1 (CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ []) (wl0274 (lit c4)) ▸
       at 4 2 (CCZ014 ∷ CS24 ∷ []) (sym (wp0062 c4)) ▸
       at 3 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸
       at 2 2 (CCZ014 ∷ CS34⁻ ∷ []) (sym (wp0063 c4)) ▸
       at 1 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸
       at 0 2 (CCZ014 ∷ CS34 ∷ []) (sym (wp0064 c4)) ▸
       at 1 5 (CCZ234 ∷ []) (sym (wl0274 (lit c4))) ▸ done

-- nat-SWbc @0410213243: 23 steps
lem-nat-SWbc-at0410213243 : Ws → ⟪ (Sw12 ∷ Bx4-0123 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0213 ∷ []) ⟫ʷ
lem-nat-SWbc-at0410213243 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw12 ∷ Bx4-0123 ∷ Sw12 ∷ []) (CCZ024 ∷ Toff402 ∷ CCZ014 ∷ Toff014 ∷ Bx4-03 ∷ Toff014 ∷ Sw12 ∷ CCZ024 ∷ Bx4-03 ∷ Toff401 ∷ CCZ014 ∷ Bx0-423 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff401 ∷ Bx0-423 ∷ Toff401 ∷ CCZ014 ∷ Bx0-423 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw12 ∷ []) (sym (wp0551 c4)) ▸
       at 1 2 (Toff402 ∷ Sw12 ∷ []) (wp0973 c4) ▸
       at 3 1 (CCZ024 ∷ Toff024 ∷ Bx4-03 ∷ Toff024 ∷ CCZ024 ∷ Bx4-03 ∷ []) (refl) ▸
       at 2 2 (CCZ014 ∷ Sw12 ∷ []) (sym (wp0553 c4)) ▸
       at 3 2 (Toff014 ∷ Sw12 ∷ []) (wp0972 c4) ▸
       at 4 2 (Bx4-03 ∷ Sw12 ∷ []) (lem-comm-SWAP12-BOX⟨4·03⟩ (lit c4)) ▸
       at 5 2 (Toff014 ∷ Sw12 ∷ []) (wp0972 c4) ▸ done

  b1 : Chain (CCZ024 ∷ Toff402 ∷ CCZ014 ∷ Toff014 ∷ Bx4-03 ∷ Toff014 ∷ Sw12 ∷ CCZ024 ∷ Bx4-03 ∷ Toff401 ∷ CCZ014 ∷ Bx0-423 ∷ Sw12 ∷ []) (CCZ024 ∷ Toff402 ∷ CCZ014 ∷ Toff014 ∷ Bx4-03 ∷ Toff014 ∷ CCZ014 ∷ Bx4-03 ∷ Toff402 ∷ CCZ024 ∷ CCZ014 ∷ Toff014 ∷ Bx4-03 ∷ Sw12 ∷ Toff024 ∷ CCZ024 ∷ Bx4-03 ∷ Sw12 ∷ [])
  b1 = at 6 2 (CCZ014 ∷ Sw12 ∷ []) (sym (wp0553 c4)) ▸
       at 7 2 (Bx4-03 ∷ Sw12 ∷ []) (lem-comm-SWAP12-BOX⟨4·03⟩ (lit c4)) ▸
       at 8 2 (Toff402 ∷ Sw12 ∷ []) (wp0973 c4) ▸
       at 9 2 (CCZ024 ∷ Sw12 ∷ []) (sym (wp0551 c4)) ▸
       at 11 1 (CCZ024 ∷ Toff024 ∷ Bx4-03 ∷ Toff024 ∷ CCZ024 ∷ Bx4-03 ∷ []) (refl) ▸
       at 10 2 (CCZ014 ∷ Sw12 ∷ []) (sym (wp0553 c4)) ▸
       at 11 2 (Toff014 ∷ Sw12 ∷ []) (wp0972 c4) ▸
       at 12 2 (Bx4-03 ∷ Sw12 ∷ []) (lem-comm-SWAP12-BOX⟨4·03⟩ (lit c4)) ▸ done

  b2 : Chain (CCZ024 ∷ Toff402 ∷ CCZ014 ∷ Toff014 ∷ Bx4-03 ∷ Toff014 ∷ CCZ014 ∷ Bx4-03 ∷ Toff402 ∷ CCZ024 ∷ CCZ014 ∷ Toff014 ∷ Bx4-03 ∷ Sw12 ∷ Toff024 ∷ CCZ024 ∷ Bx4-03 ∷ Sw12 ∷ []) (Bx4-0213 ∷ [])
  b2 = at 13 2 (Toff014 ∷ Sw12 ∷ []) (wp0972 c4) ▸
       at 14 2 (CCZ014 ∷ Sw12 ∷ []) (sym (wp0553 c4)) ▸
       at 15 2 (Bx4-03 ∷ Sw12 ∷ []) (lem-comm-SWAP12-BOX⟨4·03⟩ (lit c4)) ▸
       at 16 2 [] (wl0006 (lit c4)) ▸
       at 2 6 (Bx0-413 ∷ []) (refl) ▸
       at 5 6 (Bx0-413 ∷ []) (refl) ▸
       at 0 6 (Bx4-0213 ∷ []) (refl) ▸ done

-- cQ @04103143: 7 steps
lem-cQ-at04103143 : Ws → ⟪ (CCZ024 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ CCZ024 ∷ []) ⟫ʷ
lem-cQ-at04103143 c4 = run b0
  where
  b0 : Chain (CCZ024 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ024 ∷ [])
  b0 = at 0 1 (CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ []) (wp0296 c4) ▸
       at 4 2 (CCZ134 ∷ CS04 ∷ []) (sym (wp1003 c4)) ▸
       at 3 2 (CCZ134 ∷ CX02 ∷ []) (lem-comm-CX02-CCZ134 (lit c4)) ▸
       at 2 2 (CCZ134 ∷ CS24⁻ ∷ []) (sym (wl1221 (lit c4))) ▸
       at 1 2 (CCZ134 ∷ CX02 ∷ []) (lem-comm-CX02-CCZ134 (lit c4)) ▸
       at 0 2 (CCZ134 ∷ CS24 ∷ []) (sym (wl1220 (lit c4))) ▸
       at 1 5 (CCZ024 ∷ []) (sym (wp0296 c4)) ▸ done

-- cQ @04233042: 7 steps
lem-cQ-at04233042 : Ws → ⟪ (CCZ134 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ CCZ134 ∷ []) ⟫ʷ
lem-cQ-at04233042 c4 = run b0
  where
  b0 : Chain (CCZ134 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ134 ∷ [])
  b0 = at 0 1 (CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ []) (wl0166 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ CS14 ∷ []) (sym (wp0034 c4)) ▸
       at 3 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ CS34⁻ ∷ []) (sym (wp0035 c4)) ▸
       at 1 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 0 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 1 5 (CCZ134 ∷ []) (sym (wl0166 (lit c4))) ▸ done

-- nat-SWbc @0412233041: 23 steps
lem-nat-SWbc-at0412233041 : Ws → ⟪ (Sw03 ∷ Bx4-2301 ∷ Sw03 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2031 ∷ []) ⟫ʷ
lem-nat-SWbc-at0412233041 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw03 ∷ Bx4-2301 ∷ Sw03 ∷ []) (CCZ024 ∷ Toff402 ∷ CCZ234 ∷ Toff234 ∷ Bx4-21 ∷ Toff234 ∷ Sw03 ∷ CCZ024 ∷ Bx4-21 ∷ Toff423 ∷ CCZ234 ∷ Bx2-401 ∷ Sw03 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff423 ∷ Bx2-401 ∷ Toff423 ∷ CCZ234 ∷ Bx2-401 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw03 ∷ []) (sym (wp1157 c4)) ▸
       at 1 2 (Toff402 ∷ Sw03 ∷ []) (wp1158 c4) ▸
       at 3 1 (CCZ024 ∷ Toff204 ∷ Bx4-21 ∷ Toff204 ∷ CCZ024 ∷ Bx4-21 ∷ []) (refl) ▸
       at 2 2 (CCZ234 ∷ Sw03 ∷ []) (sym (wp1155 c4)) ▸
       at 3 2 (Toff234 ∷ Sw03 ∷ []) (wp1156 c4) ▸
       at 4 2 (Bx4-21 ∷ Sw03 ∷ []) (lem-comm-SWAP03-BOX⟨4·21⟩ (lit c4)) ▸
       at 5 2 (Toff234 ∷ Sw03 ∷ []) (wp1156 c4) ▸ done

  b1 : Chain (CCZ024 ∷ Toff402 ∷ CCZ234 ∷ Toff234 ∷ Bx4-21 ∷ Toff234 ∷ Sw03 ∷ CCZ024 ∷ Bx4-21 ∷ Toff423 ∷ CCZ234 ∷ Bx2-401 ∷ Sw03 ∷ []) (CCZ024 ∷ Toff402 ∷ CCZ234 ∷ Toff234 ∷ Bx4-21 ∷ Toff234 ∷ CCZ234 ∷ Bx4-21 ∷ Toff402 ∷ CCZ024 ∷ CCZ234 ∷ Toff234 ∷ Bx4-21 ∷ Sw03 ∷ Toff204 ∷ CCZ024 ∷ Bx4-21 ∷ Sw03 ∷ [])
  b1 = at 6 2 (CCZ234 ∷ Sw03 ∷ []) (sym (wp1155 c4)) ▸
       at 7 2 (Bx4-21 ∷ Sw03 ∷ []) (lem-comm-SWAP03-BOX⟨4·21⟩ (lit c4)) ▸
       at 8 2 (Toff402 ∷ Sw03 ∷ []) (wp1158 c4) ▸
       at 9 2 (CCZ024 ∷ Sw03 ∷ []) (sym (wp1157 c4)) ▸
       at 11 1 (CCZ024 ∷ Toff204 ∷ Bx4-21 ∷ Toff204 ∷ CCZ024 ∷ Bx4-21 ∷ []) (refl) ▸
       at 10 2 (CCZ234 ∷ Sw03 ∷ []) (sym (wp1155 c4)) ▸
       at 11 2 (Toff234 ∷ Sw03 ∷ []) (wp1156 c4) ▸
       at 12 2 (Bx4-21 ∷ Sw03 ∷ []) (lem-comm-SWAP03-BOX⟨4·21⟩ (lit c4)) ▸ done

  b2 : Chain (CCZ024 ∷ Toff402 ∷ CCZ234 ∷ Toff234 ∷ Bx4-21 ∷ Toff234 ∷ CCZ234 ∷ Bx4-21 ∷ Toff402 ∷ CCZ024 ∷ CCZ234 ∷ Toff234 ∷ Bx4-21 ∷ Sw03 ∷ Toff204 ∷ CCZ024 ∷ Bx4-21 ∷ Sw03 ∷ []) (Bx4-2031 ∷ [])
  b2 = at 13 2 (Toff234 ∷ Sw03 ∷ []) (wp1156 c4) ▸
       at 14 2 (CCZ234 ∷ Sw03 ∷ []) (sym (wp1155 c4)) ▸
       at 15 2 (Bx4-21 ∷ Sw03 ∷ []) (lem-comm-SWAP03-BOX⟨4·21⟩ (lit c4)) ▸
       at 16 2 [] (wl0928 (lit c4)) ▸
       at 2 6 (Bx2-431 ∷ []) (refl) ▸
       at 5 6 (Bx2-431 ∷ []) (refl) ▸
       at 0 6 (Bx4-2031 ∷ []) (refl) ▸ done

-- cQ @041041: 7 steps
lem-cQ-at041041 : Ws → ⟪ (CCZ024 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ CCZ024 ∷ []) ⟫ʷ
lem-cQ-at041041 c4 = run b0
  where
  b0 : Chain (CCZ024 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ024 ∷ [])
  b0 = at 0 1 (CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ []) (wp0296 c4) ▸
       at 4 2 (CCZ134 ∷ CS04 ∷ []) (sym (wp1003 c4)) ▸
       at 3 2 (CCZ134 ∷ CX02 ∷ []) (lem-comm-CX02-CCZ134 (lit c4)) ▸
       at 2 2 (CCZ134 ∷ CS24⁻ ∷ []) (sym (wl1221 (lit c4))) ▸
       at 1 2 (CCZ134 ∷ CX02 ∷ []) (lem-comm-CX02-CCZ134 (lit c4)) ▸
       at 0 2 (CCZ134 ∷ CS24 ∷ []) (sym (wl1220 (lit c4))) ▸
       at 1 5 (CCZ024 ∷ []) (sym (wp0296 c4)) ▸ done

-- cQ @0410233241: 7 steps
lem-cQ-at0410233241 : Ws → ⟪ (CCZ034 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ CCZ034 ∷ []) ⟫ʷ
lem-cQ-at0410233241 c4 = run b0
  where
  b0 : Chain (CCZ034 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ034 ∷ [])
  b0 = at 0 1 (CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ []) (wp0231 c4) ▸
       at 4 2 (CCZ124 ∷ CS04 ∷ []) (sym (wp0384 c4)) ▸
       at 3 2 (CCZ124 ∷ CX03 ∷ []) (lem-comm-CX03-CCZ124 (lit c4)) ▸
       at 2 2 (CCZ124 ∷ CS34⁻ ∷ []) (sym (wl1399 (lit c4))) ▸
       at 1 2 (CCZ124 ∷ CX03 ∷ []) (lem-comm-CX03-CCZ124 (lit c4)) ▸
       at 0 2 (CCZ124 ∷ CS34 ∷ []) (sym (wl0471 (lit c4))) ▸
       at 1 5 (CCZ034 ∷ []) (sym (wp0231 c4)) ▸ done

-- cQ @0412213043: 7 steps
lem-cQ-at0412213043 : Ws → ⟪ (CCZ124 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ CCZ124 ∷ []) ⟫ʷ
lem-cQ-at0412213043 c4 = run b0
  where
  b0 : Chain (CCZ124 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ124 ∷ [])
  b0 = at 0 1 (CS14 ∷ CX21 ∷ CS14⁻ ∷ CX21 ∷ CS24 ∷ []) (wl0271 (lit c4)) ▸
       at 4 2 (CCZ034 ∷ CS24 ∷ []) (sym (wp0108 c4)) ▸
       at 3 2 (CCZ034 ∷ CX21 ∷ []) (lem-comm-CX21-CCZ034 (lit c4)) ▸
       at 2 2 (CCZ034 ∷ CS14⁻ ∷ []) (sym (wp0123 c4)) ▸
       at 1 2 (CCZ034 ∷ CX21 ∷ []) (lem-comm-CX21-CCZ034 (lit c4)) ▸
       at 0 2 (CCZ034 ∷ CS14 ∷ []) (sym (wp0106 c4)) ▸
       at 1 5 (CCZ124 ∷ []) (sym (wl0271 (lit c4))) ▸ done

-- cQ @0413213240: 7 steps
lem-cQ-at0413213240 : Ws → ⟪ (CCZ134 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ CCZ134 ∷ []) ⟫ʷ
lem-cQ-at0413213240 c4 = run b0
  where
  b0 : Chain (CCZ134 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ134 ∷ [])
  b0 = at 0 1 (CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ []) (wl0831 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 3 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ CS14⁻ ∷ []) (sym (wp0746 c4)) ▸
       at 1 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸
       at 0 2 (CCZ024 ∷ CS14 ∷ []) (sym (wp0034 c4)) ▸
       at 1 5 (CCZ134 ∷ []) (sym (wl0831 (lit c4))) ▸ done

-- cQ @04233240: 7 steps
lem-cQ-at04233240 : Ws → ⟪ (CCZ134 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ CCZ134 ∷ []) ⟫ʷ
lem-cQ-at04233240 c4 = run b0
  where
  b0 : Chain (CCZ134 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ134 ∷ [])
  b0 = at 0 1 (CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ []) (wl0166 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ CS14 ∷ []) (sym (wp0034 c4)) ▸
       at 3 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ CS34⁻ ∷ []) (sym (wp0035 c4)) ▸
       at 1 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 0 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 1 5 (CCZ134 ∷ []) (sym (wl0166 (lit c4))) ▸ done

-- cQ @0440: 7 steps
lem-cQ-at0440 : Ws → ⟪ (CCZ124 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ CCZ124 ∷ []) ⟫ʷ
lem-cQ-at0440 c4 = run b0
  where
  b0 : Chain (CCZ124 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ124 ∷ [])
  b0 = at 0 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 4 2 (CCZ034 ∷ CS14 ∷ []) (sym (wp0106 c4)) ▸
       at 3 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸
       at 2 2 (CCZ034 ∷ CS24⁻ ∷ []) (sym (wp0107 c4)) ▸
       at 1 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸
       at 0 2 (CCZ034 ∷ CS24 ∷ []) (sym (wp0108 c4)) ▸
       at 1 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸ done

-- cQ @0413203142: 7 steps
lem-cQ-at0413203142 : Ws → ⟪ (CCZ034 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ CCZ034 ∷ []) ⟫ʷ
lem-cQ-at0413203142 c4 = run b0
  where
  b0 : Chain (CCZ034 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ034 ∷ [])
  b0 = at 0 1 (CS04 ∷ CX30 ∷ CS04⁻ ∷ CX30 ∷ CS34 ∷ []) (wp1193 c4) ▸
       at 4 2 (CCZ124 ∷ CS34 ∷ []) (sym (wl0471 (lit c4))) ▸
       at 3 2 (CCZ124 ∷ CX30 ∷ []) (lem-comm-CX30-CCZ124 (lit c4)) ▸
       at 2 2 (CCZ124 ∷ CS04⁻ ∷ []) (sym (wp0318 c4)) ▸
       at 1 2 (CCZ124 ∷ CX30 ∷ []) (lem-comm-CX30-CCZ124 (lit c4)) ▸
       at 0 2 (CCZ124 ∷ CS04 ∷ []) (sym (wp0384 c4)) ▸
       at 1 5 (CCZ034 ∷ []) (sym (wp1193 c4)) ▸ done

-- cQ @02142140: 7 steps
lem-cQ-at02142140 : Ws → ⟪ (CCZ124 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ CCZ124 ∷ []) ⟫ʷ
lem-cQ-at02142140 c4 = run b0
  where
  b0 : Chain (CCZ124 ∷ CCZ023 ∷ []) (CCZ023 ∷ CCZ124 ∷ [])
  b0 = at 0 1 (CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ []) (wl0334 (lit c4)) ▸
       at 4 2 (CCZ023 ∷ CS24 ∷ []) (sym (wp0513 c4)) ▸
       at 3 2 (CCZ023 ∷ CX41 ∷ []) (lem-comm-CX41-CCZ023 (lit c4)) ▸
       at 2 2 (CCZ023 ∷ CS12⁻ ∷ []) (sym (wl0620 (lit c4))) ▸
       at 1 2 (CCZ023 ∷ CX41 ∷ []) (lem-comm-CX41-CCZ023 (lit c4)) ▸
       at 0 2 (CCZ023 ∷ CS12 ∷ []) (sym (wl0621 (lit c4))) ▸
       at 1 5 (CCZ124 ∷ []) (sym (wl0334 (lit c4))) ▸ done

-- cQ @0413213042: 7 steps
lem-cQ-at0413213042 : Ws → ⟪ (CCZ134 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ CCZ134 ∷ []) ⟫ʷ
lem-cQ-at0413213042 c4 = run b0
  where
  b0 : Chain (CCZ134 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ134 ∷ [])
  b0 = at 0 1 (CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ []) (wl0831 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 3 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ CS14⁻ ∷ []) (sym (wp0746 c4)) ▸
       at 1 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸
       at 0 2 (CCZ024 ∷ CS14 ∷ []) (sym (wp0034 c4)) ▸
       at 1 5 (CCZ134 ∷ []) (sym (wl0831 (lit c4))) ▸ done

-- cQ @0412233140: 7 steps
lem-cQ-at0412233140 : Ws → ⟪ (CCZ234 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ CCZ234 ∷ []) ⟫ʷ
lem-cQ-at0412233140 c4 = run b0
  where
  b0 : Chain (CCZ234 ∷ CCZ014 ∷ []) (CCZ014 ∷ CCZ234 ∷ [])
  b0 = at 0 1 (CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ []) (wl0274 (lit c4)) ▸
       at 4 2 (CCZ014 ∷ CS24 ∷ []) (sym (wp0062 c4)) ▸
       at 3 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸
       at 2 2 (CCZ014 ∷ CS34⁻ ∷ []) (sym (wp0063 c4)) ▸
       at 1 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸
       at 0 2 (CCZ014 ∷ CS34 ∷ []) (sym (wp0064 c4)) ▸
       at 1 5 (CCZ234 ∷ []) (sym (wl0274 (lit c4))) ▸ done

-- nat-SWbc @0412233140: 23 steps
lem-nat-SWbc-at0412233140 : Ws → ⟪ (Sw13 ∷ Bx4-2310 ∷ Sw13 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2130 ∷ []) ⟫ʷ
lem-nat-SWbc-at0412233140 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw13 ∷ Bx4-2310 ∷ Sw13 ∷ []) (CCZ124 ∷ Toff412 ∷ CCZ234 ∷ Toff234 ∷ Bx4-20 ∷ Toff234 ∷ Sw13 ∷ CCZ124 ∷ Bx4-20 ∷ Toff423 ∷ CCZ234 ∷ Bx2-410 ∷ Sw13 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff423 ∷ Bx2-410 ∷ Toff423 ∷ CCZ234 ∷ Bx2-410 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw13 ∷ []) (sym (wl1669 (lit c4))) ▸
       at 1 2 (Toff412 ∷ Sw13 ∷ []) (wl1670 (lit c4)) ▸
       at 3 1 (CCZ124 ∷ Toff214 ∷ Bx4-20 ∷ Toff214 ∷ CCZ124 ∷ Bx4-20 ∷ []) (refl) ▸
       at 2 2 (CCZ234 ∷ Sw13 ∷ []) (sym (wl1671 (lit c4))) ▸
       at 3 2 (Toff234 ∷ Sw13 ∷ []) (wl1672 (lit c4)) ▸
       at 4 2 (Bx4-20 ∷ Sw13 ∷ []) (lem-comm-SWAP13-BOX⟨4·20⟩ (lit c4)) ▸
       at 5 2 (Toff234 ∷ Sw13 ∷ []) (wl1672 (lit c4)) ▸ done

  b1 : Chain (CCZ124 ∷ Toff412 ∷ CCZ234 ∷ Toff234 ∷ Bx4-20 ∷ Toff234 ∷ Sw13 ∷ CCZ124 ∷ Bx4-20 ∷ Toff423 ∷ CCZ234 ∷ Bx2-410 ∷ Sw13 ∷ []) (CCZ124 ∷ Toff412 ∷ CCZ234 ∷ Toff234 ∷ Bx4-20 ∷ Toff234 ∷ CCZ234 ∷ Bx4-20 ∷ Toff412 ∷ CCZ124 ∷ CCZ234 ∷ Toff234 ∷ Bx4-20 ∷ Sw13 ∷ Toff214 ∷ CCZ124 ∷ Bx4-20 ∷ Sw13 ∷ [])
  b1 = at 6 2 (CCZ234 ∷ Sw13 ∷ []) (sym (wl1671 (lit c4))) ▸
       at 7 2 (Bx4-20 ∷ Sw13 ∷ []) (lem-comm-SWAP13-BOX⟨4·20⟩ (lit c4)) ▸
       at 8 2 (Toff412 ∷ Sw13 ∷ []) (wl1670 (lit c4)) ▸
       at 9 2 (CCZ124 ∷ Sw13 ∷ []) (sym (wl1669 (lit c4))) ▸
       at 11 1 (CCZ124 ∷ Toff214 ∷ Bx4-20 ∷ Toff214 ∷ CCZ124 ∷ Bx4-20 ∷ []) (refl) ▸
       at 10 2 (CCZ234 ∷ Sw13 ∷ []) (sym (wl1671 (lit c4))) ▸
       at 11 2 (Toff234 ∷ Sw13 ∷ []) (wl1672 (lit c4)) ▸
       at 12 2 (Bx4-20 ∷ Sw13 ∷ []) (lem-comm-SWAP13-BOX⟨4·20⟩ (lit c4)) ▸ done

  b2 : Chain (CCZ124 ∷ Toff412 ∷ CCZ234 ∷ Toff234 ∷ Bx4-20 ∷ Toff234 ∷ CCZ234 ∷ Bx4-20 ∷ Toff412 ∷ CCZ124 ∷ CCZ234 ∷ Toff234 ∷ Bx4-20 ∷ Sw13 ∷ Toff214 ∷ CCZ124 ∷ Bx4-20 ∷ Sw13 ∷ []) (Bx4-2130 ∷ [])
  b2 = at 13 2 (Toff234 ∷ Sw13 ∷ []) (wl1672 (lit c4)) ▸
       at 14 2 (CCZ234 ∷ Sw13 ∷ []) (sym (wl1671 (lit c4))) ▸
       at 15 2 (Bx4-20 ∷ Sw13 ∷ []) (lem-comm-SWAP13-BOX⟨4·20⟩ (lit c4)) ▸
       at 16 2 [] (wl0287 (lit c4)) ▸
       at 2 6 (Bx2-430 ∷ []) (refl) ▸
       at 5 6 (Bx2-430 ∷ []) (refl) ▸
       at 0 6 (Bx4-2130 ∷ []) (refl) ▸ done

-- cQ @0410233142: 7 steps
lem-cQ-at0410233142 : Ws → ⟪ (CCZ034 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ CCZ034 ∷ []) ⟫ʷ
lem-cQ-at0410233142 c4 = run b0
  where
  b0 : Chain (CCZ034 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ034 ∷ [])
  b0 = at 0 1 (CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ []) (wp0231 c4) ▸
       at 4 2 (CCZ124 ∷ CS04 ∷ []) (sym (wp0384 c4)) ▸
       at 3 2 (CCZ124 ∷ CX03 ∷ []) (lem-comm-CX03-CCZ124 (lit c4)) ▸
       at 2 2 (CCZ124 ∷ CS34⁻ ∷ []) (sym (wl1399 (lit c4))) ▸
       at 1 2 (CCZ124 ∷ CX03 ∷ []) (lem-comm-CX03-CCZ124 (lit c4)) ▸
       at 0 2 (CCZ124 ∷ CS34 ∷ []) (sym (wl0471 (lit c4))) ▸
       at 1 5 (CCZ034 ∷ []) (sym (wp0231 c4)) ▸ done

-- cQ @04122140: 7 steps
lem-cQ-at04122140 : Ws → ⟪ (CCZ124 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ CCZ124 ∷ []) ⟫ʷ
lem-cQ-at04122140 c4 = run b0
  where
  b0 : Chain (CCZ124 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ124 ∷ [])
  b0 = at 0 1 (CS14 ∷ CX21 ∷ CS14⁻ ∷ CX21 ∷ CS24 ∷ []) (wl0271 (lit c4)) ▸
       at 4 2 (CCZ034 ∷ CS24 ∷ []) (sym (wp0108 c4)) ▸
       at 3 2 (CCZ034 ∷ CX21 ∷ []) (lem-comm-CX21-CCZ034 (lit c4)) ▸
       at 2 2 (CCZ034 ∷ CS14⁻ ∷ []) (sym (wp0123 c4)) ▸
       at 1 2 (CCZ034 ∷ CX21 ∷ []) (lem-comm-CX21-CCZ034 (lit c4)) ▸
       at 0 2 (CCZ034 ∷ CS14 ∷ []) (sym (wp0106 c4)) ▸
       at 1 5 (CCZ124 ∷ []) (sym (wl0271 (lit c4))) ▸ done

-- nat-SWbc @04122140: 23 steps
lem-nat-SWbc-at04122140 : Ws → ⟪ (Sw13 ∷ Bx4-2130 ∷ Sw13 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2310 ∷ []) ⟫ʷ
lem-nat-SWbc-at04122140 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw13 ∷ Bx4-2130 ∷ Sw13 ∷ []) (CCZ234 ∷ Toff423 ∷ CCZ124 ∷ Toff214 ∷ Bx4-20 ∷ Toff214 ∷ Sw13 ∷ CCZ234 ∷ Bx4-20 ∷ Toff412 ∷ CCZ124 ∷ Bx2-430 ∷ Sw13 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff412 ∷ Bx2-430 ∷ Toff412 ∷ CCZ124 ∷ Bx2-430 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw13 ∷ []) (sym (wl1671 (lit c4))) ▸
       at 1 2 (Toff423 ∷ Sw13 ∷ []) (wl1680 (lit c4)) ▸
       at 3 1 (CCZ234 ∷ Toff234 ∷ Bx4-20 ∷ Toff234 ∷ CCZ234 ∷ Bx4-20 ∷ []) (refl) ▸
       at 2 2 (CCZ124 ∷ Sw13 ∷ []) (sym (wl1669 (lit c4))) ▸
       at 3 2 (Toff214 ∷ Sw13 ∷ []) (wl1681 (lit c4)) ▸
       at 4 2 (Bx4-20 ∷ Sw13 ∷ []) (lem-comm-SWAP13-BOX⟨4·20⟩ (lit c4)) ▸
       at 5 2 (Toff214 ∷ Sw13 ∷ []) (wl1681 (lit c4)) ▸ done

  b1 : Chain (CCZ234 ∷ Toff423 ∷ CCZ124 ∷ Toff214 ∷ Bx4-20 ∷ Toff214 ∷ Sw13 ∷ CCZ234 ∷ Bx4-20 ∷ Toff412 ∷ CCZ124 ∷ Bx2-430 ∷ Sw13 ∷ []) (CCZ234 ∷ Toff423 ∷ CCZ124 ∷ Toff214 ∷ Bx4-20 ∷ Toff214 ∷ CCZ124 ∷ Bx4-20 ∷ Toff423 ∷ CCZ234 ∷ CCZ124 ∷ Toff214 ∷ Bx4-20 ∷ Sw13 ∷ Toff234 ∷ CCZ234 ∷ Bx4-20 ∷ Sw13 ∷ [])
  b1 = at 6 2 (CCZ124 ∷ Sw13 ∷ []) (sym (wl1669 (lit c4))) ▸
       at 7 2 (Bx4-20 ∷ Sw13 ∷ []) (lem-comm-SWAP13-BOX⟨4·20⟩ (lit c4)) ▸
       at 8 2 (Toff423 ∷ Sw13 ∷ []) (wl1680 (lit c4)) ▸
       at 9 2 (CCZ234 ∷ Sw13 ∷ []) (sym (wl1671 (lit c4))) ▸
       at 11 1 (CCZ234 ∷ Toff234 ∷ Bx4-20 ∷ Toff234 ∷ CCZ234 ∷ Bx4-20 ∷ []) (refl) ▸
       at 10 2 (CCZ124 ∷ Sw13 ∷ []) (sym (wl1669 (lit c4))) ▸
       at 11 2 (Toff214 ∷ Sw13 ∷ []) (wl1681 (lit c4)) ▸
       at 12 2 (Bx4-20 ∷ Sw13 ∷ []) (lem-comm-SWAP13-BOX⟨4·20⟩ (lit c4)) ▸ done

  b2 : Chain (CCZ234 ∷ Toff423 ∷ CCZ124 ∷ Toff214 ∷ Bx4-20 ∷ Toff214 ∷ CCZ124 ∷ Bx4-20 ∷ Toff423 ∷ CCZ234 ∷ CCZ124 ∷ Toff214 ∷ Bx4-20 ∷ Sw13 ∷ Toff234 ∷ CCZ234 ∷ Bx4-20 ∷ Sw13 ∷ []) (Bx4-2310 ∷ [])
  b2 = at 13 2 (Toff214 ∷ Sw13 ∷ []) (wl1681 (lit c4)) ▸
       at 14 2 (CCZ124 ∷ Sw13 ∷ []) (sym (wl1669 (lit c4))) ▸
       at 15 2 (Bx4-20 ∷ Sw13 ∷ []) (lem-comm-SWAP13-BOX⟨4·20⟩ (lit c4)) ▸
       at 16 2 [] (wl0287 (lit c4)) ▸
       at 2 6 (Bx2-410 ∷ []) (refl) ▸
       at 5 6 (Bx2-410 ∷ []) (refl) ▸
       at 0 6 (Bx4-2310 ∷ []) (refl) ▸ done

-- cQ @0413203241: 7 steps
lem-cQ-at0413203241 : Ws → ⟪ (CCZ034 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ CCZ034 ∷ []) ⟫ʷ
lem-cQ-at0413203241 c4 = run b0
  where
  b0 : Chain (CCZ034 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ034 ∷ [])
  b0 = at 0 1 (CS04 ∷ CX30 ∷ CS04⁻ ∷ CX30 ∷ CS34 ∷ []) (wp1193 c4) ▸
       at 4 2 (CCZ124 ∷ CS34 ∷ []) (sym (wl0471 (lit c4))) ▸
       at 3 2 (CCZ124 ∷ CX30 ∷ []) (lem-comm-CX30-CCZ124 (lit c4)) ▸
       at 2 2 (CCZ124 ∷ CS04⁻ ∷ []) (sym (wp0318 c4)) ▸
       at 1 2 (CCZ124 ∷ CX30 ∷ []) (lem-comm-CX30-CCZ124 (lit c4)) ▸
       at 0 2 (CCZ124 ∷ CS04 ∷ []) (sym (wp0384 c4)) ▸
       at 1 5 (CCZ034 ∷ []) (sym (wp1193 c4)) ▸ done

-- cQ @04133140: 7 steps
lem-cQ-at04133140 : Ws → ⟪ (CCZ234 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ CCZ234 ∷ []) ⟫ʷ
lem-cQ-at04133140 c4 = run b0
  where
  b0 : Chain (CCZ234 ∷ CCZ014 ∷ []) (CCZ014 ∷ CCZ234 ∷ [])
  b0 = at 0 1 (CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ []) (wl0829 (lit c4)) ▸
       at 4 2 (CCZ014 ∷ CS34 ∷ []) (sym (wp0064 c4)) ▸
       at 3 2 (CCZ014 ∷ CX32 ∷ []) (lem-comm-CX32-CCZ014 (lit c4)) ▸
       at 2 2 (CCZ014 ∷ CS24⁻ ∷ []) (sym (wp0722 c4)) ▸
       at 1 2 (CCZ014 ∷ CX32 ∷ []) (lem-comm-CX32-CCZ014 (lit c4)) ▸
       at 0 2 (CCZ014 ∷ CS24 ∷ []) (sym (wp0062 c4)) ▸
       at 1 5 (CCZ234 ∷ []) (sym (wl0829 (lit c4))) ▸ done

-- nat-SWbc @04133140: 23 steps
lem-nat-SWbc-at04133140 : Ws → ⟪ (Sw12 ∷ Bx4-3210 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3120 ∷ []) ⟫ʷ
lem-nat-SWbc-at04133140 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw12 ∷ Bx4-3210 ∷ Sw12 ∷ []) (CCZ134 ∷ Toff413 ∷ CCZ234 ∷ Toff324 ∷ Bx4-30 ∷ Toff324 ∷ Sw12 ∷ CCZ134 ∷ Bx4-30 ∷ Toff423 ∷ CCZ234 ∷ Bx3-410 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff423 ∷ Bx3-410 ∷ Toff423 ∷ CCZ234 ∷ Bx3-410 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0037 (lit c4))) ▸
       at 1 2 (Toff413 ∷ Sw12 ∷ []) (wl0085 (lit c4)) ▸
       at 3 1 (CCZ134 ∷ Toff314 ∷ Bx4-30 ∷ Toff314 ∷ CCZ134 ∷ Bx4-30 ∷ []) (refl) ▸
       at 2 2 (CCZ234 ∷ Sw12 ∷ []) (sym (wl0044 (lit c4))) ▸
       at 3 2 (Toff324 ∷ Sw12 ∷ []) (wl0045 (lit c4)) ▸
       at 4 2 (Bx4-30 ∷ Sw12 ∷ []) (lem-comm-SWAP12-BOX⟨4·30⟩ (lit c4)) ▸
       at 5 2 (Toff324 ∷ Sw12 ∷ []) (wl0045 (lit c4)) ▸ done

  b1 : Chain (CCZ134 ∷ Toff413 ∷ CCZ234 ∷ Toff324 ∷ Bx4-30 ∷ Toff324 ∷ Sw12 ∷ CCZ134 ∷ Bx4-30 ∷ Toff423 ∷ CCZ234 ∷ Bx3-410 ∷ Sw12 ∷ []) (CCZ134 ∷ Toff413 ∷ CCZ234 ∷ Toff324 ∷ Bx4-30 ∷ Toff324 ∷ CCZ234 ∷ Bx4-30 ∷ Toff413 ∷ CCZ134 ∷ CCZ234 ∷ Toff324 ∷ Bx4-30 ∷ Sw12 ∷ Toff314 ∷ CCZ134 ∷ Bx4-30 ∷ Sw12 ∷ [])
  b1 = at 6 2 (CCZ234 ∷ Sw12 ∷ []) (sym (wl0044 (lit c4))) ▸
       at 7 2 (Bx4-30 ∷ Sw12 ∷ []) (lem-comm-SWAP12-BOX⟨4·30⟩ (lit c4)) ▸
       at 8 2 (Toff413 ∷ Sw12 ∷ []) (wl0085 (lit c4)) ▸
       at 9 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0037 (lit c4))) ▸
       at 11 1 (CCZ134 ∷ Toff314 ∷ Bx4-30 ∷ Toff314 ∷ CCZ134 ∷ Bx4-30 ∷ []) (refl) ▸
       at 10 2 (CCZ234 ∷ Sw12 ∷ []) (sym (wl0044 (lit c4))) ▸
       at 11 2 (Toff324 ∷ Sw12 ∷ []) (wl0045 (lit c4)) ▸
       at 12 2 (Bx4-30 ∷ Sw12 ∷ []) (lem-comm-SWAP12-BOX⟨4·30⟩ (lit c4)) ▸ done

  b2 : Chain (CCZ134 ∷ Toff413 ∷ CCZ234 ∷ Toff324 ∷ Bx4-30 ∷ Toff324 ∷ CCZ234 ∷ Bx4-30 ∷ Toff413 ∷ CCZ134 ∷ CCZ234 ∷ Toff324 ∷ Bx4-30 ∷ Sw12 ∷ Toff314 ∷ CCZ134 ∷ Bx4-30 ∷ Sw12 ∷ []) (Bx4-3120 ∷ [])
  b2 = at 13 2 (Toff324 ∷ Sw12 ∷ []) (wl0045 (lit c4)) ▸
       at 14 2 (CCZ234 ∷ Sw12 ∷ []) (sym (wl0044 (lit c4))) ▸
       at 15 2 (Bx4-30 ∷ Sw12 ∷ []) (lem-comm-SWAP12-BOX⟨4·30⟩ (lit c4)) ▸
       at 16 2 [] (wl0006 (lit c4)) ▸
       at 2 6 (Bx3-420 ∷ []) (refl) ▸
       at 5 6 (Bx3-420 ∷ []) (refl) ▸
       at 0 6 (Bx4-3120 ∷ []) (refl) ▸ done

-- nat-SWbc @0413213240: 23 steps
lem-nat-SWbc-at0413213240 : Ws → ⟪ (Sw12 ∷ Bx4-3120 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3210 ∷ []) ⟫ʷ
lem-nat-SWbc-at0413213240 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw12 ∷ Bx4-3120 ∷ Sw12 ∷ []) (CCZ234 ∷ Toff423 ∷ CCZ134 ∷ Toff314 ∷ Bx4-30 ∷ Toff314 ∷ Sw12 ∷ CCZ234 ∷ Bx4-30 ∷ Toff413 ∷ CCZ134 ∷ Bx3-420 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff413 ∷ Bx3-420 ∷ Toff413 ∷ CCZ134 ∷ Bx3-420 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw12 ∷ []) (sym (wl0044 (lit c4))) ▸
       at 1 2 (Toff423 ∷ Sw12 ∷ []) (wl0084 (lit c4)) ▸
       at 3 1 (CCZ234 ∷ Toff324 ∷ Bx4-30 ∷ Toff324 ∷ CCZ234 ∷ Bx4-30 ∷ []) (refl) ▸
       at 2 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0037 (lit c4))) ▸
       at 3 2 (Toff314 ∷ Sw12 ∷ []) (wl0038 (lit c4)) ▸
       at 4 2 (Bx4-30 ∷ Sw12 ∷ []) (lem-comm-SWAP12-BOX⟨4·30⟩ (lit c4)) ▸
       at 5 2 (Toff314 ∷ Sw12 ∷ []) (wl0038 (lit c4)) ▸ done

  b1 : Chain (CCZ234 ∷ Toff423 ∷ CCZ134 ∷ Toff314 ∷ Bx4-30 ∷ Toff314 ∷ Sw12 ∷ CCZ234 ∷ Bx4-30 ∷ Toff413 ∷ CCZ134 ∷ Bx3-420 ∷ Sw12 ∷ []) (CCZ234 ∷ Toff423 ∷ CCZ134 ∷ Toff314 ∷ Bx4-30 ∷ Toff314 ∷ CCZ134 ∷ Bx4-30 ∷ Toff423 ∷ CCZ234 ∷ CCZ134 ∷ Toff314 ∷ Bx4-30 ∷ Sw12 ∷ Toff324 ∷ CCZ234 ∷ Bx4-30 ∷ Sw12 ∷ [])
  b1 = at 6 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0037 (lit c4))) ▸
       at 7 2 (Bx4-30 ∷ Sw12 ∷ []) (lem-comm-SWAP12-BOX⟨4·30⟩ (lit c4)) ▸
       at 8 2 (Toff423 ∷ Sw12 ∷ []) (wl0084 (lit c4)) ▸
       at 9 2 (CCZ234 ∷ Sw12 ∷ []) (sym (wl0044 (lit c4))) ▸
       at 11 1 (CCZ234 ∷ Toff324 ∷ Bx4-30 ∷ Toff324 ∷ CCZ234 ∷ Bx4-30 ∷ []) (refl) ▸
       at 10 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0037 (lit c4))) ▸
       at 11 2 (Toff314 ∷ Sw12 ∷ []) (wl0038 (lit c4)) ▸
       at 12 2 (Bx4-30 ∷ Sw12 ∷ []) (lem-comm-SWAP12-BOX⟨4·30⟩ (lit c4)) ▸ done

  b2 : Chain (CCZ234 ∷ Toff423 ∷ CCZ134 ∷ Toff314 ∷ Bx4-30 ∷ Toff314 ∷ CCZ134 ∷ Bx4-30 ∷ Toff423 ∷ CCZ234 ∷ CCZ134 ∷ Toff314 ∷ Bx4-30 ∷ Sw12 ∷ Toff324 ∷ CCZ234 ∷ Bx4-30 ∷ Sw12 ∷ []) (Bx4-3210 ∷ [])
  b2 = at 13 2 (Toff314 ∷ Sw12 ∷ []) (wl0038 (lit c4)) ▸
       at 14 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0037 (lit c4))) ▸
       at 15 2 (Bx4-30 ∷ Sw12 ∷ []) (lem-comm-SWAP12-BOX⟨4·30⟩ (lit c4)) ▸
       at 16 2 [] (wl0006 (lit c4)) ▸
       at 2 6 (Bx3-410 ∷ []) (refl) ▸
       at 5 6 (Bx3-410 ∷ []) (refl) ▸
       at 0 6 (Bx4-3210 ∷ []) (refl) ▸ done
