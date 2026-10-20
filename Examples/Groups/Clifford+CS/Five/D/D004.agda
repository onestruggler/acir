{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D004 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0003 ; wl0155 ; wl0156 ; wl0157 ; wl0171 ; wl0172 ; wl0173 ; wl0175 ; wl0199 ; wl0207 ; wl0220 ; wl0225 ; wl0242 ; wl0245 ; wl0256 ; wl0264 ; wl0265 ; wl0266 ; wl0267 ; wl0269 ; wl0270 ; wp0001 ; wp0002 ; wp0003 ; wp0004 ; wp0013 ; wp0021 ; wp0032 ; wp0039 ; wp0046 ; wp0047 ; wp0048 ; wp0075 ; wp0076 ; wp0077 ; wp0081 ; wp0087 ; wp0091 ; wp0092 ; wp0106 ; wp0107 ; wp0108 ; wp0118 ; wp0119 ; wp0120 ; wl0283 ; wl0284 ; wl0285 ; wl0286 ; wl0287 ; wl0288 ; wl0289 ; wl0297 ; wl0306 ; wl0307 ; wl0322 ; wl0323 ; wl0324 ; wl0326 ; wl0334 ; wl0342 ; wl0343 ; wp0136 ; wp0149 ; wp0150 ; wp0151 ; wp0152 ; wp0155 ; wp0156 ; wp0157 ; wp0162 ; wp0175 ; wp0176 ; wp0177 ; wp0178 ; wp0179 ; wp0184 ; wp0185 ; wp0194 ; wp0195 ; wp0196 ; wp0197 ; wp0206 ; wp0207 ; wp0208 ; wp0209 ; wp0213 ; wp0215 ; wl0391 ; wl0392 ; wl0393 ; wl0416 ; wl0417 ; wp0261 ; wp0273 ; wp0274 ; wp0280 ; wl0434 ; wl0435 ; wl0436 ; wl0453 ; wl0454 ; wl0485 ; wl0486 ; wl0490 ; wl0491 ; wl0492 ; wl0495 ; wp0288 ; wp0289 ; wp0303 ; wp0305 ; wp0312 ; wp0313 ; wp0314 ; wp0320 ; wp0337 ; wp0338 ; wp0339 ; wp0340 ; wp0352 ; wp0355 ; wp0356 ; wl0518 ; wl0519 ; wl0520 ; wl0528 ; wl0529 ; wl0530 ; wl0531 ; wl0539 ; wl0540 ; wp0370 ; wp0371 ; wl0006 ; wl0611 ; wl0617 ; wl0620 ; wl0621 ; wl0637 ; wl0638 ; wl0639 ; wl0667 ; wl0669 ; wl0670 ; wp0496 ; wp0513 ; wp0515 ; wp0540 ; wp0543 ; wp0569 ; wp0570 ; wp0582 ; wp0583 ; wp0584 ; wp0585 ; wp0594 ; wp0595 ; wp0596 ; wp0597 ; wl0757 ; wp0679 ; wl0838 ; wl0839 ; wl0840 ; wl0841 ; wl0854 ; wl0855 ; wl0856 ; wl0857 ; wl0864 ; wl0865 ; wp0734 ; wl0930 ; wl0931 ; wl0935 ; wl0936 ; wl0937 ; wl0989 ; wl0990 ; wl1023 ; wl1024 ; wp0820)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-cQ-at021021 ; lem-cQ-at0210213443 ; lem-cQ-at03102132 ; lem-cQ-at032032 ; lem-cQ-at0410213243 ; lem-cQ-at04203243 ; lem-cQ-at13243142 ; lem-cQ-at13243241 ; lem-cQ-at14233142 ; lem-cQ-at14233241 ; lem-sym-ab ; lem-sym-ab-at03102132)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-cQ-at0213243140 ; lem-cQ-at0220)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CX02-CCZ134 ; lem-comm-CX04-CCZ123 ; lem-comm-CX12-CCZ034 ; lem-comm-CX13-CCZ024 ; lem-comm-CX14-CCZ023 ; lem-comm-CX21-CCZ034 ; lem-comm-CX23-CCZ014 ; lem-comm-CX24-CCZ013 ; lem-comm-CX31-CCZ024 ; lem-comm-CX32-CCZ014 ; lem-comm-CX42-CCZ013 ; lem-comm-SWAP02-BOX⟨4·13⟩ ; lem-comm-SWAP13-BOX⟨0·24⟩ ; lem-comm-SWAP13-BOX⟨0·42⟩ ; lem-comm-SWAP14-BOX⟨0·23⟩ ; lem-comm-SWAP14-BOX⟨0·32⟩ ; lem-comm-SWAP23-BOX⟨0·14⟩ ; lem-comm-SWAP24-BOX⟨0·31⟩)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-CX03-CCZ124 ; lem-comm-CX30-CCZ124 ; lem-comm-CX40-CCZ123 ; lem-comm-CX41-CCZ023 ; lem-comm-SWAP02-BOX⟨3·14⟩ ; lem-comm-SWAP12-BOX⟨3·04⟩ ; lem-comm-SWAP14-BOX⟨2·03⟩ ; lem-comm-SWAP14-BOX⟨2·30⟩ ; lem-comm-SWAP14-BOX⟨3·20⟩ ; lem-comm-SWAP23-BOX⟨0·41⟩ ; lem-comm-SWAP24-BOX⟨0·13⟩)

-- cQ: 7 steps
lem-cQ : Ws → ⟪ (CCZ012 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ CCZ012 ∷ []) ⟫ʷ
lem-cQ c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ012 ∷ [])
  b0 = at 0 1 (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) (wl0155 (lit c4)) ▸
       at 4 2 (CCZ034 ∷ CS01 ∷ []) (sym (wp0001 c4)) ▸
       at 3 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸
       at 2 2 (CCZ034 ∷ CS02⁻ ∷ []) (sym (wp0002 c4)) ▸
       at 1 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸
       at 0 2 (CCZ034 ∷ CS02 ∷ []) (sym (wp0003 c4)) ▸
       at 1 5 (CCZ012 ∷ []) (sym (wl0155 (lit c4))) ▸ done

-- cQ @0210243143: 7 steps
lem-cQ-at0210243143 : Ws → ⟪ (CCZ024 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CCZ024 ∷ []) ⟫ʷ
lem-cQ-at0210243143 c4 = run b0
  where
  b0 : Chain (CCZ024 ∷ CCZ123 ∷ []) (CCZ123 ∷ CCZ024 ∷ [])
  b0 = at 0 1 (CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ []) (wp0013 c4) ▸
       at 4 2 (CCZ123 ∷ CS02 ∷ []) (sym (wl0171 (lit c4))) ▸
       at 3 2 (CCZ123 ∷ CX04 ∷ []) (lem-comm-CX04-CCZ123 (lit c4)) ▸
       at 2 2 (CCZ123 ∷ CS24⁻ ∷ []) (sym (wl0172 (lit c4))) ▸
       at 1 2 (CCZ123 ∷ CX04 ∷ []) (lem-comm-CX04-CCZ123 (lit c4)) ▸
       at 0 2 (CCZ123 ∷ CS24 ∷ []) (sym (wl0173 (lit c4))) ▸
       at 1 5 (CCZ024 ∷ []) (sym (wp0013 c4)) ▸ done

-- cQ @243243: 7 steps
lem-cQ-at243243 : Ws → ⟪ (CCZ014 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ CCZ014 ∷ []) ⟫ʷ
lem-cQ-at243243 c4 = run b0
  where
  b0 : Chain (CCZ014 ∷ CCZ023 ∷ []) (CCZ023 ∷ CCZ014 ∷ [])
  b0 = at 0 1 (CS04 ∷ CX14 ∷ CS04⁻ ∷ CX14 ∷ CS01 ∷ []) (wp0046 c4) ▸
       at 4 2 (CCZ023 ∷ CS01 ∷ []) (sym (wl0199 (lit c4))) ▸
       at 3 2 (CCZ023 ∷ CX14 ∷ []) (lem-comm-CX14-CCZ023 (lit c4)) ▸
       at 2 2 (CCZ023 ∷ CS04⁻ ∷ []) (sym (wp0047 c4)) ▸
       at 1 2 (CCZ023 ∷ CX14 ∷ []) (lem-comm-CX14-CCZ023 (lit c4)) ▸
       at 0 2 (CCZ023 ∷ CS04 ∷ []) (sym (wp0048 c4)) ▸
       at 1 5 (CCZ014 ∷ []) (sym (wp0046 c4)) ▸ done

-- cQ @122441: 7 steps
lem-cQ-at122441 : Ws → ⟪ (CCZ024 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ CCZ024 ∷ []) ⟫ʷ
lem-cQ-at122441 c4 = run b0
  where
  b0 : Chain (CCZ024 ∷ CCZ013 ∷ []) (CCZ013 ∷ CCZ024 ∷ [])
  b0 = at 0 1 (CS04 ∷ CX24 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ []) (wp0075 c4) ▸
       at 4 2 (CCZ013 ∷ CS02 ∷ []) (sym (wl0225 (lit c4))) ▸
       at 3 2 (CCZ013 ∷ CX24 ∷ []) (lem-comm-CX24-CCZ013 (lit c4)) ▸
       at 2 2 (CCZ013 ∷ CS04⁻ ∷ []) (sym (wp0076 c4)) ▸
       at 1 2 (CCZ013 ∷ CX24 ∷ []) (lem-comm-CX24-CCZ013 (lit c4)) ▸
       at 0 2 (CCZ013 ∷ CS04 ∷ []) (sym (wp0077 c4)) ▸
       at 1 5 (CCZ024 ∷ []) (sym (wp0075 c4)) ▸ done

-- nat-SWbc: 23 steps
lem-nat-SWbc : Ws → ⟪ (Sw23 ∷ Bx0-1234 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ []) ⟫ʷ
lem-nat-SWbc c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw23 ∷ Bx0-1234 ∷ Sw23 ∷ []) (CCZ013 ∷ Toff013 ∷ CCZ012 ∷ Toff102 ∷ Bx0-14 ∷ Toff102 ∷ Sw23 ∷ CCZ013 ∷ Bx0-14 ∷ Toff012 ∷ CCZ012 ∷ Bx1-034 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff012 ∷ Bx1-034 ∷ Toff012 ∷ CCZ012 ∷ Bx1-034 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw23 ∷ []) (sym (wl0264 (lit c4))) ▸
       at 1 2 (Toff013 ∷ Sw23 ∷ []) (wl0265 (lit c4)) ▸
       at 3 1 (CCZ013 ∷ Toff103 ∷ Bx0-14 ∷ Toff103 ∷ CCZ013 ∷ Bx0-14 ∷ []) (refl) ▸
       at 2 2 (CCZ012 ∷ Sw23 ∷ []) (sym (wl0266 (lit c4))) ▸
       at 3 2 (Toff102 ∷ Sw23 ∷ []) (wl0267 (lit c4)) ▸
       at 4 2 (Bx0-14 ∷ Sw23 ∷ []) (lem-comm-SWAP23-BOX⟨0·14⟩ (lit c4)) ▸
       at 5 2 (Toff102 ∷ Sw23 ∷ []) (wl0267 (lit c4)) ▸ done

  b1 : Chain (CCZ013 ∷ Toff013 ∷ CCZ012 ∷ Toff102 ∷ Bx0-14 ∷ Toff102 ∷ Sw23 ∷ CCZ013 ∷ Bx0-14 ∷ Toff012 ∷ CCZ012 ∷ Bx1-034 ∷ Sw23 ∷ []) (CCZ013 ∷ Toff013 ∷ CCZ012 ∷ Toff102 ∷ Bx0-14 ∷ Toff102 ∷ CCZ012 ∷ Bx0-14 ∷ Toff013 ∷ CCZ013 ∷ CCZ012 ∷ Toff102 ∷ Bx0-14 ∷ Sw23 ∷ Toff103 ∷ CCZ013 ∷ Bx0-14 ∷ Sw23 ∷ [])
  b1 = at 6 2 (CCZ012 ∷ Sw23 ∷ []) (sym (wl0266 (lit c4))) ▸
       at 7 2 (Bx0-14 ∷ Sw23 ∷ []) (lem-comm-SWAP23-BOX⟨0·14⟩ (lit c4)) ▸
       at 8 2 (Toff013 ∷ Sw23 ∷ []) (wl0265 (lit c4)) ▸
       at 9 2 (CCZ013 ∷ Sw23 ∷ []) (sym (wl0264 (lit c4))) ▸
       at 11 1 (CCZ013 ∷ Toff103 ∷ Bx0-14 ∷ Toff103 ∷ CCZ013 ∷ Bx0-14 ∷ []) (refl) ▸
       at 10 2 (CCZ012 ∷ Sw23 ∷ []) (sym (wl0266 (lit c4))) ▸
       at 11 2 (Toff102 ∷ Sw23 ∷ []) (wl0267 (lit c4)) ▸
       at 12 2 (Bx0-14 ∷ Sw23 ∷ []) (lem-comm-SWAP23-BOX⟨0·14⟩ (lit c4)) ▸ done

  b2 : Chain (CCZ013 ∷ Toff013 ∷ CCZ012 ∷ Toff102 ∷ Bx0-14 ∷ Toff102 ∷ CCZ012 ∷ Bx0-14 ∷ Toff013 ∷ CCZ013 ∷ CCZ012 ∷ Toff102 ∷ Bx0-14 ∷ Sw23 ∷ Toff103 ∷ CCZ013 ∷ Bx0-14 ∷ Sw23 ∷ []) (Bx0-1324 ∷ [])
  b2 = at 13 2 (Toff102 ∷ Sw23 ∷ []) (wl0267 (lit c4)) ▸
       at 14 2 (CCZ012 ∷ Sw23 ∷ []) (sym (wl0266 (lit c4))) ▸
       at 15 2 (Bx0-14 ∷ Sw23 ∷ []) (lem-comm-SWAP23-BOX⟨0·14⟩ (lit c4)) ▸
       at 16 2 [] (wl0003 (lit c4)) ▸
       at 2 6 (Bx1-024 ∷ []) (refl) ▸
       at 5 6 (Bx1-024 ∷ []) (refl) ▸
       at 0 6 (Bx0-1324 ∷ []) (refl) ▸ done

-- box-tQ @13243142: 13 steps
lem-box-tQ-at13243142 : Ws → ⟪ (Bx0-3412 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ []) ⟫ʷ
lem-box-tQ-at13243142 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-3412 ∷ []) (CCZ034 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ CCZ013 ∷ Toff301 ∷ CZ23 ∷ Toff301 ∷ CCZ013 ∷ CZ23 ∷ [])
  b0 = at 0 1 (CCZ034 ∷ Toff034 ∷ Bx3-012 ∷ Toff034 ∷ CCZ034 ∷ Bx3-012 ∷ []) (refl) ▸
       at 2 1 (CCZ013 ∷ Toff301 ∷ Bx0-32 ∷ Toff301 ∷ CCZ013 ∷ Bx0-32 ∷ []) (refl) ▸
       at 4 1 (CZ23 ∷ []) (refl) ▸
       at 7 1 (CZ23 ∷ []) (refl) ▸
       at 2 6 (CCZ012 ∷ []) (sym (wl0269 (lit c4))) ▸
       at 5 1 (CCZ013 ∷ Toff301 ∷ Bx0-32 ∷ Toff301 ∷ CCZ013 ∷ Bx0-32 ∷ []) (refl) ▸
       at 7 1 (CZ23 ∷ []) (refl) ▸
       at 10 1 (CZ23 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ034 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ CCZ013 ∷ Toff301 ∷ CZ23 ∷ Toff301 ∷ CCZ013 ∷ CZ23 ∷ []) (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ [])
  b1 = at 5 6 (CCZ012 ∷ []) (sym (wl0269 (lit c4))) ▸
       at 0 2 (Toff034 ∷ CCZ034 ∷ CZ34 ∷ []) (wp0118 c4) ▸
       at 2 2 (CCZ012 ∷ CZ34 ∷ []) (sym (c₃ (CCZ) (CZ))) ▸
       at 1 2 (CCZ012 ∷ CCZ034 ∷ []) (lem-cQ-at13243142 c4) ▸
       at 2 4 (Toff034 ∷ []) (wp0119 c4) ▸ done

-- box-perm-2134: 1 steps
lem-box-perm-2134 : Ws → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ []) ⟫ʷ
lem-box-perm-2134 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ []) (Bx0-2134 ∷ [])
  b0 = at 0 1 (Bx0-2134 ∷ []) (lem-sym-ab c4) ▸ done

-- cQ @1221: 7 steps
lem-cQ-at1221 : Ws → ⟪ (CCZ012 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ CCZ012 ∷ []) ⟫ʷ
lem-cQ-at1221 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ012 ∷ [])
  b0 = at 0 1 (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) (wl0270 (lit c4)) ▸
       at 4 2 (CCZ034 ∷ CS02 ∷ []) (sym (wp0003 c4)) ▸
       at 3 2 (CCZ034 ∷ CX21 ∷ []) (lem-comm-CX21-CCZ034 (lit c4)) ▸
       at 2 2 (CCZ034 ∷ CS01⁻ ∷ []) (sym (wp0120 c4)) ▸
       at 1 2 (CCZ034 ∷ CX21 ∷ []) (lem-comm-CX21-CCZ034 (lit c4)) ▸
       at 0 2 (CCZ034 ∷ CS01 ∷ []) (sym (wp0001 c4)) ▸
       at 1 5 (CCZ012 ∷ []) (sym (wl0270 (lit c4))) ▸ done

-- nat-SWbc @1221: 23 steps
lem-nat-SWbc-at1221 : Ws → ⟪ (Sw13 ∷ Bx0-2134 ∷ Sw13 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2314 ∷ []) ⟫ʷ
lem-nat-SWbc-at1221 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw13 ∷ Bx0-2134 ∷ Sw13 ∷ []) (CCZ023 ∷ Toff023 ∷ CCZ012 ∷ Toff201 ∷ Bx0-24 ∷ Toff201 ∷ Sw13 ∷ CCZ023 ∷ Bx0-24 ∷ Toff012 ∷ CCZ012 ∷ Bx2-034 ∷ Sw13 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff012 ∷ Bx2-034 ∷ Toff012 ∷ CCZ012 ∷ Bx2-034 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw13 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 1 2 (Toff023 ∷ Sw13 ∷ []) (wl0284 (lit c4)) ▸
       at 3 1 (CCZ023 ∷ Toff203 ∷ Bx0-24 ∷ Toff203 ∷ CCZ023 ∷ Bx0-24 ∷ []) (refl) ▸
       at 2 2 (CCZ012 ∷ Sw13 ∷ []) (sym (wl0285 (lit c4))) ▸
       at 3 2 (Toff201 ∷ Sw13 ∷ []) (wl0286 (lit c4)) ▸
       at 4 2 (Bx0-24 ∷ Sw13 ∷ []) (lem-comm-SWAP13-BOX⟨0·24⟩ (lit c4)) ▸
       at 5 2 (Toff201 ∷ Sw13 ∷ []) (wl0286 (lit c4)) ▸ done

  b1 : Chain (CCZ023 ∷ Toff023 ∷ CCZ012 ∷ Toff201 ∷ Bx0-24 ∷ Toff201 ∷ Sw13 ∷ CCZ023 ∷ Bx0-24 ∷ Toff012 ∷ CCZ012 ∷ Bx2-034 ∷ Sw13 ∷ []) (CCZ023 ∷ Toff023 ∷ CCZ012 ∷ Toff201 ∷ Bx0-24 ∷ Toff201 ∷ CCZ012 ∷ Bx0-24 ∷ Toff023 ∷ CCZ023 ∷ CCZ012 ∷ Toff201 ∷ Bx0-24 ∷ Sw13 ∷ Toff203 ∷ CCZ023 ∷ Bx0-24 ∷ Sw13 ∷ [])
  b1 = at 6 2 (CCZ012 ∷ Sw13 ∷ []) (sym (wl0285 (lit c4))) ▸
       at 7 2 (Bx0-24 ∷ Sw13 ∷ []) (lem-comm-SWAP13-BOX⟨0·24⟩ (lit c4)) ▸
       at 8 2 (Toff023 ∷ Sw13 ∷ []) (wl0284 (lit c4)) ▸
       at 9 2 (CCZ023 ∷ Sw13 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 1 (CCZ023 ∷ Toff203 ∷ Bx0-24 ∷ Toff203 ∷ CCZ023 ∷ Bx0-24 ∷ []) (refl) ▸
       at 10 2 (CCZ012 ∷ Sw13 ∷ []) (sym (wl0285 (lit c4))) ▸
       at 11 2 (Toff201 ∷ Sw13 ∷ []) (wl0286 (lit c4)) ▸
       at 12 2 (Bx0-24 ∷ Sw13 ∷ []) (lem-comm-SWAP13-BOX⟨0·24⟩ (lit c4)) ▸ done

  b2 : Chain (CCZ023 ∷ Toff023 ∷ CCZ012 ∷ Toff201 ∷ Bx0-24 ∷ Toff201 ∷ CCZ012 ∷ Bx0-24 ∷ Toff023 ∷ CCZ023 ∷ CCZ012 ∷ Toff201 ∷ Bx0-24 ∷ Sw13 ∷ Toff203 ∷ CCZ023 ∷ Bx0-24 ∷ Sw13 ∷ []) (Bx0-2314 ∷ [])
  b2 = at 13 2 (Toff201 ∷ Sw13 ∷ []) (wl0286 (lit c4)) ▸
       at 14 2 (CCZ012 ∷ Sw13 ∷ []) (sym (wl0285 (lit c4))) ▸
       at 15 2 (Bx0-24 ∷ Sw13 ∷ []) (lem-comm-SWAP13-BOX⟨0·24⟩ (lit c4)) ▸
       at 16 2 [] (wl0287 (lit c4)) ▸
       at 2 6 (Bx2-014 ∷ []) (refl) ▸
       at 5 6 (Bx2-014 ∷ []) (refl) ▸
       at 0 6 (Bx0-2314 ∷ []) (refl) ▸ done

-- box-tQ @13243241: 13 steps
lem-box-tQ-at13243241 : Ws → ⟪ (Bx0-3421 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ []) ⟫ʷ
lem-box-tQ-at13243241 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-3421 ∷ []) (CCZ034 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ CCZ023 ∷ Toff302 ∷ CZ13 ∷ Toff302 ∷ CCZ023 ∷ CZ13 ∷ [])
  b0 = at 0 1 (CCZ034 ∷ Toff034 ∷ Bx3-021 ∷ Toff034 ∷ CCZ034 ∷ Bx3-021 ∷ []) (refl) ▸
       at 2 1 (CCZ023 ∷ Toff302 ∷ Bx0-31 ∷ Toff302 ∷ CCZ023 ∷ Bx0-31 ∷ []) (refl) ▸
       at 4 1 (CZ13 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 2 6 (CCZ012 ∷ []) (sym (wl0288 (lit c4))) ▸
       at 5 1 (CCZ023 ∷ Toff302 ∷ Bx0-31 ∷ Toff302 ∷ CCZ023 ∷ Bx0-31 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 10 1 (CZ13 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ034 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ CCZ023 ∷ Toff302 ∷ CZ13 ∷ Toff302 ∷ CCZ023 ∷ CZ13 ∷ []) (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ [])
  b1 = at 5 6 (CCZ012 ∷ []) (sym (wl0288 (lit c4))) ▸
       at 0 2 (Toff034 ∷ CCZ034 ∷ CZ34 ∷ []) (wp0118 c4) ▸
       at 2 2 (CCZ012 ∷ CZ34 ∷ []) (sym (c₃ (CCZ) (CZ))) ▸
       at 1 2 (CCZ012 ∷ CCZ034 ∷ []) (lem-cQ-at13243241 c4) ▸
       at 2 4 (Toff034 ∷ []) (wp0119 c4) ▸ done

-- cQ @2332: 7 steps
lem-cQ-at2332 : Ws → ⟪ (CCZ013 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ CCZ013 ∷ []) ⟫ʷ
lem-cQ-at2332 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ013 ∷ [])
  b0 = at 0 1 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (wl0289 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ CS01 ∷ []) (sym (wp0039 c4)) ▸
       at 3 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ CS03⁻ ∷ []) (sym (wp0032 c4)) ▸
       at 1 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 0 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸
       at 1 5 (CCZ013 ∷ []) (sym (wl0289 (lit c4))) ▸ done

-- cQ @12243143: 7 steps
lem-cQ-at12243143 : Ws → ⟪ (CCZ024 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ CCZ024 ∷ []) ⟫ʷ
lem-cQ-at12243143 c4 = run b0
  where
  b0 : Chain (CCZ024 ∷ CCZ013 ∷ []) (CCZ013 ∷ CCZ024 ∷ [])
  b0 = at 0 1 (CS04 ∷ CX24 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ []) (wp0075 c4) ▸
       at 4 2 (CCZ013 ∷ CS02 ∷ []) (sym (wl0225 (lit c4))) ▸
       at 3 2 (CCZ013 ∷ CX24 ∷ []) (lem-comm-CX24-CCZ013 (lit c4)) ▸
       at 2 2 (CCZ013 ∷ CS04⁻ ∷ []) (sym (wp0076 c4)) ▸
       at 1 2 (CCZ013 ∷ CX24 ∷ []) (lem-comm-CX24-CCZ013 (lit c4)) ▸
       at 0 2 (CCZ013 ∷ CS04 ∷ []) (sym (wp0077 c4)) ▸
       at 1 5 (CCZ024 ∷ []) (sym (wp0075 c4)) ▸ done

-- nat-SWbc @13243142: 23 steps
lem-nat-SWbc-at13243142 : Ws → ⟪ (Sw14 ∷ Bx0-3412 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3142 ∷ []) ⟫ʷ
lem-nat-SWbc-at13243142 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw14 ∷ Bx0-3412 ∷ Sw14 ∷ []) (CCZ013 ∷ Toff013 ∷ CCZ034 ∷ Toff304 ∷ Bx0-32 ∷ Toff304 ∷ Sw14 ∷ CCZ013 ∷ Bx0-32 ∷ Toff034 ∷ CCZ034 ∷ Bx3-012 ∷ Sw14 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff034 ∷ Bx3-012 ∷ Toff034 ∷ CCZ034 ∷ Bx3-012 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw14 ∷ []) (sym (wp0149 c4)) ▸
       at 1 2 (Toff013 ∷ Sw14 ∷ []) (wp0150 c4) ▸
       at 3 1 (CCZ013 ∷ Toff301 ∷ Bx0-32 ∷ Toff301 ∷ CCZ013 ∷ Bx0-32 ∷ []) (refl) ▸
       at 2 2 (CCZ034 ∷ Sw14 ∷ []) (sym (wp0151 c4)) ▸
       at 3 2 (Toff304 ∷ Sw14 ∷ []) (wp0152 c4) ▸
       at 4 2 (Bx0-32 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨0·32⟩ (lit c4)) ▸
       at 5 2 (Toff304 ∷ Sw14 ∷ []) (wp0152 c4) ▸ done

  b1 : Chain (CCZ013 ∷ Toff013 ∷ CCZ034 ∷ Toff304 ∷ Bx0-32 ∷ Toff304 ∷ Sw14 ∷ CCZ013 ∷ Bx0-32 ∷ Toff034 ∷ CCZ034 ∷ Bx3-012 ∷ Sw14 ∷ []) (CCZ013 ∷ Toff013 ∷ CCZ034 ∷ Toff304 ∷ Bx0-32 ∷ Toff304 ∷ CCZ034 ∷ Bx0-32 ∷ Toff013 ∷ CCZ013 ∷ CCZ034 ∷ Toff304 ∷ Bx0-32 ∷ Sw14 ∷ Toff301 ∷ CCZ013 ∷ Bx0-32 ∷ Sw14 ∷ [])
  b1 = at 6 2 (CCZ034 ∷ Sw14 ∷ []) (sym (wp0151 c4)) ▸
       at 7 2 (Bx0-32 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨0·32⟩ (lit c4)) ▸
       at 8 2 (Toff013 ∷ Sw14 ∷ []) (wp0150 c4) ▸
       at 9 2 (CCZ013 ∷ Sw14 ∷ []) (sym (wp0149 c4)) ▸
       at 11 1 (CCZ013 ∷ Toff301 ∷ Bx0-32 ∷ Toff301 ∷ CCZ013 ∷ Bx0-32 ∷ []) (refl) ▸
       at 10 2 (CCZ034 ∷ Sw14 ∷ []) (sym (wp0151 c4)) ▸
       at 11 2 (Toff304 ∷ Sw14 ∷ []) (wp0152 c4) ▸
       at 12 2 (Bx0-32 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨0·32⟩ (lit c4)) ▸ done

  b2 : Chain (CCZ013 ∷ Toff013 ∷ CCZ034 ∷ Toff304 ∷ Bx0-32 ∷ Toff304 ∷ CCZ034 ∷ Bx0-32 ∷ Toff013 ∷ CCZ013 ∷ CCZ034 ∷ Toff304 ∷ Bx0-32 ∷ Sw14 ∷ Toff301 ∷ CCZ013 ∷ Bx0-32 ∷ Sw14 ∷ []) (Bx0-3142 ∷ [])
  b2 = at 13 2 (Toff304 ∷ Sw14 ∷ []) (wp0152 c4) ▸
       at 14 2 (CCZ034 ∷ Sw14 ∷ []) (sym (wp0151 c4)) ▸
       at 15 2 (Bx0-32 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨0·32⟩ (lit c4)) ▸
       at 16 2 [] (wl0306 (lit c4)) ▸
       at 2 6 (Bx3-042 ∷ []) (refl) ▸
       at 5 6 (Bx3-042 ∷ []) (refl) ▸
       at 0 6 (Bx0-3142 ∷ []) (refl) ▸ done

-- cQ @122331: 7 steps
lem-cQ-at122331 : Ws → ⟪ (CCZ023 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ CCZ023 ∷ []) ⟫ʷ
lem-cQ-at122331 c4 = run b0
  where
  b0 : Chain (CCZ023 ∷ CCZ014 ∷ []) (CCZ014 ∷ CCZ023 ∷ [])
  b0 = at 0 1 (CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ []) (wl0307 (lit c4)) ▸
       at 4 2 (CCZ014 ∷ CS02 ∷ []) (sym (wp0155 c4)) ▸
       at 3 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸
       at 2 2 (CCZ014 ∷ CS03⁻ ∷ []) (sym (wp0156 c4)) ▸
       at 1 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸
       at 0 2 (CCZ014 ∷ CS03 ∷ []) (sym (wp0157 c4)) ▸
       at 1 5 (CCZ023 ∷ []) (sym (wl0307 (lit c4))) ▸ done

-- nat-SWbc @13243241: 23 steps
lem-nat-SWbc-at13243241 : Ws → ⟪ (Sw24 ∷ Bx0-3421 ∷ Sw24 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3241 ∷ []) ⟫ʷ
lem-nat-SWbc-at13243241 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw24 ∷ Bx0-3421 ∷ Sw24 ∷ []) (CCZ023 ∷ Toff023 ∷ CCZ034 ∷ Toff304 ∷ Bx0-31 ∷ Toff304 ∷ Sw24 ∷ CCZ023 ∷ Bx0-31 ∷ Toff034 ∷ CCZ034 ∷ Bx3-021 ∷ Sw24 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff034 ∷ Bx3-021 ∷ Toff034 ∷ CCZ034 ∷ Bx3-021 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw24 ∷ []) (sym (wp0175 c4)) ▸
       at 1 2 (Toff023 ∷ Sw24 ∷ []) (wp0176 c4) ▸
       at 3 1 (CCZ023 ∷ Toff302 ∷ Bx0-31 ∷ Toff302 ∷ CCZ023 ∷ Bx0-31 ∷ []) (refl) ▸
       at 2 2 (CCZ034 ∷ Sw24 ∷ []) (sym (wp0177 c4)) ▸
       at 3 2 (Toff304 ∷ Sw24 ∷ []) (wp0178 c4) ▸
       at 4 2 (Bx0-31 ∷ Sw24 ∷ []) (lem-comm-SWAP24-BOX⟨0·31⟩ (lit c4)) ▸
       at 5 2 (Toff304 ∷ Sw24 ∷ []) (wp0178 c4) ▸ done

  b1 : Chain (CCZ023 ∷ Toff023 ∷ CCZ034 ∷ Toff304 ∷ Bx0-31 ∷ Toff304 ∷ Sw24 ∷ CCZ023 ∷ Bx0-31 ∷ Toff034 ∷ CCZ034 ∷ Bx3-021 ∷ Sw24 ∷ []) (CCZ023 ∷ Toff023 ∷ CCZ034 ∷ Toff304 ∷ Bx0-31 ∷ Toff304 ∷ CCZ034 ∷ Bx0-31 ∷ Toff023 ∷ CCZ023 ∷ CCZ034 ∷ Toff304 ∷ Bx0-31 ∷ Sw24 ∷ Toff302 ∷ CCZ023 ∷ Bx0-31 ∷ Sw24 ∷ [])
  b1 = at 6 2 (CCZ034 ∷ Sw24 ∷ []) (sym (wp0177 c4)) ▸
       at 7 2 (Bx0-31 ∷ Sw24 ∷ []) (lem-comm-SWAP24-BOX⟨0·31⟩ (lit c4)) ▸
       at 8 2 (Toff023 ∷ Sw24 ∷ []) (wp0176 c4) ▸
       at 9 2 (CCZ023 ∷ Sw24 ∷ []) (sym (wp0175 c4)) ▸
       at 11 1 (CCZ023 ∷ Toff302 ∷ Bx0-31 ∷ Toff302 ∷ CCZ023 ∷ Bx0-31 ∷ []) (refl) ▸
       at 10 2 (CCZ034 ∷ Sw24 ∷ []) (sym (wp0177 c4)) ▸
       at 11 2 (Toff304 ∷ Sw24 ∷ []) (wp0178 c4) ▸
       at 12 2 (Bx0-31 ∷ Sw24 ∷ []) (lem-comm-SWAP24-BOX⟨0·31⟩ (lit c4)) ▸ done

  b2 : Chain (CCZ023 ∷ Toff023 ∷ CCZ034 ∷ Toff304 ∷ Bx0-31 ∷ Toff304 ∷ CCZ034 ∷ Bx0-31 ∷ Toff023 ∷ CCZ023 ∷ CCZ034 ∷ Toff304 ∷ Bx0-31 ∷ Sw24 ∷ Toff302 ∷ CCZ023 ∷ Bx0-31 ∷ Sw24 ∷ []) (Bx0-3241 ∷ [])
  b2 = at 13 2 (Toff304 ∷ Sw24 ∷ []) (wp0178 c4) ▸
       at 14 2 (CCZ034 ∷ Sw24 ∷ []) (sym (wp0177 c4)) ▸
       at 15 2 (Bx0-31 ∷ Sw24 ∷ []) (lem-comm-SWAP24-BOX⟨0·31⟩ (lit c4)) ▸
       at 16 2 [] (wl0322 (lit c4)) ▸
       at 2 6 (Bx3-041 ∷ []) (refl) ▸
       at 5 6 (Bx3-041 ∷ []) (refl) ▸
       at 0 6 (Bx0-3241 ∷ []) (refl) ▸ done

-- cQ @132132: 7 steps
lem-cQ-at132132 : Ws → ⟪ (CCZ013 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ CCZ013 ∷ []) ⟫ʷ
lem-cQ-at132132 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ013 ∷ [])
  b0 = at 0 1 (CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ []) (wl0323 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸
       at 3 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ CS01⁻ ∷ []) (sym (wp0179 c4)) ▸
       at 1 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸
       at 0 2 (CCZ024 ∷ CS01 ∷ []) (sym (wp0039 c4)) ▸
       at 1 5 (CCZ013 ∷ []) (sym (wl0323 (lit c4))) ▸ done

-- nat-SWbc @12243143: 23 steps
lem-nat-SWbc-at12243143 : Ws → ⟪ (Sw14 ∷ Bx0-2413 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2143 ∷ []) ⟫ʷ
lem-nat-SWbc-at12243143 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw14 ∷ Bx0-2413 ∷ Sw14 ∷ []) (CCZ012 ∷ Toff012 ∷ CCZ024 ∷ Toff204 ∷ Bx0-23 ∷ Toff204 ∷ Sw14 ∷ CCZ012 ∷ Bx0-23 ∷ Toff024 ∷ CCZ024 ∷ Bx2-013 ∷ Sw14 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff024 ∷ Bx2-013 ∷ Toff024 ∷ CCZ024 ∷ Bx2-013 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw14 ∷ []) (sym (wp0194 c4)) ▸
       at 1 2 (Toff012 ∷ Sw14 ∷ []) (wp0195 c4) ▸
       at 3 1 (CCZ012 ∷ Toff201 ∷ Bx0-23 ∷ Toff201 ∷ CCZ012 ∷ Bx0-23 ∷ []) (refl) ▸
       at 2 2 (CCZ024 ∷ Sw14 ∷ []) (sym (wp0196 c4)) ▸
       at 3 2 (Toff204 ∷ Sw14 ∷ []) (wp0197 c4) ▸
       at 4 2 (Bx0-23 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨0·23⟩ (lit c4)) ▸
       at 5 2 (Toff204 ∷ Sw14 ∷ []) (wp0197 c4) ▸ done

  b1 : Chain (CCZ012 ∷ Toff012 ∷ CCZ024 ∷ Toff204 ∷ Bx0-23 ∷ Toff204 ∷ Sw14 ∷ CCZ012 ∷ Bx0-23 ∷ Toff024 ∷ CCZ024 ∷ Bx2-013 ∷ Sw14 ∷ []) (CCZ012 ∷ Toff012 ∷ CCZ024 ∷ Toff204 ∷ Bx0-23 ∷ Toff204 ∷ CCZ024 ∷ Bx0-23 ∷ Toff012 ∷ CCZ012 ∷ CCZ024 ∷ Toff204 ∷ Bx0-23 ∷ Sw14 ∷ Toff201 ∷ CCZ012 ∷ Bx0-23 ∷ Sw14 ∷ [])
  b1 = at 6 2 (CCZ024 ∷ Sw14 ∷ []) (sym (wp0196 c4)) ▸
       at 7 2 (Bx0-23 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨0·23⟩ (lit c4)) ▸
       at 8 2 (Toff012 ∷ Sw14 ∷ []) (wp0195 c4) ▸
       at 9 2 (CCZ012 ∷ Sw14 ∷ []) (sym (wp0194 c4)) ▸
       at 11 1 (CCZ012 ∷ Toff201 ∷ Bx0-23 ∷ Toff201 ∷ CCZ012 ∷ Bx0-23 ∷ []) (refl) ▸
       at 10 2 (CCZ024 ∷ Sw14 ∷ []) (sym (wp0196 c4)) ▸
       at 11 2 (Toff204 ∷ Sw14 ∷ []) (wp0197 c4) ▸
       at 12 2 (Bx0-23 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨0·23⟩ (lit c4)) ▸ done

  b2 : Chain (CCZ012 ∷ Toff012 ∷ CCZ024 ∷ Toff204 ∷ Bx0-23 ∷ Toff204 ∷ CCZ024 ∷ Bx0-23 ∷ Toff012 ∷ CCZ012 ∷ CCZ024 ∷ Toff204 ∷ Bx0-23 ∷ Sw14 ∷ Toff201 ∷ CCZ012 ∷ Bx0-23 ∷ Sw14 ∷ []) (Bx0-2143 ∷ [])
  b2 = at 13 2 (Toff204 ∷ Sw14 ∷ []) (wp0197 c4) ▸
       at 14 2 (CCZ024 ∷ Sw14 ∷ []) (sym (wp0196 c4)) ▸
       at 15 2 (Bx0-23 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨0·23⟩ (lit c4)) ▸
       at 16 2 [] (wl0306 (lit c4)) ▸
       at 2 6 (Bx2-043 ∷ []) (refl) ▸
       at 5 6 (Bx2-043 ∷ []) (refl) ▸
       at 0 6 (Bx0-2143 ∷ []) (refl) ▸ done

-- box-tQ @14233142: 13 steps
lem-box-tQ-at14233142 : Ws → ⟪ (Bx0-4312 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ []) ⟫ʷ
lem-box-tQ-at14233142 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-4312 ∷ []) (CCZ034 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ CCZ014 ∷ Toff401 ∷ CZ24 ∷ Toff401 ∷ CCZ014 ∷ CZ24 ∷ [])
  b0 = at 0 1 (CCZ034 ∷ Toff034 ∷ Bx4-012 ∷ Toff034 ∷ CCZ034 ∷ Bx4-012 ∷ []) (refl) ▸
       at 2 1 (CCZ014 ∷ Toff401 ∷ Bx0-42 ∷ Toff401 ∷ CCZ014 ∷ Bx0-42 ∷ []) (refl) ▸
       at 4 1 (CZ24 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 2 6 (CCZ012 ∷ []) (sym (wp0136 c4)) ▸
       at 5 1 (CCZ014 ∷ Toff401 ∷ Bx0-42 ∷ Toff401 ∷ CCZ014 ∷ Bx0-42 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 10 1 (CZ24 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ034 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ CCZ014 ∷ Toff401 ∷ CZ24 ∷ Toff401 ∷ CCZ014 ∷ CZ24 ∷ []) (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ [])
  b1 = at 5 6 (CCZ012 ∷ []) (sym (wp0136 c4)) ▸
       at 0 2 (Toff034 ∷ CCZ034 ∷ CZ34 ∷ []) (wp0118 c4) ▸
       at 2 2 (CCZ012 ∷ CZ34 ∷ []) (sym (c₃ (CCZ) (CZ))) ▸
       at 1 2 (CCZ012 ∷ CCZ034 ∷ []) (lem-cQ-at14233142 c4) ▸
       at 2 4 (Toff034 ∷ []) (wp0119 c4) ▸ done

-- nat-SWbc @14233142: 23 steps
lem-nat-SWbc-at14233142 : Ws → ⟪ (Sw13 ∷ Bx0-4312 ∷ Sw13 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4132 ∷ []) ⟫ʷ
lem-nat-SWbc-at14233142 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw13 ∷ Bx0-4312 ∷ Sw13 ∷ []) (CCZ014 ∷ Toff014 ∷ CCZ034 ∷ Toff403 ∷ Bx0-42 ∷ Toff403 ∷ Sw13 ∷ CCZ014 ∷ Bx0-42 ∷ Toff034 ∷ CCZ034 ∷ Bx4-012 ∷ Sw13 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff034 ∷ Bx4-012 ∷ Toff034 ∷ CCZ034 ∷ Bx4-012 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw13 ∷ []) (sym (wp0206 c4)) ▸
       at 1 2 (Toff014 ∷ Sw13 ∷ []) (wp0207 c4) ▸
       at 3 1 (CCZ014 ∷ Toff401 ∷ Bx0-42 ∷ Toff401 ∷ CCZ014 ∷ Bx0-42 ∷ []) (refl) ▸
       at 2 2 (CCZ034 ∷ Sw13 ∷ []) (sym (wp0208 c4)) ▸
       at 3 2 (Toff403 ∷ Sw13 ∷ []) (wp0209 c4) ▸
       at 4 2 (Bx0-42 ∷ Sw13 ∷ []) (lem-comm-SWAP13-BOX⟨0·42⟩ (lit c4)) ▸
       at 5 2 (Toff403 ∷ Sw13 ∷ []) (wp0209 c4) ▸ done

  b1 : Chain (CCZ014 ∷ Toff014 ∷ CCZ034 ∷ Toff403 ∷ Bx0-42 ∷ Toff403 ∷ Sw13 ∷ CCZ014 ∷ Bx0-42 ∷ Toff034 ∷ CCZ034 ∷ Bx4-012 ∷ Sw13 ∷ []) (CCZ014 ∷ Toff014 ∷ CCZ034 ∷ Toff403 ∷ Bx0-42 ∷ Toff403 ∷ CCZ034 ∷ Bx0-42 ∷ Toff014 ∷ CCZ014 ∷ CCZ034 ∷ Toff403 ∷ Bx0-42 ∷ Sw13 ∷ Toff401 ∷ CCZ014 ∷ Bx0-42 ∷ Sw13 ∷ [])
  b1 = at 6 2 (CCZ034 ∷ Sw13 ∷ []) (sym (wp0208 c4)) ▸
       at 7 2 (Bx0-42 ∷ Sw13 ∷ []) (lem-comm-SWAP13-BOX⟨0·42⟩ (lit c4)) ▸
       at 8 2 (Toff014 ∷ Sw13 ∷ []) (wp0207 c4) ▸
       at 9 2 (CCZ014 ∷ Sw13 ∷ []) (sym (wp0206 c4)) ▸
       at 11 1 (CCZ014 ∷ Toff401 ∷ Bx0-42 ∷ Toff401 ∷ CCZ014 ∷ Bx0-42 ∷ []) (refl) ▸
       at 10 2 (CCZ034 ∷ Sw13 ∷ []) (sym (wp0208 c4)) ▸
       at 11 2 (Toff403 ∷ Sw13 ∷ []) (wp0209 c4) ▸
       at 12 2 (Bx0-42 ∷ Sw13 ∷ []) (lem-comm-SWAP13-BOX⟨0·42⟩ (lit c4)) ▸ done

  b2 : Chain (CCZ014 ∷ Toff014 ∷ CCZ034 ∷ Toff403 ∷ Bx0-42 ∷ Toff403 ∷ CCZ034 ∷ Bx0-42 ∷ Toff014 ∷ CCZ014 ∷ CCZ034 ∷ Toff403 ∷ Bx0-42 ∷ Sw13 ∷ Toff401 ∷ CCZ014 ∷ Bx0-42 ∷ Sw13 ∷ []) (Bx0-4132 ∷ [])
  b2 = at 13 2 (Toff403 ∷ Sw13 ∷ []) (wp0209 c4) ▸
       at 14 2 (CCZ034 ∷ Sw13 ∷ []) (sym (wp0208 c4)) ▸
       at 15 2 (Bx0-42 ∷ Sw13 ∷ []) (lem-comm-SWAP13-BOX⟨0·42⟩ (lit c4)) ▸
       at 16 2 [] (wl0287 (lit c4)) ▸
       at 2 6 (Bx4-032 ∷ []) (refl) ▸
       at 5 6 (Bx4-032 ∷ []) (refl) ▸
       at 0 6 (Bx0-4132 ∷ []) (refl) ▸ done

-- tP @14233142: 7 steps
lem-tP-at14233142 : Ws → ⟪ (Toff034 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ Toff034 ∷ []) ⟫ʷ
lem-tP-at14233142 c4 = run b0
  where
  b0 : Chain (Toff034 ∷ Toff012 ∷ []) (Toff012 ∷ Toff034 ∷ [])
  b0 = at 0 1 (K0 ∷ CCZ034 ∷ K0⁻ ∷ []) (sym (wp0004 c4)) ▸
       at 3 1 (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (sym (wl0156 (lit c4))) ▸
       at 2 2 [] (wl0157 (lit c4)) ▸
       at 1 2 (CCZ012 ∷ CCZ034 ∷ []) (lem-cQ-at14233142 c4) ▸
       at 2 0 (K0⁻ ∷ K0 ∷ []) (sym (wl0157 (lit c4))) ▸
       at 0 3 (Toff012 ∷ []) (wl0156 (lit c4)) ▸
       at 1 3 (Toff034 ∷ []) (wp0004 c4) ▸ done

-- cQ @3443: 7 steps
lem-cQ-at3443 : Ws → ⟪ (CCZ012 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ CCZ012 ∷ []) ⟫ʷ
lem-cQ-at3443 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ012 ∷ [])
  b0 = at 0 1 (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) (wl0155 (lit c4)) ▸
       at 4 2 (CCZ034 ∷ CS01 ∷ []) (sym (wp0001 c4)) ▸
       at 3 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸
       at 2 2 (CCZ034 ∷ CS02⁻ ∷ []) (sym (wp0002 c4)) ▸
       at 1 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸
       at 0 2 (CCZ034 ∷ CS02 ∷ []) (sym (wp0003 c4)) ▸
       at 1 5 (CCZ012 ∷ []) (sym (wl0155 (lit c4))) ▸ done

-- cQ @13213442: 7 steps
lem-cQ-at13213442 : Ws → ⟪ (CCZ013 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ CCZ013 ∷ []) ⟫ʷ
lem-cQ-at13213442 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ013 ∷ [])
  b0 = at 0 1 (CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ []) (wl0323 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸
       at 3 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ CS01⁻ ∷ []) (sym (wp0179 c4)) ▸
       at 1 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸
       at 0 2 (CCZ024 ∷ CS01 ∷ []) (sym (wp0039 c4)) ▸
       at 1 5 (CCZ013 ∷ []) (sym (wl0323 (lit c4))) ▸ done

-- cQ @1441: 7 steps
lem-cQ-at1441 : Ws → ⟪ (CCZ024 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ CCZ024 ∷ []) ⟫ʷ
lem-cQ-at1441 c4 = run b0
  where
  b0 : Chain (CCZ024 ∷ CCZ013 ∷ []) (CCZ013 ∷ CCZ024 ∷ [])
  b0 = at 0 1 (CS02 ∷ CX42 ∷ CS02⁻ ∷ CX42 ∷ CS04 ∷ []) (wp0213 c4) ▸
       at 4 2 (CCZ013 ∷ CS04 ∷ []) (sym (wp0077 c4)) ▸
       at 3 2 (CCZ013 ∷ CX42 ∷ []) (lem-comm-CX42-CCZ013 (lit c4)) ▸
       at 2 2 (CCZ013 ∷ CS02⁻ ∷ []) (sym (wl0342 (lit c4))) ▸
       at 1 2 (CCZ013 ∷ CX42 ∷ []) (lem-comm-CX42-CCZ013 (lit c4)) ▸
       at 0 2 (CCZ013 ∷ CS02 ∷ []) (sym (wl0225 (lit c4))) ▸
       at 1 5 (CCZ024 ∷ []) (sym (wp0213 c4)) ▸ done

-- cQ @1331: 7 steps
lem-cQ-at1331 : Ws → ⟪ (CCZ023 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ CCZ023 ∷ []) ⟫ʷ
lem-cQ-at1331 c4 = run b0
  where
  b0 : Chain (CCZ023 ∷ CCZ014 ∷ []) (CCZ014 ∷ CCZ023 ∷ [])
  b0 = at 0 1 (CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ []) (wl0343 (lit c4)) ▸
       at 4 2 (CCZ014 ∷ CS03 ∷ []) (sym (wp0157 c4)) ▸
       at 3 2 (CCZ014 ∷ CX32 ∷ []) (lem-comm-CX32-CCZ014 (lit c4)) ▸
       at 2 2 (CCZ014 ∷ CS02⁻ ∷ []) (sym (wp0215 c4)) ▸
       at 1 2 (CCZ014 ∷ CX32 ∷ []) (lem-comm-CX32-CCZ014 (lit c4)) ▸
       at 0 2 (CCZ014 ∷ CS02 ∷ []) (sym (wp0155 c4)) ▸
       at 1 5 (CCZ023 ∷ []) (sym (wl0343 (lit c4))) ▸ done

-- cQ @2442: 7 steps
lem-cQ-at2442 : Ws → ⟪ (CCZ014 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ CCZ014 ∷ []) ⟫ʷ
lem-cQ-at2442 c4 = run b0
  where
  b0 : Chain (CCZ014 ∷ CCZ023 ∷ []) (CCZ023 ∷ CCZ014 ∷ [])
  b0 = at 0 1 (CS04 ∷ CX14 ∷ CS04⁻ ∷ CX14 ∷ CS01 ∷ []) (wp0046 c4) ▸
       at 4 2 (CCZ023 ∷ CS01 ∷ []) (sym (wl0199 (lit c4))) ▸
       at 3 2 (CCZ023 ∷ CX14 ∷ []) (lem-comm-CX14-CCZ023 (lit c4)) ▸
       at 2 2 (CCZ023 ∷ CS04⁻ ∷ []) (sym (wp0047 c4)) ▸
       at 1 2 (CCZ023 ∷ CX14 ∷ []) (lem-comm-CX14-CCZ023 (lit c4)) ▸
       at 0 2 (CCZ023 ∷ CS04 ∷ []) (sym (wp0048 c4)) ▸
       at 1 5 (CCZ014 ∷ []) (sym (wp0046 c4)) ▸ done

-- cQ @12233441: 7 steps
lem-cQ-at12233441 : Ws → ⟪ (CCZ023 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ CCZ023 ∷ []) ⟫ʷ
lem-cQ-at12233441 c4 = run b0
  where
  b0 : Chain (CCZ023 ∷ CCZ014 ∷ []) (CCZ014 ∷ CCZ023 ∷ [])
  b0 = at 0 1 (CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ []) (wl0307 (lit c4)) ▸
       at 4 2 (CCZ014 ∷ CS02 ∷ []) (sym (wp0155 c4)) ▸
       at 3 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸
       at 2 2 (CCZ014 ∷ CS03⁻ ∷ []) (sym (wp0156 c4)) ▸
       at 1 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸
       at 0 2 (CCZ014 ∷ CS03 ∷ []) (sym (wp0157 c4)) ▸
       at 1 5 (CCZ023 ∷ []) (sym (wl0307 (lit c4))) ▸ done

-- cQ @0110: 7 steps
lem-cQ-at0110 : Ws → ⟪ (CCZ012 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ CCZ012 ∷ []) ⟫ʷ
lem-cQ-at0110 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ012 ∷ [])
  b0 = at 0 1 (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ []) (wl0391 (lit c4)) ▸
       at 4 2 (CCZ134 ∷ CS01 ∷ []) (sym (wp0261 c4)) ▸
       at 3 2 (CCZ134 ∷ CX02 ∷ []) (lem-comm-CX02-CCZ134 (lit c4)) ▸
       at 2 2 (CCZ134 ∷ CS12⁻ ∷ []) (sym (wl0392 (lit c4))) ▸
       at 1 2 (CCZ134 ∷ CX02 ∷ []) (lem-comm-CX02-CCZ134 (lit c4)) ▸
       at 0 2 (CCZ134 ∷ CS12 ∷ []) (sym (wl0393 (lit c4))) ▸
       at 1 5 (CCZ012 ∷ []) (sym (wl0391 (lit c4))) ▸ done

-- cQ @133441: 7 steps
lem-cQ-at133441 : Ws → ⟪ (CCZ023 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ CCZ023 ∷ []) ⟫ʷ
lem-cQ-at133441 c4 = run b0
  where
  b0 : Chain (CCZ023 ∷ CCZ014 ∷ []) (CCZ014 ∷ CCZ023 ∷ [])
  b0 = at 0 1 (CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ []) (wl0343 (lit c4)) ▸
       at 4 2 (CCZ014 ∷ CS03 ∷ []) (sym (wp0157 c4)) ▸
       at 3 2 (CCZ014 ∷ CX32 ∷ []) (lem-comm-CX32-CCZ014 (lit c4)) ▸
       at 2 2 (CCZ014 ∷ CS02⁻ ∷ []) (sym (wp0215 c4)) ▸
       at 1 2 (CCZ014 ∷ CX32 ∷ []) (lem-comm-CX32-CCZ014 (lit c4)) ▸
       at 0 2 (CCZ014 ∷ CS02 ∷ []) (sym (wp0155 c4)) ▸
       at 1 5 (CCZ023 ∷ []) (sym (wl0343 (lit c4))) ▸ done

-- nat-SWbc @133441: 23 steps
lem-nat-SWbc-at133441 : Ws → ⟪ (Sw24 ∷ Bx0-3241 ∷ Sw24 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3421 ∷ []) ⟫ʷ
lem-nat-SWbc-at133441 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw24 ∷ Bx0-3241 ∷ Sw24 ∷ []) (CCZ034 ∷ Toff034 ∷ CCZ023 ∷ Toff302 ∷ Bx0-31 ∷ Toff302 ∷ Sw24 ∷ CCZ034 ∷ Bx0-31 ∷ Toff023 ∷ CCZ023 ∷ Bx3-041 ∷ Sw24 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff023 ∷ Bx3-041 ∷ Toff023 ∷ CCZ023 ∷ Bx3-041 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw24 ∷ []) (sym (wp0177 c4)) ▸
       at 1 2 (Toff034 ∷ Sw24 ∷ []) (wp0273 c4) ▸
       at 3 1 (CCZ034 ∷ Toff304 ∷ Bx0-31 ∷ Toff304 ∷ CCZ034 ∷ Bx0-31 ∷ []) (refl) ▸
       at 2 2 (CCZ023 ∷ Sw24 ∷ []) (sym (wp0175 c4)) ▸
       at 3 2 (Toff302 ∷ Sw24 ∷ []) (wp0274 c4) ▸
       at 4 2 (Bx0-31 ∷ Sw24 ∷ []) (lem-comm-SWAP24-BOX⟨0·31⟩ (lit c4)) ▸
       at 5 2 (Toff302 ∷ Sw24 ∷ []) (wp0274 c4) ▸ done

  b1 : Chain (CCZ034 ∷ Toff034 ∷ CCZ023 ∷ Toff302 ∷ Bx0-31 ∷ Toff302 ∷ Sw24 ∷ CCZ034 ∷ Bx0-31 ∷ Toff023 ∷ CCZ023 ∷ Bx3-041 ∷ Sw24 ∷ []) (CCZ034 ∷ Toff034 ∷ CCZ023 ∷ Toff302 ∷ Bx0-31 ∷ Toff302 ∷ CCZ023 ∷ Bx0-31 ∷ Toff034 ∷ CCZ034 ∷ CCZ023 ∷ Toff302 ∷ Bx0-31 ∷ Sw24 ∷ Toff304 ∷ CCZ034 ∷ Bx0-31 ∷ Sw24 ∷ [])
  b1 = at 6 2 (CCZ023 ∷ Sw24 ∷ []) (sym (wp0175 c4)) ▸
       at 7 2 (Bx0-31 ∷ Sw24 ∷ []) (lem-comm-SWAP24-BOX⟨0·31⟩ (lit c4)) ▸
       at 8 2 (Toff034 ∷ Sw24 ∷ []) (wp0273 c4) ▸
       at 9 2 (CCZ034 ∷ Sw24 ∷ []) (sym (wp0177 c4)) ▸
       at 11 1 (CCZ034 ∷ Toff304 ∷ Bx0-31 ∷ Toff304 ∷ CCZ034 ∷ Bx0-31 ∷ []) (refl) ▸
       at 10 2 (CCZ023 ∷ Sw24 ∷ []) (sym (wp0175 c4)) ▸
       at 11 2 (Toff302 ∷ Sw24 ∷ []) (wp0274 c4) ▸
       at 12 2 (Bx0-31 ∷ Sw24 ∷ []) (lem-comm-SWAP24-BOX⟨0·31⟩ (lit c4)) ▸ done

  b2 : Chain (CCZ034 ∷ Toff034 ∷ CCZ023 ∷ Toff302 ∷ Bx0-31 ∷ Toff302 ∷ CCZ023 ∷ Bx0-31 ∷ Toff034 ∷ CCZ034 ∷ CCZ023 ∷ Toff302 ∷ Bx0-31 ∷ Sw24 ∷ Toff304 ∷ CCZ034 ∷ Bx0-31 ∷ Sw24 ∷ []) (Bx0-3421 ∷ [])
  b2 = at 13 2 (Toff302 ∷ Sw24 ∷ []) (wp0274 c4) ▸
       at 14 2 (CCZ023 ∷ Sw24 ∷ []) (sym (wp0175 c4)) ▸
       at 15 2 (Bx0-31 ∷ Sw24 ∷ []) (lem-comm-SWAP24-BOX⟨0·31⟩ (lit c4)) ▸
       at 16 2 [] (wl0322 (lit c4)) ▸
       at 2 6 (Bx3-021 ∷ []) (refl) ▸
       at 5 6 (Bx3-021 ∷ []) (refl) ▸
       at 0 6 (Bx0-3421 ∷ []) (refl) ▸ done

-- tP @13243241: 7 steps
lem-tP-at13243241 : Ws → ⟪ (Toff034 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ Toff034 ∷ []) ⟫ʷ
lem-tP-at13243241 c4 = run b0
  where
  b0 : Chain (Toff034 ∷ Toff012 ∷ []) (Toff012 ∷ Toff034 ∷ [])
  b0 = at 0 1 (K0 ∷ CCZ034 ∷ K0⁻ ∷ []) (sym (wp0004 c4)) ▸
       at 3 1 (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (sym (wl0156 (lit c4))) ▸
       at 2 2 [] (wl0157 (lit c4)) ▸
       at 1 2 (CCZ012 ∷ CCZ034 ∷ []) (lem-cQ-at13243241 c4) ▸
       at 2 0 (K0⁻ ∷ K0 ∷ []) (sym (wl0157 (lit c4))) ▸
       at 0 3 (Toff012 ∷ []) (wl0156 (lit c4)) ▸
       at 1 3 (Toff034 ∷ []) (wp0004 c4) ▸ done

-- cQ @233442: 7 steps
lem-cQ-at233442 : Ws → ⟪ (CCZ013 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ CCZ013 ∷ []) ⟫ʷ
lem-cQ-at233442 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ013 ∷ [])
  b0 = at 0 1 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (wl0289 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ CS01 ∷ []) (sym (wp0039 c4)) ▸
       at 3 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ CS03⁻ ∷ []) (sym (wp0032 c4)) ▸
       at 1 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 0 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸
       at 1 5 (CCZ013 ∷ []) (sym (wl0289 (lit c4))) ▸ done

-- tP @021021: 7 steps
lem-tP-at021021 : Ws → ⟪ (Toff201 ∷ Toff234 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ Toff201 ∷ []) ⟫ʷ
lem-tP-at021021 c4 = run b0
  where
  b0 : Chain (Toff201 ∷ Toff234 ∷ []) (Toff234 ∷ Toff201 ∷ [])
  b0 = at 0 1 (K2 ∷ CCZ012 ∷ K2⁻ ∷ []) (sym (wl0416 (lit c4))) ▸
       at 3 1 (K2 ∷ CCZ234 ∷ K2⁻ ∷ []) (sym (wl0417 (lit c4))) ▸
       at 2 2 [] (wl0175 (lit c4)) ▸
       at 1 2 (CCZ234 ∷ CCZ012 ∷ []) (lem-cQ-at021021 c4) ▸
       at 2 0 (K2⁻ ∷ K2 ∷ []) (sym (wl0175 (lit c4))) ▸
       at 0 3 (Toff234 ∷ []) (wl0417 (lit c4)) ▸
       at 1 3 (Toff201 ∷ []) (wl0416 (lit c4)) ▸ done

-- nat-SWbc @13213442: 23 steps
lem-nat-SWbc-at13213442 : Ws → ⟪ (Sw14 ∷ Bx0-3142 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3412 ∷ []) ⟫ʷ
lem-nat-SWbc-at13213442 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw14 ∷ Bx0-3142 ∷ Sw14 ∷ []) (CCZ034 ∷ Toff034 ∷ CCZ013 ∷ Toff301 ∷ Bx0-32 ∷ Toff301 ∷ Sw14 ∷ CCZ034 ∷ Bx0-32 ∷ Toff013 ∷ CCZ013 ∷ Bx3-042 ∷ Sw14 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff013 ∷ Bx3-042 ∷ Toff013 ∷ CCZ013 ∷ Bx3-042 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw14 ∷ []) (sym (wp0151 c4)) ▸
       at 1 2 (Toff034 ∷ Sw14 ∷ []) (wp0288 c4) ▸
       at 3 1 (CCZ034 ∷ Toff304 ∷ Bx0-32 ∷ Toff304 ∷ CCZ034 ∷ Bx0-32 ∷ []) (refl) ▸
       at 2 2 (CCZ013 ∷ Sw14 ∷ []) (sym (wp0149 c4)) ▸
       at 3 2 (Toff301 ∷ Sw14 ∷ []) (wp0289 c4) ▸
       at 4 2 (Bx0-32 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨0·32⟩ (lit c4)) ▸
       at 5 2 (Toff301 ∷ Sw14 ∷ []) (wp0289 c4) ▸ done

  b1 : Chain (CCZ034 ∷ Toff034 ∷ CCZ013 ∷ Toff301 ∷ Bx0-32 ∷ Toff301 ∷ Sw14 ∷ CCZ034 ∷ Bx0-32 ∷ Toff013 ∷ CCZ013 ∷ Bx3-042 ∷ Sw14 ∷ []) (CCZ034 ∷ Toff034 ∷ CCZ013 ∷ Toff301 ∷ Bx0-32 ∷ Toff301 ∷ CCZ013 ∷ Bx0-32 ∷ Toff034 ∷ CCZ034 ∷ CCZ013 ∷ Toff301 ∷ Bx0-32 ∷ Sw14 ∷ Toff304 ∷ CCZ034 ∷ Bx0-32 ∷ Sw14 ∷ [])
  b1 = at 6 2 (CCZ013 ∷ Sw14 ∷ []) (sym (wp0149 c4)) ▸
       at 7 2 (Bx0-32 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨0·32⟩ (lit c4)) ▸
       at 8 2 (Toff034 ∷ Sw14 ∷ []) (wp0288 c4) ▸
       at 9 2 (CCZ034 ∷ Sw14 ∷ []) (sym (wp0151 c4)) ▸
       at 11 1 (CCZ034 ∷ Toff304 ∷ Bx0-32 ∷ Toff304 ∷ CCZ034 ∷ Bx0-32 ∷ []) (refl) ▸
       at 10 2 (CCZ013 ∷ Sw14 ∷ []) (sym (wp0149 c4)) ▸
       at 11 2 (Toff301 ∷ Sw14 ∷ []) (wp0289 c4) ▸
       at 12 2 (Bx0-32 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨0·32⟩ (lit c4)) ▸ done

  b2 : Chain (CCZ034 ∷ Toff034 ∷ CCZ013 ∷ Toff301 ∷ Bx0-32 ∷ Toff301 ∷ CCZ013 ∷ Bx0-32 ∷ Toff034 ∷ CCZ034 ∷ CCZ013 ∷ Toff301 ∷ Bx0-32 ∷ Sw14 ∷ Toff304 ∷ CCZ034 ∷ Bx0-32 ∷ Sw14 ∷ []) (Bx0-3412 ∷ [])
  b2 = at 13 2 (Toff301 ∷ Sw14 ∷ []) (wp0289 c4) ▸
       at 14 2 (CCZ013 ∷ Sw14 ∷ []) (sym (wp0149 c4)) ▸
       at 15 2 (Bx0-32 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨0·32⟩ (lit c4)) ▸
       at 16 2 [] (wl0306 (lit c4)) ▸
       at 2 6 (Bx3-012 ∷ []) (refl) ▸
       at 5 6 (Bx3-012 ∷ []) (refl) ▸
       at 0 6 (Bx0-3412 ∷ []) (refl) ▸ done

-- tP @13243142: 7 steps
lem-tP-at13243142 : Ws → ⟪ (Toff034 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ Toff034 ∷ []) ⟫ʷ
lem-tP-at13243142 c4 = run b0
  where
  b0 : Chain (Toff034 ∷ Toff012 ∷ []) (Toff012 ∷ Toff034 ∷ [])
  b0 = at 0 1 (K0 ∷ CCZ034 ∷ K0⁻ ∷ []) (sym (wp0004 c4)) ▸
       at 3 1 (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (sym (wl0156 (lit c4))) ▸
       at 2 2 [] (wl0157 (lit c4)) ▸
       at 1 2 (CCZ012 ∷ CCZ034 ∷ []) (lem-cQ-at13243142 c4) ▸
       at 2 0 (K0⁻ ∷ K0 ∷ []) (sym (wl0157 (lit c4))) ▸
       at 0 3 (Toff012 ∷ []) (wl0156 (lit c4)) ▸
       at 1 3 (Toff034 ∷ []) (wp0004 c4) ▸ done

-- tP @03102132: 7 steps
lem-tP-at03102132 : Ws → ⟪ (Toff301 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ Toff301 ∷ []) ⟫ʷ
lem-tP-at03102132 c4 = run b0
  where
  b0 : Chain (Toff301 ∷ Toff324 ∷ []) (Toff324 ∷ Toff301 ∷ [])
  b0 = at 0 1 (K3 ∷ CCZ013 ∷ K3⁻ ∷ []) (sym (wl0434 (lit c4))) ▸
       at 3 1 (K3 ∷ CCZ234 ∷ K3⁻ ∷ []) (sym (wl0435 (lit c4))) ▸
       at 2 2 [] (wl0436 (lit c4)) ▸
       at 1 2 (CCZ234 ∷ CCZ013 ∷ []) (lem-cQ-at03102132 c4) ▸
       at 2 0 (K3⁻ ∷ K3 ∷ []) (sym (wl0436 (lit c4))) ▸
       at 0 3 (Toff324 ∷ []) (wl0435 (lit c4)) ▸
       at 1 3 (Toff301 ∷ []) (wl0434 (lit c4)) ▸ done

-- tP @0410213243: 7 steps
lem-tP-at0410213243 : Ws → ⟪ (Toff401 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ Toff401 ∷ []) ⟫ʷ
lem-tP-at0410213243 c4 = run b0
  where
  b0 : Chain (Toff401 ∷ Toff423 ∷ []) (Toff423 ∷ Toff401 ∷ [])
  b0 = at 0 1 (K4 ∷ CCZ014 ∷ K4⁻ ∷ []) (sym (wp0303 c4)) ▸
       at 3 1 (K4 ∷ CCZ234 ∷ K4⁻ ∷ []) (sym (wl0453 (lit c4))) ▸
       at 2 2 [] (wl0454 (lit c4)) ▸
       at 1 2 (CCZ234 ∷ CCZ014 ∷ []) (lem-cQ-at0410213243 c4) ▸
       at 2 0 (K4⁻ ∷ K4 ∷ []) (sym (wl0454 (lit c4))) ▸
       at 0 3 (Toff423 ∷ []) (wl0453 (lit c4)) ▸
       at 1 3 (Toff401 ∷ []) (wp0303 c4) ▸ done

-- cQ @043043: 7 steps
lem-cQ-at043043 : Ws → ⟪ (CCZ124 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ CCZ124 ∷ []) ⟫ʷ
lem-cQ-at043043 c4 = run b0
  where
  b0 : Chain (CCZ124 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ124 ∷ [])
  b0 = at 0 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 4 2 (CCZ034 ∷ CS14 ∷ []) (sym (wp0106 c4)) ▸
       at 3 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸
       at 2 2 (CCZ034 ∷ CS24⁻ ∷ []) (sym (wp0107 c4)) ▸
       at 1 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸
       at 0 2 (CCZ034 ∷ CS24 ∷ []) (sym (wp0108 c4)) ▸
       at 1 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸ done

-- cQ @0330: 7 steps
lem-cQ-at0330 : Ws → ⟪ (CCZ123 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ CCZ123 ∷ []) ⟫ʷ
lem-cQ-at0330 c4 = run b0
  where
  b0 : Chain (CCZ123 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ123 ∷ [])
  b0 = at 0 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0207 (lit c4)) ▸
       at 4 2 (CCZ034 ∷ CS13 ∷ []) (sym (wp0312 c4)) ▸
       at 3 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸
       at 2 2 (CCZ034 ∷ CS23⁻ ∷ []) (sym (wp0313 c4)) ▸
       at 1 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸
       at 0 2 (CCZ034 ∷ CS23 ∷ []) (sym (wp0314 c4)) ▸
       at 1 5 (CCZ123 ∷ []) (sym (wl0207 (lit c4))) ▸ done

-- nat-SWbc @043043: 23 steps
lem-nat-SWbc-at043043 : Ws → ⟪ (Sw02 ∷ Bx4-1203 ∷ Sw02 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1023 ∷ []) ⟫ʷ
lem-nat-SWbc-at043043 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw02 ∷ Bx4-1203 ∷ Sw02 ∷ []) (CCZ014 ∷ Toff401 ∷ CCZ124 ∷ Toff124 ∷ Bx4-13 ∷ Toff124 ∷ Sw02 ∷ CCZ014 ∷ Bx4-13 ∷ Toff412 ∷ CCZ124 ∷ Bx1-403 ∷ Sw02 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff412 ∷ Bx1-403 ∷ Toff412 ∷ CCZ124 ∷ Bx1-403 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw02 ∷ []) (sym (wp0337 c4)) ▸
       at 1 2 (Toff401 ∷ Sw02 ∷ []) (wp0338 c4) ▸
       at 3 1 (CCZ014 ∷ Toff104 ∷ Bx4-13 ∷ Toff104 ∷ CCZ014 ∷ Bx4-13 ∷ []) (refl) ▸
       at 2 2 (CCZ124 ∷ Sw02 ∷ []) (sym (wp0339 c4)) ▸
       at 3 2 (Toff124 ∷ Sw02 ∷ []) (wp0340 c4) ▸
       at 4 2 (Bx4-13 ∷ Sw02 ∷ []) (lem-comm-SWAP02-BOX⟨4·13⟩ (lit c4)) ▸
       at 5 2 (Toff124 ∷ Sw02 ∷ []) (wp0340 c4) ▸ done

  b1 : Chain (CCZ014 ∷ Toff401 ∷ CCZ124 ∷ Toff124 ∷ Bx4-13 ∷ Toff124 ∷ Sw02 ∷ CCZ014 ∷ Bx4-13 ∷ Toff412 ∷ CCZ124 ∷ Bx1-403 ∷ Sw02 ∷ []) (CCZ014 ∷ Toff401 ∷ CCZ124 ∷ Toff124 ∷ Bx4-13 ∷ Toff124 ∷ CCZ124 ∷ Bx4-13 ∷ Toff401 ∷ CCZ014 ∷ CCZ124 ∷ Toff124 ∷ Bx4-13 ∷ Sw02 ∷ Toff104 ∷ CCZ014 ∷ Bx4-13 ∷ Sw02 ∷ [])
  b1 = at 6 2 (CCZ124 ∷ Sw02 ∷ []) (sym (wp0339 c4)) ▸
       at 7 2 (Bx4-13 ∷ Sw02 ∷ []) (lem-comm-SWAP02-BOX⟨4·13⟩ (lit c4)) ▸
       at 8 2 (Toff401 ∷ Sw02 ∷ []) (wp0338 c4) ▸
       at 9 2 (CCZ014 ∷ Sw02 ∷ []) (sym (wp0337 c4)) ▸
       at 11 1 (CCZ014 ∷ Toff104 ∷ Bx4-13 ∷ Toff104 ∷ CCZ014 ∷ Bx4-13 ∷ []) (refl) ▸
       at 10 2 (CCZ124 ∷ Sw02 ∷ []) (sym (wp0339 c4)) ▸
       at 11 2 (Toff124 ∷ Sw02 ∷ []) (wp0340 c4) ▸
       at 12 2 (Bx4-13 ∷ Sw02 ∷ []) (lem-comm-SWAP02-BOX⟨4·13⟩ (lit c4)) ▸ done

  b2 : Chain (CCZ014 ∷ Toff401 ∷ CCZ124 ∷ Toff124 ∷ Bx4-13 ∷ Toff124 ∷ CCZ124 ∷ Bx4-13 ∷ Toff401 ∷ CCZ014 ∷ CCZ124 ∷ Toff124 ∷ Bx4-13 ∷ Sw02 ∷ Toff104 ∷ CCZ014 ∷ Bx4-13 ∷ Sw02 ∷ []) (Bx4-1023 ∷ [])
  b2 = at 13 2 (Toff124 ∷ Sw02 ∷ []) (wp0340 c4) ▸
       at 14 2 (CCZ124 ∷ Sw02 ∷ []) (sym (wp0339 c4)) ▸
       at 15 2 (Bx4-13 ∷ Sw02 ∷ []) (lem-comm-SWAP02-BOX⟨4·13⟩ (lit c4)) ▸
       at 16 2 [] (wl0485 (lit c4)) ▸
       at 2 6 (Bx1-423 ∷ []) (refl) ▸
       at 5 6 (Bx1-423 ∷ []) (refl) ▸
       at 0 6 (Bx4-1023 ∷ []) (refl) ▸ done

-- tP @04203243: 7 steps
lem-tP-at04203243 : Ws → ⟪ (Toff401 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ Toff401 ∷ []) ⟫ʷ
lem-tP-at04203243 c4 = run b0
  where
  b0 : Chain (Toff401 ∷ Toff423 ∷ []) (Toff423 ∷ Toff401 ∷ [])
  b0 = at 0 1 (K4 ∷ CCZ014 ∷ K4⁻ ∷ []) (sym (wp0303 c4)) ▸
       at 3 1 (K4 ∷ CCZ234 ∷ K4⁻ ∷ []) (sym (wl0453 (lit c4))) ▸
       at 2 2 [] (wl0454 (lit c4)) ▸
       at 1 2 (CCZ234 ∷ CCZ014 ∷ []) (lem-cQ-at04203243 c4) ▸
       at 2 0 (K4⁻ ∷ K4 ∷ []) (sym (wl0454 (lit c4))) ▸
       at 0 3 (Toff423 ∷ []) (wl0453 (lit c4)) ▸
       at 1 3 (Toff401 ∷ []) (wp0303 c4) ▸ done

-- cQ @0310243142: 7 steps
lem-cQ-at0310243142 : Ws → ⟪ (CCZ034 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CCZ034 ∷ []) ⟫ʷ
lem-cQ-at0310243142 c4 = run b0
  where
  b0 : Chain (CCZ034 ∷ CCZ123 ∷ []) (CCZ123 ∷ CCZ034 ∷ [])
  b0 = at 0 1 (CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ []) (wp0352 c4) ▸
       at 4 2 (CCZ123 ∷ CS03 ∷ []) (sym (wl0490 (lit c4))) ▸
       at 3 2 (CCZ123 ∷ CX04 ∷ []) (lem-comm-CX04-CCZ123 (lit c4)) ▸
       at 2 2 (CCZ123 ∷ CS34⁻ ∷ []) (sym (wl0491 (lit c4))) ▸
       at 1 2 (CCZ123 ∷ CX04 ∷ []) (lem-comm-CX04-CCZ123 (lit c4)) ▸
       at 0 2 (CCZ123 ∷ CS34 ∷ []) (sym (wl0492 (lit c4))) ▸
       at 1 5 (CCZ034 ∷ []) (sym (wp0352 c4)) ▸ done

-- box-tQ @0410213243: 13 steps
lem-box-tQ-at0410213243 : Ws → ⟪ (Bx4-0123 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ []) ⟫ʷ
lem-box-tQ-at0410213243 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx4-0123 ∷ []) (CCZ014 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ014 ∷ CCZ024 ∷ Toff024 ∷ CZ03 ∷ Toff024 ∷ CCZ024 ∷ CZ03 ∷ [])
  b0 = at 0 1 (CCZ014 ∷ Toff401 ∷ Bx0-423 ∷ Toff401 ∷ CCZ014 ∷ Bx0-423 ∷ []) (refl) ▸
       at 2 1 (CCZ024 ∷ Toff024 ∷ Bx4-03 ∷ Toff024 ∷ CCZ024 ∷ Bx4-03 ∷ []) (refl) ▸
       at 4 1 (CZ03 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 2 6 (CCZ234 ∷ []) (wp0305 c4) ▸
       at 5 1 (CCZ024 ∷ Toff024 ∷ Bx4-03 ∷ Toff024 ∷ CCZ024 ∷ Bx4-03 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 10 1 (CZ03 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ014 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ014 ∷ CCZ024 ∷ Toff024 ∷ CZ03 ∷ Toff024 ∷ CCZ024 ∷ CZ03 ∷ []) (Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ [])
  b1 = at 5 6 (CCZ234 ∷ []) (wp0305 c4) ▸
       at 0 2 (Toff401 ∷ CCZ014 ∷ CZ01 ∷ []) (wp0355 c4) ▸
       at 2 2 (CCZ234 ∷ CZ01 ∷ []) (c₂ (CZ) (CCZ)) ▸
       at 1 2 (CCZ234 ∷ CCZ014 ∷ []) (lem-cQ-at0410213243 c4) ▸
       at 2 4 (Toff401 ∷ []) (wp0356 c4) ▸ done

-- cQ @0314203142: 7 steps
lem-cQ-at0314203142 : Ws → ⟪ (CCZ034 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CCZ034 ∷ []) ⟫ʷ
lem-cQ-at0314203142 c4 = run b0
  where
  b0 : Chain (CCZ034 ∷ CCZ123 ∷ []) (CCZ123 ∷ CCZ034 ∷ [])
  b0 = at 0 1 (CS03 ∷ CX40 ∷ CS03⁻ ∷ CX40 ∷ CS34 ∷ []) (wp0320 c4) ▸
       at 4 2 (CCZ123 ∷ CS34 ∷ []) (sym (wl0492 (lit c4))) ▸
       at 3 2 (CCZ123 ∷ CX40 ∷ []) (lem-comm-CX40-CCZ123 (lit c4)) ▸
       at 2 2 (CCZ123 ∷ CS03⁻ ∷ []) (sym (wl0495 (lit c4))) ▸
       at 1 2 (CCZ123 ∷ CX40 ∷ []) (lem-comm-CX40-CCZ123 (lit c4)) ▸
       at 0 2 (CCZ123 ∷ CS03 ∷ []) (sym (wl0490 (lit c4))) ▸
       at 1 5 (CCZ034 ∷ []) (sym (wp0320 c4)) ▸ done

-- box-tQ @04203243: 13 steps
lem-box-tQ-at04203243 : Ws → ⟪ (Bx4-1023 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ []) ⟫ʷ
lem-box-tQ-at04203243 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx4-1023 ∷ []) (CCZ014 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ014 ∷ CCZ124 ∷ Toff124 ∷ CZ13 ∷ Toff124 ∷ CCZ124 ∷ CZ13 ∷ [])
  b0 = at 0 1 (CCZ014 ∷ Toff401 ∷ Bx1-423 ∷ Toff401 ∷ CCZ014 ∷ Bx1-423 ∷ []) (refl) ▸
       at 2 1 (CCZ124 ∷ Toff124 ∷ Bx4-13 ∷ Toff124 ∷ CCZ124 ∷ Bx4-13 ∷ []) (refl) ▸
       at 4 1 (CZ13 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 2 6 (CCZ234 ∷ []) (wl0486 (lit c4)) ▸
       at 5 1 (CCZ124 ∷ Toff124 ∷ Bx4-13 ∷ Toff124 ∷ CCZ124 ∷ Bx4-13 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 10 1 (CZ13 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ014 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ014 ∷ CCZ124 ∷ Toff124 ∷ CZ13 ∷ Toff124 ∷ CCZ124 ∷ CZ13 ∷ []) (Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ [])
  b1 = at 5 6 (CCZ234 ∷ []) (wl0486 (lit c4)) ▸
       at 0 2 (Toff401 ∷ CCZ014 ∷ CZ01 ∷ []) (wp0355 c4) ▸
       at 2 2 (CCZ234 ∷ CZ01 ∷ []) (c₂ (CZ) (CCZ)) ▸
       at 1 2 (CCZ234 ∷ CCZ014 ∷ []) (lem-cQ-at04203243 c4) ▸
       at 2 4 (Toff401 ∷ []) (wp0356 c4) ▸ done

-- nat-SWbc @04203243: 23 steps
lem-nat-SWbc-at04203243 : Ws → ⟪ (Sw02 ∷ Bx4-1023 ∷ Sw02 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1203 ∷ []) ⟫ʷ
lem-nat-SWbc-at04203243 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw02 ∷ Bx4-1023 ∷ Sw02 ∷ []) (CCZ124 ∷ Toff412 ∷ CCZ014 ∷ Toff104 ∷ Bx4-13 ∷ Toff104 ∷ Sw02 ∷ CCZ124 ∷ Bx4-13 ∷ Toff401 ∷ CCZ014 ∷ Bx1-423 ∷ Sw02 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff401 ∷ Bx1-423 ∷ Toff401 ∷ CCZ014 ∷ Bx1-423 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw02 ∷ []) (sym (wp0339 c4)) ▸
       at 1 2 (Toff412 ∷ Sw02 ∷ []) (wp0370 c4) ▸
       at 3 1 (CCZ124 ∷ Toff124 ∷ Bx4-13 ∷ Toff124 ∷ CCZ124 ∷ Bx4-13 ∷ []) (refl) ▸
       at 2 2 (CCZ014 ∷ Sw02 ∷ []) (sym (wp0337 c4)) ▸
       at 3 2 (Toff104 ∷ Sw02 ∷ []) (wp0371 c4) ▸
       at 4 2 (Bx4-13 ∷ Sw02 ∷ []) (lem-comm-SWAP02-BOX⟨4·13⟩ (lit c4)) ▸
       at 5 2 (Toff104 ∷ Sw02 ∷ []) (wp0371 c4) ▸ done

  b1 : Chain (CCZ124 ∷ Toff412 ∷ CCZ014 ∷ Toff104 ∷ Bx4-13 ∷ Toff104 ∷ Sw02 ∷ CCZ124 ∷ Bx4-13 ∷ Toff401 ∷ CCZ014 ∷ Bx1-423 ∷ Sw02 ∷ []) (CCZ124 ∷ Toff412 ∷ CCZ014 ∷ Toff104 ∷ Bx4-13 ∷ Toff104 ∷ CCZ014 ∷ Bx4-13 ∷ Toff412 ∷ CCZ124 ∷ CCZ014 ∷ Toff104 ∷ Bx4-13 ∷ Sw02 ∷ Toff124 ∷ CCZ124 ∷ Bx4-13 ∷ Sw02 ∷ [])
  b1 = at 6 2 (CCZ014 ∷ Sw02 ∷ []) (sym (wp0337 c4)) ▸
       at 7 2 (Bx4-13 ∷ Sw02 ∷ []) (lem-comm-SWAP02-BOX⟨4·13⟩ (lit c4)) ▸
       at 8 2 (Toff412 ∷ Sw02 ∷ []) (wp0370 c4) ▸
       at 9 2 (CCZ124 ∷ Sw02 ∷ []) (sym (wp0339 c4)) ▸
       at 11 1 (CCZ124 ∷ Toff124 ∷ Bx4-13 ∷ Toff124 ∷ CCZ124 ∷ Bx4-13 ∷ []) (refl) ▸
       at 10 2 (CCZ014 ∷ Sw02 ∷ []) (sym (wp0337 c4)) ▸
       at 11 2 (Toff104 ∷ Sw02 ∷ []) (wp0371 c4) ▸
       at 12 2 (Bx4-13 ∷ Sw02 ∷ []) (lem-comm-SWAP02-BOX⟨4·13⟩ (lit c4)) ▸ done

  b2 : Chain (CCZ124 ∷ Toff412 ∷ CCZ014 ∷ Toff104 ∷ Bx4-13 ∷ Toff104 ∷ CCZ014 ∷ Bx4-13 ∷ Toff412 ∷ CCZ124 ∷ CCZ014 ∷ Toff104 ∷ Bx4-13 ∷ Sw02 ∷ Toff124 ∷ CCZ124 ∷ Bx4-13 ∷ Sw02 ∷ []) (Bx4-1203 ∷ [])
  b2 = at 13 2 (Toff104 ∷ Sw02 ∷ []) (wp0371 c4) ▸
       at 14 2 (CCZ014 ∷ Sw02 ∷ []) (sym (wp0337 c4)) ▸
       at 15 2 (Bx4-13 ∷ Sw02 ∷ []) (lem-comm-SWAP02-BOX⟨4·13⟩ (lit c4)) ▸
       at 16 2 [] (wl0485 (lit c4)) ▸
       at 2 6 (Bx1-403 ∷ []) (refl) ▸
       at 5 6 (Bx1-403 ∷ []) (refl) ▸
       at 0 6 (Bx4-1203 ∷ []) (refl) ▸ done

-- box-tQ @032032: 13 steps
lem-box-tQ-at032032 : Ws → ⟪ (Bx3-1024 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ []) ⟫ʷ
lem-box-tQ-at032032 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-1024 ∷ []) (CCZ013 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ013 ∷ CCZ123 ∷ Toff123 ∷ CZ14 ∷ Toff123 ∷ CCZ123 ∷ CZ14 ∷ [])
  b0 = at 0 1 (CCZ013 ∷ Toff301 ∷ Bx1-324 ∷ Toff301 ∷ CCZ013 ∷ Bx1-324 ∷ []) (refl) ▸
       at 2 1 (CCZ123 ∷ Toff123 ∷ Bx3-14 ∷ Toff123 ∷ CCZ123 ∷ Bx3-14 ∷ []) (refl) ▸
       at 4 1 (CZ14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 2 6 (CCZ234 ∷ []) (wl0518 (lit c4)) ▸
       at 5 1 (CCZ123 ∷ Toff123 ∷ Bx3-14 ∷ Toff123 ∷ CCZ123 ∷ Bx3-14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 10 1 (CZ14 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ013 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ013 ∷ CCZ123 ∷ Toff123 ∷ CZ14 ∷ Toff123 ∷ CCZ123 ∷ CZ14 ∷ []) (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ [])
  b1 = at 5 6 (CCZ234 ∷ []) (wl0518 (lit c4)) ▸
       at 0 2 (Toff301 ∷ CCZ013 ∷ CZ01 ∷ []) (wl0519 (lit c4)) ▸
       at 2 2 (CCZ234 ∷ CZ01 ∷ []) (c₂ (CZ) (CCZ)) ▸
       at 1 2 (CCZ234 ∷ CCZ013 ∷ []) (lem-cQ-at032032 c4) ▸
       at 2 4 (Toff301 ∷ []) (wl0520 (lit c4)) ▸ done

-- nat-SWbc @032032: 23 steps
lem-nat-SWbc-at032032 : Ws → ⟪ (Sw02 ∷ Bx3-1024 ∷ Sw02 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1204 ∷ []) ⟫ʷ
lem-nat-SWbc-at032032 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw02 ∷ Bx3-1024 ∷ Sw02 ∷ []) (CCZ123 ∷ Toff312 ∷ CCZ013 ∷ Toff103 ∷ Bx3-14 ∷ Toff103 ∷ Sw02 ∷ CCZ123 ∷ Bx3-14 ∷ Toff301 ∷ CCZ013 ∷ Bx1-324 ∷ Sw02 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff301 ∷ Bx1-324 ∷ Toff301 ∷ CCZ013 ∷ Bx1-324 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw02 ∷ []) (sym (wl0528 (lit c4))) ▸
       at 1 2 (Toff312 ∷ Sw02 ∷ []) (wl0529 (lit c4)) ▸
       at 3 1 (CCZ123 ∷ Toff123 ∷ Bx3-14 ∷ Toff123 ∷ CCZ123 ∷ Bx3-14 ∷ []) (refl) ▸
       at 2 2 (CCZ013 ∷ Sw02 ∷ []) (sym (wl0530 (lit c4))) ▸
       at 3 2 (Toff103 ∷ Sw02 ∷ []) (wl0531 (lit c4)) ▸
       at 4 2 (Bx3-14 ∷ Sw02 ∷ []) (lem-comm-SWAP02-BOX⟨3·14⟩ (lit c4)) ▸
       at 5 2 (Toff103 ∷ Sw02 ∷ []) (wl0531 (lit c4)) ▸ done

  b1 : Chain (CCZ123 ∷ Toff312 ∷ CCZ013 ∷ Toff103 ∷ Bx3-14 ∷ Toff103 ∷ Sw02 ∷ CCZ123 ∷ Bx3-14 ∷ Toff301 ∷ CCZ013 ∷ Bx1-324 ∷ Sw02 ∷ []) (CCZ123 ∷ Toff312 ∷ CCZ013 ∷ Toff103 ∷ Bx3-14 ∷ Toff103 ∷ CCZ013 ∷ Bx3-14 ∷ Toff312 ∷ CCZ123 ∷ CCZ013 ∷ Toff103 ∷ Bx3-14 ∷ Sw02 ∷ Toff123 ∷ CCZ123 ∷ Bx3-14 ∷ Sw02 ∷ [])
  b1 = at 6 2 (CCZ013 ∷ Sw02 ∷ []) (sym (wl0530 (lit c4))) ▸
       at 7 2 (Bx3-14 ∷ Sw02 ∷ []) (lem-comm-SWAP02-BOX⟨3·14⟩ (lit c4)) ▸
       at 8 2 (Toff312 ∷ Sw02 ∷ []) (wl0529 (lit c4)) ▸
       at 9 2 (CCZ123 ∷ Sw02 ∷ []) (sym (wl0528 (lit c4))) ▸
       at 11 1 (CCZ123 ∷ Toff123 ∷ Bx3-14 ∷ Toff123 ∷ CCZ123 ∷ Bx3-14 ∷ []) (refl) ▸
       at 10 2 (CCZ013 ∷ Sw02 ∷ []) (sym (wl0530 (lit c4))) ▸
       at 11 2 (Toff103 ∷ Sw02 ∷ []) (wl0531 (lit c4)) ▸
       at 12 2 (Bx3-14 ∷ Sw02 ∷ []) (lem-comm-SWAP02-BOX⟨3·14⟩ (lit c4)) ▸ done

  b2 : Chain (CCZ123 ∷ Toff312 ∷ CCZ013 ∷ Toff103 ∷ Bx3-14 ∷ Toff103 ∷ CCZ013 ∷ Bx3-14 ∷ Toff312 ∷ CCZ123 ∷ CCZ013 ∷ Toff103 ∷ Bx3-14 ∷ Sw02 ∷ Toff123 ∷ CCZ123 ∷ Bx3-14 ∷ Sw02 ∷ []) (Bx3-1204 ∷ [])
  b2 = at 13 2 (Toff103 ∷ Sw02 ∷ []) (wl0531 (lit c4)) ▸
       at 14 2 (CCZ013 ∷ Sw02 ∷ []) (sym (wl0530 (lit c4))) ▸
       at 15 2 (Bx3-14 ∷ Sw02 ∷ []) (lem-comm-SWAP02-BOX⟨3·14⟩ (lit c4)) ▸
       at 16 2 [] (wl0485 (lit c4)) ▸
       at 2 6 (Bx1-304 ∷ []) (refl) ▸
       at 5 6 (Bx1-304 ∷ []) (refl) ▸
       at 0 6 (Bx3-1204 ∷ []) (refl) ▸ done

-- nat-SWbc @0330: 23 steps
lem-nat-SWbc-at0330 : Ws → ⟪ (Sw02 ∷ Bx3-1204 ∷ Sw02 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1024 ∷ []) ⟫ʷ
lem-nat-SWbc-at0330 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw02 ∷ Bx3-1204 ∷ Sw02 ∷ []) (CCZ013 ∷ Toff301 ∷ CCZ123 ∷ Toff123 ∷ Bx3-14 ∷ Toff123 ∷ Sw02 ∷ CCZ013 ∷ Bx3-14 ∷ Toff312 ∷ CCZ123 ∷ Bx1-304 ∷ Sw02 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff312 ∷ Bx1-304 ∷ Toff312 ∷ CCZ123 ∷ Bx1-304 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw02 ∷ []) (sym (wl0530 (lit c4))) ▸
       at 1 2 (Toff301 ∷ Sw02 ∷ []) (wl0539 (lit c4)) ▸
       at 3 1 (CCZ013 ∷ Toff103 ∷ Bx3-14 ∷ Toff103 ∷ CCZ013 ∷ Bx3-14 ∷ []) (refl) ▸
       at 2 2 (CCZ123 ∷ Sw02 ∷ []) (sym (wl0528 (lit c4))) ▸
       at 3 2 (Toff123 ∷ Sw02 ∷ []) (wl0540 (lit c4)) ▸
       at 4 2 (Bx3-14 ∷ Sw02 ∷ []) (lem-comm-SWAP02-BOX⟨3·14⟩ (lit c4)) ▸
       at 5 2 (Toff123 ∷ Sw02 ∷ []) (wl0540 (lit c4)) ▸ done

  b1 : Chain (CCZ013 ∷ Toff301 ∷ CCZ123 ∷ Toff123 ∷ Bx3-14 ∷ Toff123 ∷ Sw02 ∷ CCZ013 ∷ Bx3-14 ∷ Toff312 ∷ CCZ123 ∷ Bx1-304 ∷ Sw02 ∷ []) (CCZ013 ∷ Toff301 ∷ CCZ123 ∷ Toff123 ∷ Bx3-14 ∷ Toff123 ∷ CCZ123 ∷ Bx3-14 ∷ Toff301 ∷ CCZ013 ∷ CCZ123 ∷ Toff123 ∷ Bx3-14 ∷ Sw02 ∷ Toff103 ∷ CCZ013 ∷ Bx3-14 ∷ Sw02 ∷ [])
  b1 = at 6 2 (CCZ123 ∷ Sw02 ∷ []) (sym (wl0528 (lit c4))) ▸
       at 7 2 (Bx3-14 ∷ Sw02 ∷ []) (lem-comm-SWAP02-BOX⟨3·14⟩ (lit c4)) ▸
       at 8 2 (Toff301 ∷ Sw02 ∷ []) (wl0539 (lit c4)) ▸
       at 9 2 (CCZ013 ∷ Sw02 ∷ []) (sym (wl0530 (lit c4))) ▸
       at 11 1 (CCZ013 ∷ Toff103 ∷ Bx3-14 ∷ Toff103 ∷ CCZ013 ∷ Bx3-14 ∷ []) (refl) ▸
       at 10 2 (CCZ123 ∷ Sw02 ∷ []) (sym (wl0528 (lit c4))) ▸
       at 11 2 (Toff123 ∷ Sw02 ∷ []) (wl0540 (lit c4)) ▸
       at 12 2 (Bx3-14 ∷ Sw02 ∷ []) (lem-comm-SWAP02-BOX⟨3·14⟩ (lit c4)) ▸ done

  b2 : Chain (CCZ013 ∷ Toff301 ∷ CCZ123 ∷ Toff123 ∷ Bx3-14 ∷ Toff123 ∷ CCZ123 ∷ Bx3-14 ∷ Toff301 ∷ CCZ013 ∷ CCZ123 ∷ Toff123 ∷ Bx3-14 ∷ Sw02 ∷ Toff103 ∷ CCZ013 ∷ Bx3-14 ∷ Sw02 ∷ []) (Bx3-1024 ∷ [])
  b2 = at 13 2 (Toff123 ∷ Sw02 ∷ []) (wl0540 (lit c4)) ▸
       at 14 2 (CCZ123 ∷ Sw02 ∷ []) (sym (wl0528 (lit c4))) ▸
       at 15 2 (Bx3-14 ∷ Sw02 ∷ []) (lem-comm-SWAP02-BOX⟨3·14⟩ (lit c4)) ▸
       at 16 2 [] (wl0485 (lit c4)) ▸
       at 2 6 (Bx1-324 ∷ []) (refl) ▸
       at 5 6 (Bx1-324 ∷ []) (refl) ▸
       at 0 6 (Bx3-1024 ∷ []) (refl) ▸ done

-- cQ @0214203143: 7 steps
lem-cQ-at0214203143 : Ws → ⟪ (CCZ024 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CCZ024 ∷ []) ⟫ʷ
lem-cQ-at0214203143 c4 = run b0
  where
  b0 : Chain (CCZ024 ∷ CCZ123 ∷ []) (CCZ123 ∷ CCZ024 ∷ [])
  b0 = at 0 1 (CS02 ∷ CX40 ∷ CS02⁻ ∷ CX40 ∷ CS24 ∷ []) (wp0496 c4) ▸
       at 4 2 (CCZ123 ∷ CS24 ∷ []) (sym (wl0173 (lit c4))) ▸
       at 3 2 (CCZ123 ∷ CX40 ∷ []) (lem-comm-CX40-CCZ123 (lit c4)) ▸
       at 2 2 (CCZ123 ∷ CS02⁻ ∷ []) (sym (wl0611 (lit c4))) ▸
       at 1 2 (CCZ123 ∷ CX40 ∷ []) (lem-comm-CX40-CCZ123 (lit c4)) ▸
       at 0 2 (CCZ123 ∷ CS02 ∷ []) (sym (wl0171 (lit c4))) ▸
       at 1 5 (CCZ024 ∷ []) (sym (wp0496 c4)) ▸ done

-- cQ @0214213043: 7 steps
lem-cQ-at0214213043 : Ws → ⟪ (CCZ124 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ CCZ124 ∷ []) ⟫ʷ
lem-cQ-at0214213043 c4 = run b0
  where
  b0 : Chain (CCZ124 ∷ CCZ023 ∷ []) (CCZ023 ∷ CCZ124 ∷ [])
  b0 = at 0 1 (CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ []) (wl0334 (lit c4)) ▸
       at 4 2 (CCZ023 ∷ CS24 ∷ []) (sym (wp0513 c4)) ▸
       at 3 2 (CCZ023 ∷ CX41 ∷ []) (lem-comm-CX41-CCZ023 (lit c4)) ▸
       at 2 2 (CCZ023 ∷ CS12⁻ ∷ []) (sym (wl0620 (lit c4))) ▸
       at 1 2 (CCZ023 ∷ CX41 ∷ []) (lem-comm-CX41-CCZ023 (lit c4)) ▸
       at 0 2 (CCZ023 ∷ CS12 ∷ []) (sym (wl0621 (lit c4))) ▸
       at 1 5 (CCZ124 ∷ []) (sym (wl0334 (lit c4))) ▸ done

-- cQ @0210233441: 7 steps
lem-cQ-at0210233441 : Ws → ⟪ (CCZ023 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ CCZ023 ∷ []) ⟫ʷ
lem-cQ-at0210233441 c4 = run b0
  where
  b0 : Chain (CCZ023 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ023 ∷ [])
  b0 = at 0 1 (CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ []) (wl0637 (lit c4)) ▸
       at 4 2 (CCZ124 ∷ CS02 ∷ []) (sym (wp0515 c4)) ▸
       at 3 2 (CCZ124 ∷ CX03 ∷ []) (lem-comm-CX03-CCZ124 (lit c4)) ▸
       at 2 2 (CCZ124 ∷ CS23⁻ ∷ []) (sym (wl0638 (lit c4))) ▸
       at 1 2 (CCZ124 ∷ CX03 ∷ []) (lem-comm-CX03-CCZ124 (lit c4)) ▸
       at 0 2 (CCZ124 ∷ CS23 ∷ []) (sym (wl0639 (lit c4))) ▸
       at 1 5 (CCZ023 ∷ []) (sym (wl0637 (lit c4))) ▸ done

-- cQ @14213243: 7 steps
lem-cQ-at14213243 : Ws → ⟪ (CCZ014 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ CCZ014 ∷ []) ⟫ʷ
lem-cQ-at14213243 c4 = run b0
  where
  b0 : Chain (CCZ014 ∷ CCZ023 ∷ []) (CCZ023 ∷ CCZ014 ∷ [])
  b0 = at 0 1 (CS01 ∷ CX41 ∷ CS01⁻ ∷ CX41 ∷ CS04 ∷ []) (wp0540 c4) ▸
       at 4 2 (CCZ023 ∷ CS04 ∷ []) (sym (wp0048 c4)) ▸
       at 3 2 (CCZ023 ∷ CX41 ∷ []) (lem-comm-CX41-CCZ023 (lit c4)) ▸
       at 2 2 (CCZ023 ∷ CS01⁻ ∷ []) (sym (wl0667 (lit c4))) ▸
       at 1 2 (CCZ023 ∷ CX41 ∷ []) (lem-comm-CX41-CCZ023 (lit c4)) ▸
       at 0 2 (CCZ023 ∷ CS01 ∷ []) (sym (wl0199 (lit c4))) ▸
       at 1 5 (CCZ014 ∷ []) (sym (wp0540 c4)) ▸ done

-- cQ @143143: 7 steps
lem-cQ-at143143 : Ws → ⟪ (CCZ024 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ CCZ024 ∷ []) ⟫ʷ
lem-cQ-at143143 c4 = run b0
  where
  b0 : Chain (CCZ024 ∷ CCZ013 ∷ []) (CCZ013 ∷ CCZ024 ∷ [])
  b0 = at 0 1 (CS02 ∷ CX42 ∷ CS02⁻ ∷ CX42 ∷ CS04 ∷ []) (wp0213 c4) ▸
       at 4 2 (CCZ013 ∷ CS04 ∷ []) (sym (wp0077 c4)) ▸
       at 3 2 (CCZ013 ∷ CX42 ∷ []) (lem-comm-CX42-CCZ013 (lit c4)) ▸
       at 2 2 (CCZ013 ∷ CS02⁻ ∷ []) (sym (wl0342 (lit c4))) ▸
       at 1 2 (CCZ013 ∷ CX42 ∷ []) (lem-comm-CX42-CCZ013 (lit c4)) ▸
       at 0 2 (CCZ013 ∷ CS02 ∷ []) (sym (wl0225 (lit c4))) ▸
       at 1 5 (CCZ024 ∷ []) (sym (wp0213 c4)) ▸ done

-- nat-SWbc @0210243143: 23 steps
lem-nat-SWbc-at0210243143 : Ws → ⟪ (Sw14 ∷ Bx2-0413 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0143 ∷ []) ⟫ʷ
lem-nat-SWbc-at0210243143 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw14 ∷ Bx2-0413 ∷ Sw14 ∷ []) (CCZ012 ∷ Toff201 ∷ CCZ024 ∷ Toff024 ∷ Bx2-03 ∷ Toff024 ∷ Sw14 ∷ CCZ012 ∷ Bx2-03 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ Sw14 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff204 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw14 ∷ []) (sym (wp0194 c4)) ▸
       at 1 2 (Toff201 ∷ Sw14 ∷ []) (wp0569 c4) ▸
       at 3 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) (refl) ▸
       at 2 2 (CCZ024 ∷ Sw14 ∷ []) (sym (wp0196 c4)) ▸
       at 3 2 (Toff024 ∷ Sw14 ∷ []) (wp0570 c4) ▸
       at 4 2 (Bx2-03 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨2·03⟩ (lit c4)) ▸
       at 5 2 (Toff024 ∷ Sw14 ∷ []) (wp0570 c4) ▸ done

  b1 : Chain (CCZ012 ∷ Toff201 ∷ CCZ024 ∷ Toff024 ∷ Bx2-03 ∷ Toff024 ∷ Sw14 ∷ CCZ012 ∷ Bx2-03 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ Sw14 ∷ []) (CCZ012 ∷ Toff201 ∷ CCZ024 ∷ Toff024 ∷ Bx2-03 ∷ Toff024 ∷ CCZ024 ∷ Bx2-03 ∷ Toff201 ∷ CCZ012 ∷ CCZ024 ∷ Toff024 ∷ Bx2-03 ∷ Sw14 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ Sw14 ∷ [])
  b1 = at 6 2 (CCZ024 ∷ Sw14 ∷ []) (sym (wp0196 c4)) ▸
       at 7 2 (Bx2-03 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨2·03⟩ (lit c4)) ▸
       at 8 2 (Toff201 ∷ Sw14 ∷ []) (wp0569 c4) ▸
       at 9 2 (CCZ012 ∷ Sw14 ∷ []) (sym (wp0194 c4)) ▸
       at 11 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) (refl) ▸
       at 10 2 (CCZ024 ∷ Sw14 ∷ []) (sym (wp0196 c4)) ▸
       at 11 2 (Toff024 ∷ Sw14 ∷ []) (wp0570 c4) ▸
       at 12 2 (Bx2-03 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨2·03⟩ (lit c4)) ▸ done

  b2 : Chain (CCZ012 ∷ Toff201 ∷ CCZ024 ∷ Toff024 ∷ Bx2-03 ∷ Toff024 ∷ CCZ024 ∷ Bx2-03 ∷ Toff201 ∷ CCZ012 ∷ CCZ024 ∷ Toff024 ∷ Bx2-03 ∷ Sw14 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ Sw14 ∷ []) (Bx2-0143 ∷ [])
  b2 = at 13 2 (Toff024 ∷ Sw14 ∷ []) (wp0570 c4) ▸
       at 14 2 (CCZ024 ∷ Sw14 ∷ []) (sym (wp0196 c4)) ▸
       at 15 2 (Bx2-03 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨2·03⟩ (lit c4)) ▸
       at 16 2 [] (wl0306 (lit c4)) ▸
       at 2 6 (Bx0-243 ∷ []) (refl) ▸
       at 5 6 (Bx0-243 ∷ []) (refl) ▸
       at 0 6 (Bx2-0143 ∷ []) (refl) ▸ done

-- tP @0210213443: 7 steps
lem-tP-at0210213443 : Ws → ⟪ (Toff201 ∷ Toff234 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ Toff201 ∷ []) ⟫ʷ
lem-tP-at0210213443 c4 = run b0
  where
  b0 : Chain (Toff201 ∷ Toff234 ∷ []) (Toff234 ∷ Toff201 ∷ [])
  b0 = at 0 1 (K2 ∷ CCZ012 ∷ K2⁻ ∷ []) (sym (wl0416 (lit c4))) ▸
       at 3 1 (K2 ∷ CCZ234 ∷ K2⁻ ∷ []) (sym (wl0417 (lit c4))) ▸
       at 2 2 [] (wl0175 (lit c4)) ▸
       at 1 2 (CCZ234 ∷ CCZ012 ∷ []) (lem-cQ-at0210213443 c4) ▸
       at 2 0 (K2⁻ ∷ K2 ∷ []) (sym (wl0175 (lit c4))) ▸
       at 0 3 (Toff234 ∷ []) (wl0417 (lit c4)) ▸
       at 1 3 (Toff201 ∷ []) (wl0416 (lit c4)) ▸ done

-- nat-SWbc @243243: 23 steps
lem-nat-SWbc-at243243 : Ws → ⟪ (Sw24 ∷ Bx0-1423 ∷ Sw24 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1243 ∷ []) ⟫ʷ
lem-nat-SWbc-at243243 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw24 ∷ Bx0-1423 ∷ Sw24 ∷ []) (CCZ012 ∷ Toff012 ∷ CCZ014 ∷ Toff104 ∷ Bx0-13 ∷ Toff104 ∷ Sw24 ∷ CCZ012 ∷ Bx0-13 ∷ Toff014 ∷ CCZ014 ∷ Bx1-023 ∷ Sw24 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff014 ∷ Bx1-023 ∷ Toff014 ∷ CCZ014 ∷ Bx1-023 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw24 ∷ []) (sym (wp0582 c4)) ▸
       at 1 2 (Toff012 ∷ Sw24 ∷ []) (wp0583 c4) ▸
       at 3 1 (CCZ012 ∷ Toff102 ∷ Bx0-13 ∷ Toff102 ∷ CCZ012 ∷ Bx0-13 ∷ []) (refl) ▸
       at 2 2 (CCZ014 ∷ Sw24 ∷ []) (sym (wp0584 c4)) ▸
       at 3 2 (Toff104 ∷ Sw24 ∷ []) (wp0585 c4) ▸
       at 4 2 (Bx0-13 ∷ Sw24 ∷ []) (lem-comm-SWAP24-BOX⟨0·13⟩ (lit c4)) ▸
       at 5 2 (Toff104 ∷ Sw24 ∷ []) (wp0585 c4) ▸ done

  b1 : Chain (CCZ012 ∷ Toff012 ∷ CCZ014 ∷ Toff104 ∷ Bx0-13 ∷ Toff104 ∷ Sw24 ∷ CCZ012 ∷ Bx0-13 ∷ Toff014 ∷ CCZ014 ∷ Bx1-023 ∷ Sw24 ∷ []) (CCZ012 ∷ Toff012 ∷ CCZ014 ∷ Toff104 ∷ Bx0-13 ∷ Toff104 ∷ CCZ014 ∷ Bx0-13 ∷ Toff012 ∷ CCZ012 ∷ CCZ014 ∷ Toff104 ∷ Bx0-13 ∷ Sw24 ∷ Toff102 ∷ CCZ012 ∷ Bx0-13 ∷ Sw24 ∷ [])
  b1 = at 6 2 (CCZ014 ∷ Sw24 ∷ []) (sym (wp0584 c4)) ▸
       at 7 2 (Bx0-13 ∷ Sw24 ∷ []) (lem-comm-SWAP24-BOX⟨0·13⟩ (lit c4)) ▸
       at 8 2 (Toff012 ∷ Sw24 ∷ []) (wp0583 c4) ▸
       at 9 2 (CCZ012 ∷ Sw24 ∷ []) (sym (wp0582 c4)) ▸
       at 11 1 (CCZ012 ∷ Toff102 ∷ Bx0-13 ∷ Toff102 ∷ CCZ012 ∷ Bx0-13 ∷ []) (refl) ▸
       at 10 2 (CCZ014 ∷ Sw24 ∷ []) (sym (wp0584 c4)) ▸
       at 11 2 (Toff104 ∷ Sw24 ∷ []) (wp0585 c4) ▸
       at 12 2 (Bx0-13 ∷ Sw24 ∷ []) (lem-comm-SWAP24-BOX⟨0·13⟩ (lit c4)) ▸ done

  b2 : Chain (CCZ012 ∷ Toff012 ∷ CCZ014 ∷ Toff104 ∷ Bx0-13 ∷ Toff104 ∷ CCZ014 ∷ Bx0-13 ∷ Toff012 ∷ CCZ012 ∷ CCZ014 ∷ Toff104 ∷ Bx0-13 ∷ Sw24 ∷ Toff102 ∷ CCZ012 ∷ Bx0-13 ∷ Sw24 ∷ []) (Bx0-1243 ∷ [])
  b2 = at 13 2 (Toff104 ∷ Sw24 ∷ []) (wp0585 c4) ▸
       at 14 2 (CCZ014 ∷ Sw24 ∷ []) (sym (wp0584 c4)) ▸
       at 15 2 (Bx0-13 ∷ Sw24 ∷ []) (lem-comm-SWAP24-BOX⟨0·13⟩ (lit c4)) ▸
       at 16 2 [] (wl0322 (lit c4)) ▸
       at 2 6 (Bx1-043 ∷ []) (refl) ▸
       at 5 6 (Bx1-043 ∷ []) (refl) ▸
       at 0 6 (Bx0-1243 ∷ []) (refl) ▸ done

-- nat-SWbc @1441: 23 steps
lem-nat-SWbc-at1441 : Ws → ⟪ (Sw23 ∷ Bx0-4231 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4321 ∷ []) ⟫ʷ
lem-nat-SWbc-at1441 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw23 ∷ Bx0-4231 ∷ Sw23 ∷ []) (CCZ034 ∷ Toff034 ∷ CCZ024 ∷ Toff402 ∷ Bx0-41 ∷ Toff402 ∷ Sw23 ∷ CCZ034 ∷ Bx0-41 ∷ Toff024 ∷ CCZ024 ∷ Bx4-031 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff024 ∷ Bx4-031 ∷ Toff024 ∷ CCZ024 ∷ Bx4-031 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw23 ∷ []) (sym (wp0594 c4)) ▸
       at 1 2 (Toff034 ∷ Sw23 ∷ []) (wp0595 c4) ▸
       at 3 1 (CCZ034 ∷ Toff403 ∷ Bx0-41 ∷ Toff403 ∷ CCZ034 ∷ Bx0-41 ∷ []) (refl) ▸
       at 2 2 (CCZ024 ∷ Sw23 ∷ []) (sym (wp0596 c4)) ▸
       at 3 2 (Toff402 ∷ Sw23 ∷ []) (wp0597 c4) ▸
       at 4 2 (Bx0-41 ∷ Sw23 ∷ []) (lem-comm-SWAP23-BOX⟨0·41⟩ (lit c4)) ▸
       at 5 2 (Toff402 ∷ Sw23 ∷ []) (wp0597 c4) ▸ done

  b1 : Chain (CCZ034 ∷ Toff034 ∷ CCZ024 ∷ Toff402 ∷ Bx0-41 ∷ Toff402 ∷ Sw23 ∷ CCZ034 ∷ Bx0-41 ∷ Toff024 ∷ CCZ024 ∷ Bx4-031 ∷ Sw23 ∷ []) (CCZ034 ∷ Toff034 ∷ CCZ024 ∷ Toff402 ∷ Bx0-41 ∷ Toff402 ∷ CCZ024 ∷ Bx0-41 ∷ Toff034 ∷ CCZ034 ∷ CCZ024 ∷ Toff402 ∷ Bx0-41 ∷ Sw23 ∷ Toff403 ∷ CCZ034 ∷ Bx0-41 ∷ Sw23 ∷ [])
  b1 = at 6 2 (CCZ024 ∷ Sw23 ∷ []) (sym (wp0596 c4)) ▸
       at 7 2 (Bx0-41 ∷ Sw23 ∷ []) (lem-comm-SWAP23-BOX⟨0·41⟩ (lit c4)) ▸
       at 8 2 (Toff034 ∷ Sw23 ∷ []) (wp0595 c4) ▸
       at 9 2 (CCZ034 ∷ Sw23 ∷ []) (sym (wp0594 c4)) ▸
       at 11 1 (CCZ034 ∷ Toff403 ∷ Bx0-41 ∷ Toff403 ∷ CCZ034 ∷ Bx0-41 ∷ []) (refl) ▸
       at 10 2 (CCZ024 ∷ Sw23 ∷ []) (sym (wp0596 c4)) ▸
       at 11 2 (Toff402 ∷ Sw23 ∷ []) (wp0597 c4) ▸
       at 12 2 (Bx0-41 ∷ Sw23 ∷ []) (lem-comm-SWAP23-BOX⟨0·41⟩ (lit c4)) ▸ done

  b2 : Chain (CCZ034 ∷ Toff034 ∷ CCZ024 ∷ Toff402 ∷ Bx0-41 ∷ Toff402 ∷ CCZ024 ∷ Bx0-41 ∷ Toff034 ∷ CCZ034 ∷ CCZ024 ∷ Toff402 ∷ Bx0-41 ∷ Sw23 ∷ Toff403 ∷ CCZ034 ∷ Bx0-41 ∷ Sw23 ∷ []) (Bx0-4321 ∷ [])
  b2 = at 13 2 (Toff402 ∷ Sw23 ∷ []) (wp0597 c4) ▸
       at 14 2 (CCZ024 ∷ Sw23 ∷ []) (sym (wp0596 c4)) ▸
       at 15 2 (Bx0-41 ∷ Sw23 ∷ []) (lem-comm-SWAP23-BOX⟨0·41⟩ (lit c4)) ▸
       at 16 2 [] (wl0003 (lit c4)) ▸
       at 2 6 (Bx4-021 ∷ []) (refl) ▸
       at 5 6 (Bx4-021 ∷ []) (refl) ▸
       at 0 6 (Bx0-4321 ∷ []) (refl) ▸ done

-- box-tQ @14233241: 13 steps
lem-box-tQ-at14233241 : Ws → ⟪ (Bx0-4321 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ []) ⟫ʷ
lem-box-tQ-at14233241 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-4321 ∷ []) (CCZ034 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ CCZ024 ∷ Toff402 ∷ CZ14 ∷ Toff402 ∷ CCZ024 ∷ CZ14 ∷ [])
  b0 = at 0 1 (CCZ034 ∷ Toff034 ∷ Bx4-021 ∷ Toff034 ∷ CCZ034 ∷ Bx4-021 ∷ []) (refl) ▸
       at 2 1 (CCZ024 ∷ Toff402 ∷ Bx0-41 ∷ Toff402 ∷ CCZ024 ∷ Bx0-41 ∷ []) (refl) ▸
       at 4 1 (CZ14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 2 6 (CCZ012 ∷ []) (sym (wp0162 c4)) ▸
       at 5 1 (CCZ024 ∷ Toff402 ∷ Bx0-41 ∷ Toff402 ∷ CCZ024 ∷ Bx0-41 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 10 1 (CZ14 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ034 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ CCZ024 ∷ Toff402 ∷ CZ14 ∷ Toff402 ∷ CCZ024 ∷ CZ14 ∷ []) (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ [])
  b1 = at 5 6 (CCZ012 ∷ []) (sym (wp0162 c4)) ▸
       at 0 2 (Toff034 ∷ CCZ034 ∷ CZ34 ∷ []) (wp0118 c4) ▸
       at 2 2 (CCZ012 ∷ CZ34 ∷ []) (sym (c₃ (CCZ) (CZ))) ▸
       at 1 2 (CCZ012 ∷ CCZ034 ∷ []) (lem-cQ-at14233241 c4) ▸
       at 2 4 (Toff034 ∷ []) (wp0119 c4) ▸ done

-- tP @14233241: 7 steps
lem-tP-at14233241 : Ws → ⟪ (Toff034 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ Toff034 ∷ []) ⟫ʷ
lem-tP-at14233241 c4 = run b0
  where
  b0 : Chain (Toff034 ∷ Toff012 ∷ []) (Toff012 ∷ Toff034 ∷ [])
  b0 = at 0 1 (K0 ∷ CCZ034 ∷ K0⁻ ∷ []) (sym (wp0004 c4)) ▸
       at 3 1 (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (sym (wl0156 (lit c4))) ▸
       at 2 2 [] (wl0157 (lit c4)) ▸
       at 1 2 (CCZ012 ∷ CCZ034 ∷ []) (lem-cQ-at14233241 c4) ▸
       at 2 0 (K0⁻ ∷ K0 ∷ []) (sym (wl0157 (lit c4))) ▸
       at 0 3 (Toff012 ∷ []) (wl0156 (lit c4)) ▸
       at 1 3 (Toff034 ∷ []) (wp0004 c4) ▸ done

-- cQ @12213443: 7 steps
lem-cQ-at12213443 : Ws → ⟪ (CCZ012 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ CCZ012 ∷ []) ⟫ʷ
lem-cQ-at12213443 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ012 ∷ [])
  b0 = at 0 1 (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) (wl0270 (lit c4)) ▸
       at 4 2 (CCZ034 ∷ CS02 ∷ []) (sym (wp0003 c4)) ▸
       at 3 2 (CCZ034 ∷ CX21 ∷ []) (lem-comm-CX21-CCZ034 (lit c4)) ▸
       at 2 2 (CCZ034 ∷ CS01⁻ ∷ []) (sym (wp0120 c4)) ▸
       at 1 2 (CCZ034 ∷ CX21 ∷ []) (lem-comm-CX21-CCZ034 (lit c4)) ▸
       at 0 2 (CCZ034 ∷ CS01 ∷ []) (sym (wp0001 c4)) ▸
       at 1 5 (CCZ012 ∷ []) (sym (wl0270 (lit c4))) ▸ done

-- cQ @0314213042: 7 steps
lem-cQ-at0314213042 : Ws → ⟪ (CCZ134 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ CCZ134 ∷ []) ⟫ʷ
lem-cQ-at0314213042 c4 = run b0
  where
  b0 : Chain (CCZ134 ∷ CCZ023 ∷ []) (CCZ023 ∷ CCZ134 ∷ [])
  b0 = at 0 1 (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ []) (wl0617 (lit c4)) ▸
       at 4 2 (CCZ023 ∷ CS34 ∷ []) (sym (wp0543 c4)) ▸
       at 3 2 (CCZ023 ∷ CX41 ∷ []) (lem-comm-CX41-CCZ023 (lit c4)) ▸
       at 2 2 (CCZ023 ∷ CS13⁻ ∷ []) (sym (wl0669 (lit c4))) ▸
       at 1 2 (CCZ023 ∷ CX41 ∷ []) (lem-comm-CX41-CCZ023 (lit c4)) ▸
       at 0 2 (CCZ023 ∷ CS13 ∷ []) (sym (wl0670 (lit c4))) ▸
       at 1 5 (CCZ134 ∷ []) (sym (wl0617 (lit c4))) ▸ done

-- cQ @0213203441: 7 steps
lem-cQ-at0213203441 : Ws → ⟪ (CCZ023 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ CCZ023 ∷ []) ⟫ʷ
lem-cQ-at0213203441 c4 = run b0
  where
  b0 : Chain (CCZ023 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ023 ∷ [])
  b0 = at 0 1 (CS02 ∷ CX30 ∷ CS02⁻ ∷ CX30 ∷ CS23 ∷ []) (wl0757 (lit c4)) ▸
       at 4 2 (CCZ124 ∷ CS23 ∷ []) (sym (wl0639 (lit c4))) ▸
       at 3 2 (CCZ124 ∷ CX30 ∷ []) (lem-comm-CX30-CCZ124 (lit c4)) ▸
       at 2 2 (CCZ124 ∷ CS02⁻ ∷ []) (sym (wp0679 c4)) ▸
       at 1 2 (CCZ124 ∷ CX30 ∷ []) (lem-comm-CX30-CCZ124 (lit c4)) ▸
       at 0 2 (CCZ124 ∷ CS02 ∷ []) (sym (wp0515 c4)) ▸
       at 1 5 (CCZ023 ∷ []) (sym (wl0757 (lit c4))) ▸ done

-- tP @032032: 7 steps
lem-tP-at032032 : Ws → ⟪ (Toff301 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ Toff301 ∷ []) ⟫ʷ
lem-tP-at032032 c4 = run b0
  where
  b0 : Chain (Toff301 ∷ Toff324 ∷ []) (Toff324 ∷ Toff301 ∷ [])
  b0 = at 0 1 (K3 ∷ CCZ013 ∷ K3⁻ ∷ []) (sym (wl0434 (lit c4))) ▸
       at 3 1 (K3 ∷ CCZ234 ∷ K3⁻ ∷ []) (sym (wl0435 (lit c4))) ▸
       at 2 2 [] (wl0436 (lit c4)) ▸
       at 1 2 (CCZ234 ∷ CCZ013 ∷ []) (lem-cQ-at032032 c4) ▸
       at 2 0 (K3⁻ ∷ K3 ∷ []) (sym (wl0436 (lit c4))) ▸
       at 0 3 (Toff324 ∷ []) (wl0435 (lit c4)) ▸
       at 1 3 (Toff301 ∷ []) (wl0434 (lit c4)) ▸ done

-- cQ @0312243140: 7 steps
lem-cQ-at0312243140 : Ws → ⟪ (CCZ234 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ CCZ234 ∷ []) ⟫ʷ
lem-cQ-at0312243140 c4 = run b0
  where
  b0 : Chain (CCZ234 ∷ CCZ013 ∷ []) (CCZ013 ∷ CCZ234 ∷ [])
  b0 = at 0 1 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (wl0245 (lit c4)) ▸
       at 4 2 (CCZ013 ∷ CS23 ∷ []) (sym (wl0324 (lit c4))) ▸
       at 3 2 (CCZ013 ∷ CX24 ∷ []) (lem-comm-CX24-CCZ013 (lit c4)) ▸
       at 2 2 (CCZ013 ∷ CS34⁻ ∷ []) (sym (wp0184 c4)) ▸
       at 1 2 (CCZ013 ∷ CX24 ∷ []) (lem-comm-CX24-CCZ013 (lit c4)) ▸
       at 0 2 (CCZ013 ∷ CS34 ∷ []) (sym (wp0185 c4)) ▸
       at 1 5 (CCZ234 ∷ []) (sym (wl0245 (lit c4))) ▸ done

-- nat-SWbc @0312243140: 23 steps
lem-nat-SWbc-at0312243140 : Ws → ⟪ (Sw14 ∷ Bx3-2410 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2140 ∷ []) ⟫ʷ
lem-nat-SWbc-at0312243140 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw14 ∷ Bx3-2410 ∷ Sw14 ∷ []) (CCZ123 ∷ Toff312 ∷ CCZ234 ∷ Toff234 ∷ Bx3-20 ∷ Toff234 ∷ Sw14 ∷ CCZ123 ∷ Bx3-20 ∷ Toff324 ∷ CCZ234 ∷ Bx2-310 ∷ Sw14 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff324 ∷ Bx2-310 ∷ Toff324 ∷ CCZ234 ∷ Bx2-310 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw14 ∷ []) (sym (wl0854 (lit c4))) ▸
       at 1 2 (Toff312 ∷ Sw14 ∷ []) (wl0855 (lit c4)) ▸
       at 3 1 (CCZ123 ∷ Toff213 ∷ Bx3-20 ∷ Toff213 ∷ CCZ123 ∷ Bx3-20 ∷ []) (refl) ▸
       at 2 2 (CCZ234 ∷ Sw14 ∷ []) (sym (wl0856 (lit c4))) ▸
       at 3 2 (Toff234 ∷ Sw14 ∷ []) (wl0857 (lit c4)) ▸
       at 4 2 (Bx3-20 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨3·20⟩ (lit c4)) ▸
       at 5 2 (Toff234 ∷ Sw14 ∷ []) (wl0857 (lit c4)) ▸ done

  b1 : Chain (CCZ123 ∷ Toff312 ∷ CCZ234 ∷ Toff234 ∷ Bx3-20 ∷ Toff234 ∷ Sw14 ∷ CCZ123 ∷ Bx3-20 ∷ Toff324 ∷ CCZ234 ∷ Bx2-310 ∷ Sw14 ∷ []) (CCZ123 ∷ Toff312 ∷ CCZ234 ∷ Toff234 ∷ Bx3-20 ∷ Toff234 ∷ CCZ234 ∷ Bx3-20 ∷ Toff312 ∷ CCZ123 ∷ CCZ234 ∷ Toff234 ∷ Bx3-20 ∷ Sw14 ∷ Toff213 ∷ CCZ123 ∷ Bx3-20 ∷ Sw14 ∷ [])
  b1 = at 6 2 (CCZ234 ∷ Sw14 ∷ []) (sym (wl0856 (lit c4))) ▸
       at 7 2 (Bx3-20 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨3·20⟩ (lit c4)) ▸
       at 8 2 (Toff312 ∷ Sw14 ∷ []) (wl0855 (lit c4)) ▸
       at 9 2 (CCZ123 ∷ Sw14 ∷ []) (sym (wl0854 (lit c4))) ▸
       at 11 1 (CCZ123 ∷ Toff213 ∷ Bx3-20 ∷ Toff213 ∷ CCZ123 ∷ Bx3-20 ∷ []) (refl) ▸
       at 10 2 (CCZ234 ∷ Sw14 ∷ []) (sym (wl0856 (lit c4))) ▸
       at 11 2 (Toff234 ∷ Sw14 ∷ []) (wl0857 (lit c4)) ▸
       at 12 2 (Bx3-20 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨3·20⟩ (lit c4)) ▸ done

  b2 : Chain (CCZ123 ∷ Toff312 ∷ CCZ234 ∷ Toff234 ∷ Bx3-20 ∷ Toff234 ∷ CCZ234 ∷ Bx3-20 ∷ Toff312 ∷ CCZ123 ∷ CCZ234 ∷ Toff234 ∷ Bx3-20 ∷ Sw14 ∷ Toff213 ∷ CCZ123 ∷ Bx3-20 ∷ Sw14 ∷ []) (Bx3-2140 ∷ [])
  b2 = at 13 2 (Toff234 ∷ Sw14 ∷ []) (wl0857 (lit c4)) ▸
       at 14 2 (CCZ234 ∷ Sw14 ∷ []) (sym (wl0856 (lit c4))) ▸
       at 15 2 (Bx3-20 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨3·20⟩ (lit c4)) ▸
       at 16 2 [] (wl0306 (lit c4)) ▸
       at 2 6 (Bx2-340 ∷ []) (refl) ▸
       at 5 6 (Bx2-340 ∷ []) (refl) ▸
       at 0 6 (Bx3-2140 ∷ []) (refl) ▸ done

-- cQ @033440: 7 steps
lem-cQ-at033440 : Ws → ⟪ (CCZ123 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ CCZ123 ∷ []) ⟫ʷ
lem-cQ-at033440 c4 = run b0
  where
  b0 : Chain (CCZ123 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ123 ∷ [])
  b0 = at 0 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0207 (lit c4)) ▸
       at 4 2 (CCZ034 ∷ CS13 ∷ []) (sym (wp0312 c4)) ▸
       at 3 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸
       at 2 2 (CCZ034 ∷ CS23⁻ ∷ []) (sym (wp0313 c4)) ▸
       at 1 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸
       at 0 2 (CCZ034 ∷ CS23 ∷ []) (sym (wp0314 c4)) ▸
       at 1 5 (CCZ123 ∷ []) (sym (wl0207 (lit c4))) ▸ done

-- cQ @0312213440: 7 steps
lem-cQ-at0312213440 : Ws → ⟪ (CCZ123 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ CCZ123 ∷ []) ⟫ʷ
lem-cQ-at0312213440 c4 = run b0
  where
  b0 : Chain (CCZ123 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ123 ∷ [])
  b0 = at 0 1 (CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ []) (wl0326 (lit c4)) ▸
       at 4 2 (CCZ034 ∷ CS23 ∷ []) (sym (wp0314 c4)) ▸
       at 3 2 (CCZ034 ∷ CX21 ∷ []) (lem-comm-CX21-CCZ034 (lit c4)) ▸
       at 2 2 (CCZ034 ∷ CS13⁻ ∷ []) (sym (wp0734 c4)) ▸
       at 1 2 (CCZ034 ∷ CX21 ∷ []) (lem-comm-CX21-CCZ034 (lit c4)) ▸
       at 0 2 (CCZ034 ∷ CS13 ∷ []) (sym (wp0312 c4)) ▸
       at 1 5 (CCZ123 ∷ []) (sym (wl0326 (lit c4))) ▸ done

-- nat-SWbc @0312213440: 23 steps
lem-nat-SWbc-at0312213440 : Ws → ⟪ (Sw14 ∷ Bx3-2140 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2410 ∷ []) ⟫ʷ
lem-nat-SWbc-at0312213440 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw14 ∷ Bx3-2140 ∷ Sw14 ∷ []) (CCZ234 ∷ Toff324 ∷ CCZ123 ∷ Toff213 ∷ Bx3-20 ∷ Toff213 ∷ Sw14 ∷ CCZ234 ∷ Bx3-20 ∷ Toff312 ∷ CCZ123 ∷ Bx2-340 ∷ Sw14 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff312 ∷ Bx2-340 ∷ Toff312 ∷ CCZ123 ∷ Bx2-340 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw14 ∷ []) (sym (wl0856 (lit c4))) ▸
       at 1 2 (Toff324 ∷ Sw14 ∷ []) (wl0864 (lit c4)) ▸
       at 3 1 (CCZ234 ∷ Toff234 ∷ Bx3-20 ∷ Toff234 ∷ CCZ234 ∷ Bx3-20 ∷ []) (refl) ▸
       at 2 2 (CCZ123 ∷ Sw14 ∷ []) (sym (wl0854 (lit c4))) ▸
       at 3 2 (Toff213 ∷ Sw14 ∷ []) (wl0865 (lit c4)) ▸
       at 4 2 (Bx3-20 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨3·20⟩ (lit c4)) ▸
       at 5 2 (Toff213 ∷ Sw14 ∷ []) (wl0865 (lit c4)) ▸ done

  b1 : Chain (CCZ234 ∷ Toff324 ∷ CCZ123 ∷ Toff213 ∷ Bx3-20 ∷ Toff213 ∷ Sw14 ∷ CCZ234 ∷ Bx3-20 ∷ Toff312 ∷ CCZ123 ∷ Bx2-340 ∷ Sw14 ∷ []) (CCZ234 ∷ Toff324 ∷ CCZ123 ∷ Toff213 ∷ Bx3-20 ∷ Toff213 ∷ CCZ123 ∷ Bx3-20 ∷ Toff324 ∷ CCZ234 ∷ CCZ123 ∷ Toff213 ∷ Bx3-20 ∷ Sw14 ∷ Toff234 ∷ CCZ234 ∷ Bx3-20 ∷ Sw14 ∷ [])
  b1 = at 6 2 (CCZ123 ∷ Sw14 ∷ []) (sym (wl0854 (lit c4))) ▸
       at 7 2 (Bx3-20 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨3·20⟩ (lit c4)) ▸
       at 8 2 (Toff324 ∷ Sw14 ∷ []) (wl0864 (lit c4)) ▸
       at 9 2 (CCZ234 ∷ Sw14 ∷ []) (sym (wl0856 (lit c4))) ▸
       at 11 1 (CCZ234 ∷ Toff234 ∷ Bx3-20 ∷ Toff234 ∷ CCZ234 ∷ Bx3-20 ∷ []) (refl) ▸
       at 10 2 (CCZ123 ∷ Sw14 ∷ []) (sym (wl0854 (lit c4))) ▸
       at 11 2 (Toff213 ∷ Sw14 ∷ []) (wl0865 (lit c4)) ▸
       at 12 2 (Bx3-20 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨3·20⟩ (lit c4)) ▸ done

  b2 : Chain (CCZ234 ∷ Toff324 ∷ CCZ123 ∷ Toff213 ∷ Bx3-20 ∷ Toff213 ∷ CCZ123 ∷ Bx3-20 ∷ Toff324 ∷ CCZ234 ∷ CCZ123 ∷ Toff213 ∷ Bx3-20 ∷ Sw14 ∷ Toff234 ∷ CCZ234 ∷ Bx3-20 ∷ Sw14 ∷ []) (Bx3-2410 ∷ [])
  b2 = at 13 2 (Toff213 ∷ Sw14 ∷ []) (wl0865 (lit c4)) ▸
       at 14 2 (CCZ123 ∷ Sw14 ∷ []) (sym (wl0854 (lit c4))) ▸
       at 15 2 (Bx3-20 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨3·20⟩ (lit c4)) ▸
       at 16 2 [] (wl0306 (lit c4)) ▸
       at 2 6 (Bx2-310 ∷ []) (refl) ▸
       at 5 6 (Bx2-310 ∷ []) (refl) ▸
       at 0 6 (Bx3-2410 ∷ []) (refl) ▸ done

-- cQ @022330: 7 steps
lem-cQ-at022330 : Ws → ⟪ (CCZ123 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ CCZ123 ∷ []) ⟫ʷ
lem-cQ-at022330 c4 = run b0
  where
  b0 : Chain (CCZ123 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ123 ∷ [])
  b0 = at 0 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0242 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ CS12 ∷ []) (sym (wp0081 c4)) ▸
       at 3 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ CS23⁻ ∷ []) (sym (wp0091 c4)) ▸
       at 1 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 0 2 (CCZ024 ∷ CS23 ∷ []) (sym (wp0092 c4)) ▸
       at 1 5 (CCZ123 ∷ []) (sym (wl0242 (lit c4))) ▸ done

-- box-tQ @0220: 13 steps
lem-box-tQ-at0220 : Ws → ⟪ (Bx2-1034 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) ⟫ʷ
lem-box-tQ-at0220 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx2-1034 ∷ []) (CCZ012 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ012 ∷ CCZ123 ∷ Toff123 ∷ CZ14 ∷ Toff123 ∷ CCZ123 ∷ CZ14 ∷ [])
  b0 = at 0 1 (CCZ012 ∷ Toff201 ∷ Bx1-234 ∷ Toff201 ∷ CCZ012 ∷ Bx1-234 ∷ []) (refl) ▸
       at 2 1 (CCZ123 ∷ Toff123 ∷ Bx2-14 ∷ Toff123 ∷ CCZ123 ∷ Bx2-14 ∷ []) (refl) ▸
       at 4 1 (CZ14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 2 6 (CCZ234 ∷ []) (wl0518 (lit c4)) ▸
       at 5 1 (CCZ123 ∷ Toff123 ∷ Bx2-14 ∷ Toff123 ∷ CCZ123 ∷ Bx2-14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 10 1 (CZ14 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ012 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ012 ∷ CCZ123 ∷ Toff123 ∷ CZ14 ∷ Toff123 ∷ CCZ123 ∷ CZ14 ∷ []) (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ [])
  b1 = at 5 6 (CCZ234 ∷ []) (wl0518 (lit c4)) ▸
       at 0 2 (Toff201 ∷ CCZ012 ∷ CZ01 ∷ []) (wl0930 (lit c4)) ▸
       at 2 2 (CCZ234 ∷ CZ01 ∷ []) (c₂ (CZ) (CCZ)) ▸
       at 1 2 (CCZ234 ∷ CCZ012 ∷ []) (lem-cQ-at0220 c4) ▸
       at 2 4 (Toff201 ∷ []) (wl0931 (lit c4)) ▸ done

-- tP @0220: 7 steps
lem-tP-at0220 : Ws → ⟪ (Toff201 ∷ Toff234 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ Toff201 ∷ []) ⟫ʷ
lem-tP-at0220 c4 = run b0
  where
  b0 : Chain (Toff201 ∷ Toff234 ∷ []) (Toff234 ∷ Toff201 ∷ [])
  b0 = at 0 1 (K2 ∷ CCZ012 ∷ K2⁻ ∷ []) (sym (wl0416 (lit c4))) ▸
       at 3 1 (K2 ∷ CCZ234 ∷ K2⁻ ∷ []) (sym (wl0417 (lit c4))) ▸
       at 2 2 [] (wl0175 (lit c4)) ▸
       at 1 2 (CCZ234 ∷ CCZ012 ∷ []) (lem-cQ-at0220 c4) ▸
       at 2 0 (K2⁻ ∷ K2 ∷ []) (sym (wl0175 (lit c4))) ▸
       at 0 3 (Toff234 ∷ []) (wl0417 (lit c4)) ▸
       at 1 3 (Toff201 ∷ []) (wl0416 (lit c4)) ▸ done

-- box-tQ @0213243140: 13 steps
lem-box-tQ-at0213243140 : Ws → ⟪ (Bx2-3410 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ CCZ012 ∷ Toff234 ∷ CCZ012 ∷ []) ⟫ʷ
lem-box-tQ-at0213243140 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx2-3410 ∷ []) (CCZ234 ∷ Toff234 ∷ CCZ012 ∷ Toff234 ∷ CCZ234 ∷ CCZ123 ∷ Toff312 ∷ CZ03 ∷ Toff312 ∷ CCZ123 ∷ CZ03 ∷ [])
  b0 = at 0 1 (CCZ234 ∷ Toff234 ∷ Bx3-210 ∷ Toff234 ∷ CCZ234 ∷ Bx3-210 ∷ []) (refl) ▸
       at 2 1 (CCZ123 ∷ Toff312 ∷ Bx2-30 ∷ Toff312 ∷ CCZ123 ∷ Bx2-30 ∷ []) (refl) ▸
       at 4 1 (CZ03 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 2 6 (CCZ012 ∷ []) (sym (wl0935 (lit c4))) ▸
       at 5 1 (CCZ123 ∷ Toff312 ∷ Bx2-30 ∷ Toff312 ∷ CCZ123 ∷ Bx2-30 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 10 1 (CZ03 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ234 ∷ Toff234 ∷ CCZ012 ∷ Toff234 ∷ CCZ234 ∷ CCZ123 ∷ Toff312 ∷ CZ03 ∷ Toff312 ∷ CCZ123 ∷ CZ03 ∷ []) (Toff234 ∷ CCZ012 ∷ Toff234 ∷ CCZ012 ∷ [])
  b1 = at 5 6 (CCZ012 ∷ []) (sym (wl0935 (lit c4))) ▸
       at 0 2 (Toff234 ∷ CCZ234 ∷ CZ34 ∷ []) (wl0936 (lit c4)) ▸
       at 2 2 (CCZ012 ∷ CZ34 ∷ []) (sym (c₃ (CCZ) (CZ))) ▸
       at 1 2 (CCZ012 ∷ CCZ234 ∷ []) (lem-cQ-at0213243140 c4) ▸
       at 2 4 (Toff234 ∷ []) (wl0937 (lit c4)) ▸ done

-- nat-SWbc @0213243140: 23 steps
lem-nat-SWbc-at0213243140 : Ws → ⟪ (Sw14 ∷ Bx2-3410 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3140 ∷ []) ⟫ʷ
lem-nat-SWbc-at0213243140 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw14 ∷ Bx2-3410 ∷ Sw14 ∷ []) (CCZ123 ∷ Toff213 ∷ CCZ234 ∷ Toff324 ∷ Bx2-30 ∷ Toff324 ∷ Sw14 ∷ CCZ123 ∷ Bx2-30 ∷ Toff234 ∷ CCZ234 ∷ Bx3-210 ∷ Sw14 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff234 ∷ Bx3-210 ∷ Toff234 ∷ CCZ234 ∷ Bx3-210 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw14 ∷ []) (sym (wl0854 (lit c4))) ▸
       at 1 2 (Toff213 ∷ Sw14 ∷ []) (wl0865 (lit c4)) ▸
       at 3 1 (CCZ123 ∷ Toff312 ∷ Bx2-30 ∷ Toff312 ∷ CCZ123 ∷ Bx2-30 ∷ []) (refl) ▸
       at 2 2 (CCZ234 ∷ Sw14 ∷ []) (sym (wl0856 (lit c4))) ▸
       at 3 2 (Toff324 ∷ Sw14 ∷ []) (wl0864 (lit c4)) ▸
       at 4 2 (Bx2-30 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨2·30⟩ (lit c4)) ▸
       at 5 2 (Toff324 ∷ Sw14 ∷ []) (wl0864 (lit c4)) ▸ done

  b1 : Chain (CCZ123 ∷ Toff213 ∷ CCZ234 ∷ Toff324 ∷ Bx2-30 ∷ Toff324 ∷ Sw14 ∷ CCZ123 ∷ Bx2-30 ∷ Toff234 ∷ CCZ234 ∷ Bx3-210 ∷ Sw14 ∷ []) (CCZ123 ∷ Toff213 ∷ CCZ234 ∷ Toff324 ∷ Bx2-30 ∷ Toff324 ∷ CCZ234 ∷ Bx2-30 ∷ Toff213 ∷ CCZ123 ∷ CCZ234 ∷ Toff324 ∷ Bx2-30 ∷ Sw14 ∷ Toff312 ∷ CCZ123 ∷ Bx2-30 ∷ Sw14 ∷ [])
  b1 = at 6 2 (CCZ234 ∷ Sw14 ∷ []) (sym (wl0856 (lit c4))) ▸
       at 7 2 (Bx2-30 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨2·30⟩ (lit c4)) ▸
       at 8 2 (Toff213 ∷ Sw14 ∷ []) (wl0865 (lit c4)) ▸
       at 9 2 (CCZ123 ∷ Sw14 ∷ []) (sym (wl0854 (lit c4))) ▸
       at 11 1 (CCZ123 ∷ Toff312 ∷ Bx2-30 ∷ Toff312 ∷ CCZ123 ∷ Bx2-30 ∷ []) (refl) ▸
       at 10 2 (CCZ234 ∷ Sw14 ∷ []) (sym (wl0856 (lit c4))) ▸
       at 11 2 (Toff324 ∷ Sw14 ∷ []) (wl0864 (lit c4)) ▸
       at 12 2 (Bx2-30 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨2·30⟩ (lit c4)) ▸ done

  b2 : Chain (CCZ123 ∷ Toff213 ∷ CCZ234 ∷ Toff324 ∷ Bx2-30 ∷ Toff324 ∷ CCZ234 ∷ Bx2-30 ∷ Toff213 ∷ CCZ123 ∷ CCZ234 ∷ Toff324 ∷ Bx2-30 ∷ Sw14 ∷ Toff312 ∷ CCZ123 ∷ Bx2-30 ∷ Sw14 ∷ []) (Bx2-3140 ∷ [])
  b2 = at 13 2 (Toff324 ∷ Sw14 ∷ []) (wl0864 (lit c4)) ▸
       at 14 2 (CCZ234 ∷ Sw14 ∷ []) (sym (wl0856 (lit c4))) ▸
       at 15 2 (Bx2-30 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨2·30⟩ (lit c4)) ▸
       at 16 2 [] (wl0306 (lit c4)) ▸
       at 2 6 (Bx3-240 ∷ []) (refl) ▸
       at 5 6 (Bx3-240 ∷ []) (refl) ▸
       at 0 6 (Bx2-3140 ∷ []) (refl) ▸ done

-- cQ @02233440: 7 steps
lem-cQ-at02233440 : Ws → ⟪ (CCZ123 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ CCZ123 ∷ []) ⟫ʷ
lem-cQ-at02233440 c4 = run b0
  where
  b0 : Chain (CCZ123 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ123 ∷ [])
  b0 = at 0 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0242 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ CS12 ∷ []) (sym (wp0081 c4)) ▸
       at 3 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ CS23⁻ ∷ []) (sym (wp0091 c4)) ▸
       at 1 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 0 2 (CCZ024 ∷ CS23 ∷ []) (sym (wp0092 c4)) ▸
       at 1 5 (CCZ123 ∷ []) (sym (wl0242 (lit c4))) ▸ done

-- cQ @0213213440: 7 steps
lem-cQ-at0213213440 : Ws → ⟪ (CCZ123 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ CCZ123 ∷ []) ⟫ʷ
lem-cQ-at0213213440 c4 = run b0
  where
  b0 : Chain (CCZ123 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ123 ∷ [])
  b0 = at 0 1 (CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ []) (wl0297 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ CS23 ∷ []) (sym (wp0092 c4)) ▸
       at 3 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ CS12⁻ ∷ []) (sym (wp0087 c4)) ▸
       at 1 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸
       at 0 2 (CCZ024 ∷ CS12 ∷ []) (sym (wp0081 c4)) ▸
       at 1 5 (CCZ123 ∷ []) (sym (wl0297 (lit c4))) ▸ done

-- nat-SWbc @0213213440: 23 steps
lem-nat-SWbc-at0213213440 : Ws → ⟪ (Sw14 ∷ Bx2-3140 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3410 ∷ []) ⟫ʷ
lem-nat-SWbc-at0213213440 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw14 ∷ Bx2-3140 ∷ Sw14 ∷ []) (CCZ234 ∷ Toff234 ∷ CCZ123 ∷ Toff312 ∷ Bx2-30 ∷ Toff312 ∷ Sw14 ∷ CCZ234 ∷ Bx2-30 ∷ Toff213 ∷ CCZ123 ∷ Bx3-240 ∷ Sw14 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff213 ∷ Bx3-240 ∷ Toff213 ∷ CCZ123 ∷ Bx3-240 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw14 ∷ []) (sym (wl0856 (lit c4))) ▸
       at 1 2 (Toff234 ∷ Sw14 ∷ []) (wl0857 (lit c4)) ▸
       at 3 1 (CCZ234 ∷ Toff324 ∷ Bx2-30 ∷ Toff324 ∷ CCZ234 ∷ Bx2-30 ∷ []) (refl) ▸
       at 2 2 (CCZ123 ∷ Sw14 ∷ []) (sym (wl0854 (lit c4))) ▸
       at 3 2 (Toff312 ∷ Sw14 ∷ []) (wl0855 (lit c4)) ▸
       at 4 2 (Bx2-30 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨2·30⟩ (lit c4)) ▸
       at 5 2 (Toff312 ∷ Sw14 ∷ []) (wl0855 (lit c4)) ▸ done

  b1 : Chain (CCZ234 ∷ Toff234 ∷ CCZ123 ∷ Toff312 ∷ Bx2-30 ∷ Toff312 ∷ Sw14 ∷ CCZ234 ∷ Bx2-30 ∷ Toff213 ∷ CCZ123 ∷ Bx3-240 ∷ Sw14 ∷ []) (CCZ234 ∷ Toff234 ∷ CCZ123 ∷ Toff312 ∷ Bx2-30 ∷ Toff312 ∷ CCZ123 ∷ Bx2-30 ∷ Toff234 ∷ CCZ234 ∷ CCZ123 ∷ Toff312 ∷ Bx2-30 ∷ Sw14 ∷ Toff324 ∷ CCZ234 ∷ Bx2-30 ∷ Sw14 ∷ [])
  b1 = at 6 2 (CCZ123 ∷ Sw14 ∷ []) (sym (wl0854 (lit c4))) ▸
       at 7 2 (Bx2-30 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨2·30⟩ (lit c4)) ▸
       at 8 2 (Toff234 ∷ Sw14 ∷ []) (wl0857 (lit c4)) ▸
       at 9 2 (CCZ234 ∷ Sw14 ∷ []) (sym (wl0856 (lit c4))) ▸
       at 11 1 (CCZ234 ∷ Toff324 ∷ Bx2-30 ∷ Toff324 ∷ CCZ234 ∷ Bx2-30 ∷ []) (refl) ▸
       at 10 2 (CCZ123 ∷ Sw14 ∷ []) (sym (wl0854 (lit c4))) ▸
       at 11 2 (Toff312 ∷ Sw14 ∷ []) (wl0855 (lit c4)) ▸
       at 12 2 (Bx2-30 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨2·30⟩ (lit c4)) ▸ done

  b2 : Chain (CCZ234 ∷ Toff234 ∷ CCZ123 ∷ Toff312 ∷ Bx2-30 ∷ Toff312 ∷ CCZ123 ∷ Bx2-30 ∷ Toff234 ∷ CCZ234 ∷ CCZ123 ∷ Toff312 ∷ Bx2-30 ∷ Sw14 ∷ Toff324 ∷ CCZ234 ∷ Bx2-30 ∷ Sw14 ∷ []) (Bx2-3410 ∷ [])
  b2 = at 13 2 (Toff312 ∷ Sw14 ∷ []) (wl0855 (lit c4)) ▸
       at 14 2 (CCZ123 ∷ Sw14 ∷ []) (sym (wl0854 (lit c4))) ▸
       at 15 2 (Bx2-30 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨2·30⟩ (lit c4)) ▸
       at 16 2 [] (wl0306 (lit c4)) ▸
       at 2 6 (Bx3-210 ∷ []) (refl) ▸
       at 5 6 (Bx3-210 ∷ []) (refl) ▸
       at 0 6 (Bx2-3410 ∷ []) (refl) ▸ done

-- tP @0213243140: 7 steps
lem-tP-at0213243140 : Ws → ⟪ (Toff234 ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ Toff234 ∷ []) ⟫ʷ
lem-tP-at0213243140 c4 = run b0
  where
  b0 : Chain (Toff234 ∷ Toff201 ∷ []) (Toff201 ∷ Toff234 ∷ [])
  b0 = at 0 1 (K2 ∷ CCZ234 ∷ K2⁻ ∷ []) (sym (wl0417 (lit c4))) ▸
       at 3 1 (K2 ∷ CCZ012 ∷ K2⁻ ∷ []) (sym (wl0416 (lit c4))) ▸
       at 2 2 [] (wl0175 (lit c4)) ▸
       at 1 2 (CCZ012 ∷ CCZ234 ∷ []) (lem-cQ-at0213243140 c4) ▸
       at 2 0 (K2⁻ ∷ K2 ∷ []) (sym (wl0175 (lit c4))) ▸
       at 0 3 (Toff201 ∷ []) (wl0416 (lit c4)) ▸
       at 1 3 (Toff234 ∷ []) (wl0417 (lit c4)) ▸ done

-- nat-SWbc @122331: 23 steps
lem-nat-SWbc-at122331 : Ws → ⟪ (Sw13 ∷ Bx0-2314 ∷ Sw13 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ []) ⟫ʷ
lem-nat-SWbc-at122331 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw13 ∷ Bx0-2314 ∷ Sw13 ∷ []) (CCZ012 ∷ Toff012 ∷ CCZ023 ∷ Toff203 ∷ Bx0-24 ∷ Toff203 ∷ Sw13 ∷ CCZ012 ∷ Bx0-24 ∷ Toff023 ∷ CCZ023 ∷ Bx2-014 ∷ Sw13 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff023 ∷ Bx2-014 ∷ Toff023 ∷ CCZ023 ∷ Bx2-014 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw13 ∷ []) (sym (wl0285 (lit c4))) ▸
       at 1 2 (Toff012 ∷ Sw13 ∷ []) (wl0989 (lit c4)) ▸
       at 3 1 (CCZ012 ∷ Toff201 ∷ Bx0-24 ∷ Toff201 ∷ CCZ012 ∷ Bx0-24 ∷ []) (refl) ▸
       at 2 2 (CCZ023 ∷ Sw13 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 3 2 (Toff203 ∷ Sw13 ∷ []) (wl0990 (lit c4)) ▸
       at 4 2 (Bx0-24 ∷ Sw13 ∷ []) (lem-comm-SWAP13-BOX⟨0·24⟩ (lit c4)) ▸
       at 5 2 (Toff203 ∷ Sw13 ∷ []) (wl0990 (lit c4)) ▸ done

  b1 : Chain (CCZ012 ∷ Toff012 ∷ CCZ023 ∷ Toff203 ∷ Bx0-24 ∷ Toff203 ∷ Sw13 ∷ CCZ012 ∷ Bx0-24 ∷ Toff023 ∷ CCZ023 ∷ Bx2-014 ∷ Sw13 ∷ []) (CCZ012 ∷ Toff012 ∷ CCZ023 ∷ Toff203 ∷ Bx0-24 ∷ Toff203 ∷ CCZ023 ∷ Bx0-24 ∷ Toff012 ∷ CCZ012 ∷ CCZ023 ∷ Toff203 ∷ Bx0-24 ∷ Sw13 ∷ Toff201 ∷ CCZ012 ∷ Bx0-24 ∷ Sw13 ∷ [])
  b1 = at 6 2 (CCZ023 ∷ Sw13 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 7 2 (Bx0-24 ∷ Sw13 ∷ []) (lem-comm-SWAP13-BOX⟨0·24⟩ (lit c4)) ▸
       at 8 2 (Toff012 ∷ Sw13 ∷ []) (wl0989 (lit c4)) ▸
       at 9 2 (CCZ012 ∷ Sw13 ∷ []) (sym (wl0285 (lit c4))) ▸
       at 11 1 (CCZ012 ∷ Toff201 ∷ Bx0-24 ∷ Toff201 ∷ CCZ012 ∷ Bx0-24 ∷ []) (refl) ▸
       at 10 2 (CCZ023 ∷ Sw13 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 2 (Toff203 ∷ Sw13 ∷ []) (wl0990 (lit c4)) ▸
       at 12 2 (Bx0-24 ∷ Sw13 ∷ []) (lem-comm-SWAP13-BOX⟨0·24⟩ (lit c4)) ▸ done

  b2 : Chain (CCZ012 ∷ Toff012 ∷ CCZ023 ∷ Toff203 ∷ Bx0-24 ∷ Toff203 ∷ CCZ023 ∷ Bx0-24 ∷ Toff012 ∷ CCZ012 ∷ CCZ023 ∷ Toff203 ∷ Bx0-24 ∷ Sw13 ∷ Toff201 ∷ CCZ012 ∷ Bx0-24 ∷ Sw13 ∷ []) (Bx0-2134 ∷ [])
  b2 = at 13 2 (Toff203 ∷ Sw13 ∷ []) (wl0990 (lit c4)) ▸
       at 14 2 (CCZ023 ∷ Sw13 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 15 2 (Bx0-24 ∷ Sw13 ∷ []) (lem-comm-SWAP13-BOX⟨0·24⟩ (lit c4)) ▸
       at 16 2 [] (wl0287 (lit c4)) ▸
       at 2 6 (Bx2-034 ∷ []) (refl) ▸
       at 5 6 (Bx2-034 ∷ []) (refl) ▸
       at 0 6 (Bx0-2134 ∷ []) (refl) ▸ done

-- nat-SWbc @2332: 23 steps
lem-nat-SWbc-at2332 : Ws → ⟪ (Sw23 ∷ Bx0-1324 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-nat-SWbc-at2332 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw23 ∷ Bx0-1324 ∷ Sw23 ∷ []) (CCZ012 ∷ Toff012 ∷ CCZ013 ∷ Toff103 ∷ Bx0-14 ∷ Toff103 ∷ Sw23 ∷ CCZ012 ∷ Bx0-14 ∷ Toff013 ∷ CCZ013 ∷ Bx1-024 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff013 ∷ Bx1-024 ∷ Toff013 ∷ CCZ013 ∷ Bx1-024 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw23 ∷ []) (sym (wl0266 (lit c4))) ▸
       at 1 2 (Toff012 ∷ Sw23 ∷ []) (wl1023 (lit c4)) ▸
       at 3 1 (CCZ012 ∷ Toff102 ∷ Bx0-14 ∷ Toff102 ∷ CCZ012 ∷ Bx0-14 ∷ []) (refl) ▸
       at 2 2 (CCZ013 ∷ Sw23 ∷ []) (sym (wl0264 (lit c4))) ▸
       at 3 2 (Toff103 ∷ Sw23 ∷ []) (wl1024 (lit c4)) ▸
       at 4 2 (Bx0-14 ∷ Sw23 ∷ []) (lem-comm-SWAP23-BOX⟨0·14⟩ (lit c4)) ▸
       at 5 2 (Toff103 ∷ Sw23 ∷ []) (wl1024 (lit c4)) ▸ done

  b1 : Chain (CCZ012 ∷ Toff012 ∷ CCZ013 ∷ Toff103 ∷ Bx0-14 ∷ Toff103 ∷ Sw23 ∷ CCZ012 ∷ Bx0-14 ∷ Toff013 ∷ CCZ013 ∷ Bx1-024 ∷ Sw23 ∷ []) (CCZ012 ∷ Toff012 ∷ CCZ013 ∷ Toff103 ∷ Bx0-14 ∷ Toff103 ∷ CCZ013 ∷ Bx0-14 ∷ Toff012 ∷ CCZ012 ∷ CCZ013 ∷ Toff103 ∷ Bx0-14 ∷ Sw23 ∷ Toff102 ∷ CCZ012 ∷ Bx0-14 ∷ Sw23 ∷ [])
  b1 = at 6 2 (CCZ013 ∷ Sw23 ∷ []) (sym (wl0264 (lit c4))) ▸
       at 7 2 (Bx0-14 ∷ Sw23 ∷ []) (lem-comm-SWAP23-BOX⟨0·14⟩ (lit c4)) ▸
       at 8 2 (Toff012 ∷ Sw23 ∷ []) (wl1023 (lit c4)) ▸
       at 9 2 (CCZ012 ∷ Sw23 ∷ []) (sym (wl0266 (lit c4))) ▸
       at 11 1 (CCZ012 ∷ Toff102 ∷ Bx0-14 ∷ Toff102 ∷ CCZ012 ∷ Bx0-14 ∷ []) (refl) ▸
       at 10 2 (CCZ013 ∷ Sw23 ∷ []) (sym (wl0264 (lit c4))) ▸
       at 11 2 (Toff103 ∷ Sw23 ∷ []) (wl1024 (lit c4)) ▸
       at 12 2 (Bx0-14 ∷ Sw23 ∷ []) (lem-comm-SWAP23-BOX⟨0·14⟩ (lit c4)) ▸ done

  b2 : Chain (CCZ012 ∷ Toff012 ∷ CCZ013 ∷ Toff103 ∷ Bx0-14 ∷ Toff103 ∷ CCZ013 ∷ Bx0-14 ∷ Toff012 ∷ CCZ012 ∷ CCZ013 ∷ Toff103 ∷ Bx0-14 ∷ Sw23 ∷ Toff102 ∷ CCZ012 ∷ Bx0-14 ∷ Sw23 ∷ []) (Bx0-1234 ∷ [])
  b2 = at 13 2 (Toff103 ∷ Sw23 ∷ []) (wl1024 (lit c4)) ▸
       at 14 2 (CCZ013 ∷ Sw23 ∷ []) (sym (wl0264 (lit c4))) ▸
       at 15 2 (Bx0-14 ∷ Sw23 ∷ []) (lem-comm-SWAP23-BOX⟨0·14⟩ (lit c4)) ▸
       at 16 2 [] (wl0003 (lit c4)) ▸
       at 2 6 (Bx1-034 ∷ []) (refl) ▸
       at 5 6 (Bx1-034 ∷ []) (refl) ▸
       at 0 6 (Bx0-1234 ∷ []) (refl) ▸ done

-- box-tQ @0210213443: 13 steps
lem-box-tQ-at0210213443 : Ws → ⟪ (Bx2-0143 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) ⟫ʷ
lem-box-tQ-at0210213443 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx2-0143 ∷ []) (CCZ012 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ012 ∷ CCZ024 ∷ Toff024 ∷ CZ03 ∷ Toff024 ∷ CCZ024 ∷ CZ03 ∷ [])
  b0 = at 0 1 (CCZ012 ∷ Toff201 ∷ Bx0-243 ∷ Toff201 ∷ CCZ012 ∷ Bx0-243 ∷ []) (refl) ▸
       at 2 1 (CCZ024 ∷ Toff024 ∷ Bx2-03 ∷ Toff024 ∷ CCZ024 ∷ Bx2-03 ∷ []) (refl) ▸
       at 4 1 (CZ03 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 2 6 (CCZ234 ∷ []) (wp0305 c4) ▸
       at 5 1 (CCZ024 ∷ Toff024 ∷ Bx2-03 ∷ Toff024 ∷ CCZ024 ∷ Bx2-03 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 10 1 (CZ03 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ012 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ012 ∷ CCZ024 ∷ Toff024 ∷ CZ03 ∷ Toff024 ∷ CCZ024 ∷ CZ03 ∷ []) (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ [])
  b1 = at 5 6 (CCZ234 ∷ []) (wp0305 c4) ▸
       at 0 2 (Toff201 ∷ CCZ012 ∷ CZ01 ∷ []) (wl0930 (lit c4)) ▸
       at 2 2 (CCZ234 ∷ CZ01 ∷ []) (c₂ (CZ) (CCZ)) ▸
       at 1 2 (CCZ234 ∷ CCZ012 ∷ []) (lem-cQ-at0210213443 c4) ▸
       at 2 4 (Toff201 ∷ []) (wl0931 (lit c4)) ▸ done

-- box-perm-2134 @03102132: 1 steps
lem-box-perm-2134-at03102132 : Ws → ⟪ (Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1024 ∷ []) ⟫ʷ
lem-box-perm-2134-at03102132 c4 = run b0
  where
  b0 : Chain (Bx3-0124 ∷ []) (Bx3-1024 ∷ [])
  b0 = at 0 1 (Bx3-1024 ∷ []) (lem-sym-ab-at03102132 c4) ▸ done

-- box-tQ @03102132: 13 steps
lem-box-tQ-at03102132 : Ws → ⟪ (Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ []) ⟫ʷ
lem-box-tQ-at03102132 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-0124 ∷ []) (CCZ013 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ013 ∷ CCZ023 ∷ Toff023 ∷ CZ04 ∷ Toff023 ∷ CCZ023 ∷ CZ04 ∷ [])
  b0 = at 0 1 (CCZ013 ∷ Toff301 ∷ Bx0-324 ∷ Toff301 ∷ CCZ013 ∷ Bx0-324 ∷ []) (refl) ▸
       at 2 1 (CCZ023 ∷ Toff023 ∷ Bx3-04 ∷ Toff023 ∷ CCZ023 ∷ Bx3-04 ∷ []) (refl) ▸
       at 4 1 (CZ04 ∷ []) (refl) ▸
       at 7 1 (CZ04 ∷ []) (refl) ▸
       at 2 6 (CCZ234 ∷ []) (wp0280 c4) ▸
       at 5 1 (CCZ023 ∷ Toff023 ∷ Bx3-04 ∷ Toff023 ∷ CCZ023 ∷ Bx3-04 ∷ []) (refl) ▸
       at 7 1 (CZ04 ∷ []) (refl) ▸
       at 10 1 (CZ04 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ013 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ013 ∷ CCZ023 ∷ Toff023 ∷ CZ04 ∷ Toff023 ∷ CCZ023 ∷ CZ04 ∷ []) (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ [])
  b1 = at 5 6 (CCZ234 ∷ []) (wp0280 c4) ▸
       at 0 2 (Toff301 ∷ CCZ013 ∷ CZ01 ∷ []) (wl0519 (lit c4)) ▸
       at 2 2 (CCZ234 ∷ CZ01 ∷ []) (c₂ (CZ) (CCZ)) ▸
       at 1 2 (CCZ234 ∷ CCZ013 ∷ []) (lem-cQ-at03102132 c4) ▸
       at 2 4 (Toff301 ∷ []) (wl0520 (lit c4)) ▸ done

-- nat-SWbc @03102132: 23 steps
lem-nat-SWbc-at03102132 : Ws → ⟪ (Sw12 ∷ Bx3-0124 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0214 ∷ []) ⟫ʷ
lem-nat-SWbc-at03102132 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw12 ∷ Bx3-0124 ∷ Sw12 ∷ []) (CCZ023 ∷ Toff302 ∷ CCZ013 ∷ Toff013 ∷ Bx3-04 ∷ Toff013 ∷ Sw12 ∷ CCZ023 ∷ Bx3-04 ∷ Toff301 ∷ CCZ013 ∷ Bx0-324 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff301 ∷ Bx0-324 ∷ Toff301 ∷ CCZ013 ∷ Bx0-324 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw12 ∷ []) (sym (wl0840 (lit c4))) ▸
       at 1 2 (Toff302 ∷ Sw12 ∷ []) (wl0841 (lit c4)) ▸
       at 3 1 (CCZ023 ∷ Toff023 ∷ Bx3-04 ∷ Toff023 ∷ CCZ023 ∷ Bx3-04 ∷ []) (refl) ▸
       at 2 2 (CCZ013 ∷ Sw12 ∷ []) (sym (wl0838 (lit c4))) ▸
       at 3 2 (Toff013 ∷ Sw12 ∷ []) (wl0839 (lit c4)) ▸
       at 4 2 (Bx3-04 ∷ Sw12 ∷ []) (lem-comm-SWAP12-BOX⟨3·04⟩ (lit c4)) ▸
       at 5 2 (Toff013 ∷ Sw12 ∷ []) (wl0839 (lit c4)) ▸ done

  b1 : Chain (CCZ023 ∷ Toff302 ∷ CCZ013 ∷ Toff013 ∷ Bx3-04 ∷ Toff013 ∷ Sw12 ∷ CCZ023 ∷ Bx3-04 ∷ Toff301 ∷ CCZ013 ∷ Bx0-324 ∷ Sw12 ∷ []) (CCZ023 ∷ Toff302 ∷ CCZ013 ∷ Toff013 ∷ Bx3-04 ∷ Toff013 ∷ CCZ013 ∷ Bx3-04 ∷ Toff302 ∷ CCZ023 ∷ CCZ013 ∷ Toff013 ∷ Bx3-04 ∷ Sw12 ∷ Toff023 ∷ CCZ023 ∷ Bx3-04 ∷ Sw12 ∷ [])
  b1 = at 6 2 (CCZ013 ∷ Sw12 ∷ []) (sym (wl0838 (lit c4))) ▸
       at 7 2 (Bx3-04 ∷ Sw12 ∷ []) (lem-comm-SWAP12-BOX⟨3·04⟩ (lit c4)) ▸
       at 8 2 (Toff302 ∷ Sw12 ∷ []) (wl0841 (lit c4)) ▸
       at 9 2 (CCZ023 ∷ Sw12 ∷ []) (sym (wl0840 (lit c4))) ▸
       at 11 1 (CCZ023 ∷ Toff023 ∷ Bx3-04 ∷ Toff023 ∷ CCZ023 ∷ Bx3-04 ∷ []) (refl) ▸
       at 10 2 (CCZ013 ∷ Sw12 ∷ []) (sym (wl0838 (lit c4))) ▸
       at 11 2 (Toff013 ∷ Sw12 ∷ []) (wl0839 (lit c4)) ▸
       at 12 2 (Bx3-04 ∷ Sw12 ∷ []) (lem-comm-SWAP12-BOX⟨3·04⟩ (lit c4)) ▸ done

  b2 : Chain (CCZ023 ∷ Toff302 ∷ CCZ013 ∷ Toff013 ∷ Bx3-04 ∷ Toff013 ∷ CCZ013 ∷ Bx3-04 ∷ Toff302 ∷ CCZ023 ∷ CCZ013 ∷ Toff013 ∷ Bx3-04 ∷ Sw12 ∷ Toff023 ∷ CCZ023 ∷ Bx3-04 ∷ Sw12 ∷ []) (Bx3-0214 ∷ [])
  b2 = at 13 2 (Toff013 ∷ Sw12 ∷ []) (wl0839 (lit c4)) ▸
       at 14 2 (CCZ013 ∷ Sw12 ∷ []) (sym (wl0838 (lit c4))) ▸
       at 15 2 (Bx3-04 ∷ Sw12 ∷ []) (lem-comm-SWAP12-BOX⟨3·04⟩ (lit c4)) ▸
       at 16 2 [] (wl0006 (lit c4)) ▸
       at 2 6 (Bx0-314 ∷ []) (refl) ▸
       at 5 6 (Bx0-314 ∷ []) (refl) ▸
       at 0 6 (Bx3-0214 ∷ []) (refl) ▸ done

-- cQ @022440: 7 steps
lem-cQ-at022440 : Ws → ⟪ (CCZ124 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ CCZ124 ∷ []) ⟫ʷ
lem-cQ-at022440 c4 = run b0
  where
  b0 : Chain (CCZ124 ∷ CCZ023 ∷ []) (CCZ023 ∷ CCZ124 ∷ [])
  b0 = at 0 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 4 2 (CCZ023 ∷ CS12 ∷ []) (sym (wl0621 (lit c4))) ▸
       at 3 2 (CCZ023 ∷ CX14 ∷ []) (lem-comm-CX14-CCZ023 (lit c4)) ▸
       at 2 2 (CCZ023 ∷ CS24⁻ ∷ []) (sym (wp0820 c4)) ▸
       at 1 2 (CCZ023 ∷ CX14 ∷ []) (lem-comm-CX14-CCZ023 (lit c4)) ▸
       at 0 2 (CCZ023 ∷ CS24 ∷ []) (sym (wp0513 c4)) ▸
       at 1 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸ done

-- cQ @02102441: 7 steps
lem-cQ-at02102441 : Ws → ⟪ (CCZ024 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CCZ024 ∷ []) ⟫ʷ
lem-cQ-at02102441 c4 = run b0
  where
  b0 : Chain (CCZ024 ∷ CCZ123 ∷ []) (CCZ123 ∷ CCZ024 ∷ [])
  b0 = at 0 1 (CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ []) (wp0013 c4) ▸
       at 4 2 (CCZ123 ∷ CS02 ∷ []) (sym (wl0171 (lit c4))) ▸
       at 3 2 (CCZ123 ∷ CX04 ∷ []) (lem-comm-CX04-CCZ123 (lit c4)) ▸
       at 2 2 (CCZ123 ∷ CS24⁻ ∷ []) (sym (wl0172 (lit c4))) ▸
       at 1 2 (CCZ123 ∷ CX04 ∷ []) (lem-comm-CX04-CCZ123 (lit c4)) ▸
       at 0 2 (CCZ123 ∷ CS24 ∷ []) (sym (wl0173 (lit c4))) ▸
       at 1 5 (CCZ024 ∷ []) (sym (wp0013 c4)) ▸ done
