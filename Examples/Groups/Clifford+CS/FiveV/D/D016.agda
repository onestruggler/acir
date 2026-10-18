{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.FiveV.D.D016 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.FiveV.WinSig using (Ws ; lit ; wl0004 ; wl0174 ; wl0175 ; wl0176 ; wl0177 ; wl0178 ; wl0179 ; wl0180 ; wl0181 ; wl0186 ; wl0190 ; wl0191 ; wl0193 ; wl0194 ; wl0195 ; wl0196 ; wl0197 ; wl0199 ; wl0204 ; wl0217 ; wl0219 ; wl0220 ; wl0221 ; wl0222 ; wl0230 ; wl0241 ; wl0244 ; wl0245 ; wl0246 ; wl0247 ; wl0263 ; wl0280 ; wl0289 ; wl0305 ; wl0547 ; wl0610 ; wl0621 ; wl0622 ; wl0623 ; wl0624 ; wl0625 ; wl0629 ; wl0630 ; wl0631 ; wl0632 ; wl0633 ; wl0634 ; wl0635 ; wl0636 ; wl0649 ; wl0671 ; wl0727 ; wl0747 ; wl0912 ; wl0913 ; wl0914 ; wl0944 ; wl0947 ; wl1000 ; wl1037 ; wl1117 ; wl1118 ; wl1119 ; wl1120 ; wl1121 ; wl1122 ; wl1123 ; wl1124 ; wl1125 ; wl1126 ; wl1127 ; wl1128 ; wl1129 ; wl1130 ; wl1131 ; wl1132 ; wl1133 ; wl1134 ; wl1135 ; wl1136 ; wl1137 ; wl1138 ; wp0014 ; wp0015 ; wp0016 ; wp0017 ; wp0018 ; wp0019 ; wp0021 ; wp0024 ; wp0032 ; wp0033 ; wp0034 ; wp0035 ; wp0036 ; wp0037 ; wp0038 ; wp0039 ; wp0041 ; wp0042 ; wp0044 ; wp0046 ; wp0047 ; wp0048 ; wp0053 ; wp0060 ; wp0061 ; wp0062 ; wp0063 ; wp0064 ; wp0065 ; wp0066 ; wp0069 ; wp0070 ; wp0072 ; wp0074 ; wp0081 ; wp0087 ; wp0088 ; wp0089 ; wp0090 ; wp0094 ; wp0095 ; wp0097 ; wp0135 ; wp0161 ; wp0513 ; wp0514 ; wp0523 ; wp0610 ; wp0617 ; wp0651 ; wp0654 ; wp0669 ; wp0680 ; wp0767 ; wp0780 ; wp0781 ; wp0782 ; wp0805 ; wp0806 ; wp0810 ; wp0820 ; wp0842 ; wp0843 ; wp0845 ; wp0906 ; wp0911 ; wp0912 ; wp0913 ; wp0914 ; wp0915 ; wp0916 ; wp0917 ; wp0918 ; wp0919 ; wp0920 ; wp0921 ; wp0922 ; wp0923 ; wp0924 ; wp0925 ; wp0926 ; wp0927 ; wp0928 ; wp0929 ; wp0930 ; wp0931 ; wp0932)
open import Examples.Groups.Clifford+CS.FiveV.Chain
open import Examples.Groups.Clifford+CS.FiveV.D.D001 using (lem-box-cP-at0210243143 ; lem-box-cP-at122441 ; lem-box-cP-at243243)
open import Examples.Groups.Clifford+CS.FiveV.D.D003 using (lem-sym-ab-at243243)
open import Examples.Groups.Clifford+CS.FiveV.D.D006 using (lem-box-tQ-at0214203143 ; lem-cQ-at0214203143 ; lem-sym-ab-at0210243143)
open import Examples.Groups.Clifford+CS.FiveV.D.D009 using (lem-sym-ab-at0214203143)
open import Examples.Groups.Clifford+CS.FiveV.D.D010 using (lem-box-tQ-at02233440 ; lem-cQ-at02233440)
open import Examples.Groups.Clifford+CS.FiveV.D.D012 using (lem-pairs-at14213243 ; lem-sym-bc-at12233441)
open import Examples.Groups.Clifford+CS.FiveV.D.D014 using (lem-S2-SBOX⟨2·0·41·3⟩)
open import Examples.Groups.Clifford+CS.FiveV.D.D015 using (lem-nf-comm-CS-S1at1)
open import Examples.Groups.Clifford+CS.FiveV.D.R001 using (lem-comm-CSd04-TOFF213 ; lem-comm-CX13-CCZ024 ; lem-comm-CX14-CCZ023 ; lem-comm-CZ04-TOFF213 ; lem-comm-TOFF204-CSd13)
open import Examples.Groups.Clifford+CS.FiveV.D.R002 using (lem-comm-CZ14-CCZ023)
open import Examples.Groups.Clifford+CS.FiveV.D.R003 using (lem-comm-CS03-CCZ124 ; lem-comm-CS04-TOFF213 ; lem-comm-CSd03-CCZ124)
open import Examples.Groups.Clifford+CS.FiveV.D.R004 using (lem-comm-CCZ024-CX13 ; lem-comm-CS03-TOFF214 ; lem-comm-CSd03-TOFF214 ; lem-comm-CSd13-TOFF204 ; lem-comm-CSd14-TOFF203 ; lem-comm-CZ13-TOFF204 ; lem-comm-TOFF213-CK40 ; lem-comm-TOFF213-CSd04 ; lem-comm-TOFF213-CX04 ; lem-comm-TOFF214-CSd03)
open import Examples.Groups.Clifford+CS.FiveV.D.R005 using (lem-comm-CCZ014-CX23 ; lem-comm-TOFF013-CX24 ; lem-comm-TOFF023-CX14 ; lem-comm-TOFF213-CS04)
-- F1-comm-CS-S1@1: 91 steps
lem-F1-comm-CS-S1at1 : Ws → ⟪ (Sb0-1-42-3 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-F1-comm-CS-S1at1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (run b11)))))))))))
  where
  b0 : Chain (Sb0-1-42-3 ∷ CS24 ∷ []) (CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ124 ∷ K3 ∷ CCZ014 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CS24 ∷ [])
  b0 = at 0 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 2 1 (CS13 ∷ []) (refl) ▸
       at 4 1 (CS13⁻ ∷ []) (refl) ▸
       at 0 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 3 2 (Toff024 ∷ Toff324 ∷ Toff023 ∷ []) (wp0805 c4) ▸
       at 2 2 (Toff024 ∷ CCZ124 ∷ CCZ014 ∷ []) (wp0806 c4) ▸
       at 5 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 4 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸ done

  b1 : Chain (CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ124 ∷ K3 ∷ CCZ014 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CS24 ∷ []) (CCZ014 ∷ Toff024 ∷ Toff023 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CS24 ∷ [])
  b1 = at 5 2 (CS34 ∷ CCZ014 ∷ []) (wp0064 c4) ▸
       at 6 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 7 2 (CS34⁻ ∷ CCZ014 ∷ []) (wp0063 c4) ▸
       at 8 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 9 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸
       at 10 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸
       at 4 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 1 2 (Toff024 ∷ Toff023 ∷ []) (wp0072 c4) ▸ done

  b2 : Chain (CCZ014 ∷ Toff024 ∷ Toff023 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CS24 ∷ []) (CCZ014 ∷ Toff024 ∷ CCZ124 ∷ Toff024 ∷ Toff324 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CS24 ∷ [])
  b2 = at 3 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 2 2 (CS24 ∷ Toff023 ∷ []) (sym (wp0070 c4)) ▸
       at 3 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 4 2 (CS24⁻ ∷ Toff023 ∷ []) (sym (wp0069 c4)) ▸
       at 5 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 6 2 (CS12 ∷ Toff023 ∷ []) (sym (wl0221 (lit c4))) ▸
       at 2 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 3 2 (Toff024 ∷ Toff324 ∷ Toff023 ∷ []) (wp0805 c4) ▸ done

  b3 : Chain (CCZ014 ∷ Toff024 ∷ CCZ124 ∷ Toff024 ∷ Toff324 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CS24 ∷ []) (CCZ124 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CCZ014 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CS24 ∷ [])
  b3 = at 1 3 (CCZ124 ∷ []) (sym (wp0074 c4)) ▸
       at 0 2 (CCZ124 ∷ CCZ014 ∷ []) (wp0066 c4) ▸
       at 2 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 1 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸
       at 2 2 (CS34 ∷ CCZ014 ∷ []) (wp0064 c4) ▸
       at 3 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 4 2 (CS34⁻ ∷ CCZ014 ∷ []) (wp0063 c4) ▸
       at 5 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸ done

  b4 : Chain (CCZ124 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CCZ014 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CS24 ∷ []) (CCZ124 ∷ Toff324 ∷ CCZ014 ∷ CS13 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13⁻ ∷ CS24 ∷ [])
  b4 = at 6 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸
       at 7 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸
       at 1 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 2 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 2 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 5 2 (CS13 ∷ Toff023 ∷ []) (sym (wl0222 (lit c4))) ▸
       at 4 2 (CS13 ∷ CCZ014 ∷ []) (wp0053 c4) ▸
       at 3 2 (CS13 ∷ Toff023 ∷ []) (sym (wl0222 (lit c4))) ▸ done

  b5 : Chain (CCZ124 ∷ Toff324 ∷ CCZ014 ∷ CS13 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13⁻ ∷ CS24 ∷ []) (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CCZ014 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CS13⁻ ∷ CS24 ∷ [])
  b5 = at 2 2 (CS13 ∷ CCZ014 ∷ []) (wp0053 c4) ▸
       at 3 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 3 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 6 2 (Toff024 ∷ Toff324 ∷ Toff023 ∷ []) (wp0805 c4) ▸
       at 5 2 (Toff024 ∷ CCZ124 ∷ CCZ014 ∷ []) (wp0806 c4) ▸
       at 8 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 7 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸
       at 8 2 (CS34 ∷ CCZ014 ∷ []) (wp0064 c4) ▸ done

  b6 : Chain (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CCZ014 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CS13⁻ ∷ CS24 ∷ []) (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff024 ∷ Toff023 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ CS24 ∷ [])
  b6 = at 9 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 10 2 (CS34⁻ ∷ CCZ014 ∷ []) (wp0063 c4) ▸
       at 11 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 12 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸
       at 13 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸
       at 7 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 4 2 (Toff024 ∷ Toff023 ∷ []) (wp0072 c4) ▸
       at 6 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸ done

  b7 : Chain (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff024 ∷ Toff023 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ CS24 ∷ []) (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ CCZ124 ∷ Toff324 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ CS24 ∷ [])
  b7 = at 5 2 (CS24 ∷ Toff023 ∷ []) (sym (wp0070 c4)) ▸
       at 6 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 7 2 (CS24⁻ ∷ Toff023 ∷ []) (sym (wp0069 c4)) ▸
       at 8 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 9 2 (CS12 ∷ Toff023 ∷ []) (sym (wl0221 (lit c4))) ▸
       at 5 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 6 2 (Toff024 ∷ Toff324 ∷ Toff023 ∷ []) (wp0805 c4) ▸
       at 4 3 (CCZ124 ∷ []) (sym (wp0074 c4)) ▸ done

  b8 : Chain (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ CCZ124 ∷ Toff324 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ CS24 ∷ []) (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ CCZ014 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ CS24 ∷ [])
  b8 = at 3 2 (CCZ124 ∷ CCZ014 ∷ []) (wp0066 c4) ▸
       at 5 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 4 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸
       at 5 2 (CS34 ∷ CCZ014 ∷ []) (wp0064 c4) ▸
       at 6 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 7 2 (CS34⁻ ∷ CCZ014 ∷ []) (wp0063 c4) ▸
       at 8 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 9 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸ done

  b9 : Chain (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ CCZ014 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ CS24 ∷ []) (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS24 ∷ [])
  b9 = at 10 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸
       at 4 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 5 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 5 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 8 2 (CS13⁻ ∷ Toff023 ∷ []) (sym (wl0219 (lit c4))) ▸
       at 7 2 (CS13⁻ ∷ CCZ014 ∷ []) (wp0060 c4) ▸
       at 6 2 (CS13⁻ ∷ Toff023 ∷ []) (sym (wl0219 (lit c4))) ▸
       at 5 2 (CS13⁻ ∷ CCZ014 ∷ []) (wp0060 c4) ▸ done

  b10 : Chain (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS24 ∷ []) (Toff324 ∷ CS13 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CS24 ∷ Bx0-1423 ∷ [])
  b10 = at 6 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 6 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 9 2 (CS24 ∷ Toff023 ∷ []) (sym (wp0070 c4)) ▸
       at 8 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸
       at 7 2 (CS24 ∷ Toff023 ∷ []) (sym (wp0070 c4)) ▸
       at 6 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸
       at 7 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 0 3 (Toff324 ∷ CS13 ∷ CCZ124 ∷ []) (wl1000 (lit c4)) ▸ done

  b11 : Chain (Toff324 ∷ CS13 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CS24 ∷ Bx0-1423 ∷ []) (CS24 ∷ Sb0-1-42-3 ∷ [])
  b11 = at 2 2 [] (wl0263 (lit c4)) ▸
       at 0 5 (CS24 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (sym (wl1117 (lit c4))) ▸
       at 0 6 (CS24 ∷ Sb0-1-42-3 ∷ []) (sym (lem-nf-comm-CS-S1at1 c4)) ▸ done


-- nf-comm-CS-S1@2: 83 steps
lem-nf-comm-CS-S1at2 : Ws → ⟪ (CS34 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ []) ⟫ʷ
lem-nf-comm-CS-S1at2 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (run b10))))))))))
  where
  b0 : Chain (CS34 ∷ Sb0-2-43-1 ∷ []) (CS34 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ K1 ∷ CCZ024 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b0 = at 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 3 1 (CS12 ∷ []) (refl) ▸
       at 5 1 (CS12⁻ ∷ []) (refl) ▸
       at 1 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 4 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp0843 c4) ▸
       at 3 2 (Toff034 ∷ CCZ234 ∷ CCZ024 ∷ []) (wp0845 c4) ▸
       at 6 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 5 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸ done

  b1 : Chain (CS34 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ K1 ∷ CCZ024 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (CS34 ∷ CCZ024 ∷ Toff034 ∷ Toff013 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b1 = at 6 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 7 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 8 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 9 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 10 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 11 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 5 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 2 2 (Toff034 ∷ Toff013 ∷ []) (wp0097 c4) ▸ done

  b2 : Chain (CS34 ∷ CCZ024 ∷ Toff034 ∷ Toff013 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (CS34 ∷ CCZ024 ∷ Toff034 ∷ CCZ234 ∷ Toff034 ∷ Toff134 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b2 = at 4 1 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (wl0245 (lit c4)) ▸
       at 3 2 (CS34 ∷ Toff013 ∷ []) (sym (wp0095 c4)) ▸
       at 4 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 5 2 (CS34⁻ ∷ Toff013 ∷ []) (sym (wp0094 c4)) ▸
       at 6 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 7 2 (CS23 ∷ Toff013 ∷ []) (sym (wl0246 (lit c4))) ▸
       at 3 5 (CCZ234 ∷ []) (sym (wl0245 (lit c4))) ▸
       at 4 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp0843 c4) ▸ done

  b3 : Chain (CS34 ∷ CCZ024 ∷ Toff034 ∷ CCZ234 ∷ Toff034 ∷ Toff134 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (CS34 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b3 = at 2 3 (CCZ234 ∷ []) (sym (wp0842 c4)) ▸
       at 1 2 (CCZ234 ∷ CCZ024 ∷ []) (wp0090 c4) ▸
       at 3 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 2 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸
       at 3 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 4 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 5 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 6 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸ done

  b4 : Chain (CS34 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (CS34 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ CS12 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b4 = at 7 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 8 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 2 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 3 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 3 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 6 2 (CS12 ∷ Toff013 ∷ []) (sym (wl0247 (lit c4))) ▸
       at 5 2 (CS12 ∷ CCZ024 ∷ []) (wp0081 c4) ▸
       at 4 2 (CS12 ∷ Toff013 ∷ []) (sym (wl0247 (lit c4))) ▸ done

  b5 : Chain (CS34 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ CS12 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12⁻ ∷ []) (CS34 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CCZ024 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CS12⁻ ∷ [])
  b5 = at 3 2 (CS12 ∷ CCZ024 ∷ []) (wp0081 c4) ▸
       at 4 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 4 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 7 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp0843 c4) ▸
       at 6 2 (Toff034 ∷ CCZ234 ∷ CCZ024 ∷ []) (wp0845 c4) ▸
       at 9 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 8 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸
       at 9 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸ done

  b6 : Chain (CS34 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CCZ024 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CS12⁻ ∷ []) (CS34 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff034 ∷ Toff013 ∷ CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ [])
  b6 = at 10 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 11 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 12 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 13 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 14 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 8 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 5 2 (Toff034 ∷ Toff013 ∷ []) (wp0097 c4) ▸
       at 7 1 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (wl0245 (lit c4)) ▸ done

  b7 : Chain (CS34 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff034 ∷ Toff013 ∷ CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ []) (CS34 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ CCZ234 ∷ Toff134 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ [])
  b7 = at 6 2 (CS34 ∷ Toff013 ∷ []) (sym (wp0095 c4)) ▸
       at 7 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 8 2 (CS34⁻ ∷ Toff013 ∷ []) (sym (wp0094 c4)) ▸
       at 9 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 10 2 (CS23 ∷ Toff013 ∷ []) (sym (wl0246 (lit c4))) ▸
       at 6 5 (CCZ234 ∷ []) (sym (wl0245 (lit c4))) ▸
       at 7 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp0843 c4) ▸
       at 5 3 (CCZ234 ∷ []) (sym (wp0842 c4)) ▸ done

  b8 : Chain (CS34 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ CCZ234 ∷ Toff134 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ []) (CS34 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ CCZ024 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ [])
  b8 = at 4 2 (CCZ234 ∷ CCZ024 ∷ []) (wp0090 c4) ▸
       at 6 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 5 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸
       at 6 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 7 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 8 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 9 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 10 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸ done

  b9 : Chain (CS34 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ CCZ024 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ []) (CS34 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ [])
  b9 = at 11 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 5 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 6 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 6 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 9 2 (CS12⁻ ∷ Toff013 ∷ []) (sym (wl0244 (lit c4))) ▸
       at 8 2 (CS12⁻ ∷ CCZ024 ∷ []) (wp0087 c4) ▸
       at 7 2 (CS12⁻ ∷ Toff013 ∷ []) (sym (wl0244 (lit c4))) ▸
       at 6 2 (CS12⁻ ∷ CCZ024 ∷ []) (wp0087 c4) ▸ done

  b10 : Chain (CS34 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (CS34 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ [])
  b10 = at 7 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 1 3 (Toff134 ∷ CS12 ∷ CCZ234 ∷ []) (wl1037 (lit c4)) ▸
       at 3 2 [] (wl0305 (lit c4)) ▸ done


-- F1-comm-CS-S1@2: 91 steps
lem-F1-comm-CS-S1at2 : Ws → ⟪ (Sb0-2-43-1 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-F1-comm-CS-S1at2 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (run b11)))))))))))
  where
  b0 : Chain (Sb0-2-43-1 ∷ CS34 ∷ []) (CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ K1 ∷ CCZ024 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CS34 ∷ [])
  b0 = at 0 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 2 1 (CS12 ∷ []) (refl) ▸
       at 4 1 (CS12⁻ ∷ []) (refl) ▸
       at 0 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 3 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp0843 c4) ▸
       at 2 2 (Toff034 ∷ CCZ234 ∷ CCZ024 ∷ []) (wp0845 c4) ▸
       at 5 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 4 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸ done

  b1 : Chain (CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ K1 ∷ CCZ024 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CS34 ∷ []) (CCZ024 ∷ Toff034 ∷ Toff013 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CS34 ∷ [])
  b1 = at 5 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 6 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 7 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 8 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 9 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 10 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 4 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 1 2 (Toff034 ∷ Toff013 ∷ []) (wp0097 c4) ▸ done

  b2 : Chain (CCZ024 ∷ Toff034 ∷ Toff013 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CS34 ∷ []) (CCZ024 ∷ Toff034 ∷ CCZ234 ∷ Toff034 ∷ Toff134 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CS34 ∷ [])
  b2 = at 3 1 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (wl0245 (lit c4)) ▸
       at 2 2 (CS34 ∷ Toff013 ∷ []) (sym (wp0095 c4)) ▸
       at 3 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 4 2 (CS34⁻ ∷ Toff013 ∷ []) (sym (wp0094 c4)) ▸
       at 5 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 6 2 (CS23 ∷ Toff013 ∷ []) (sym (wl0246 (lit c4))) ▸
       at 2 5 (CCZ234 ∷ []) (sym (wl0245 (lit c4))) ▸
       at 3 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp0843 c4) ▸ done

  b3 : Chain (CCZ024 ∷ Toff034 ∷ CCZ234 ∷ Toff034 ∷ Toff134 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CS34 ∷ []) (CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CS34 ∷ [])
  b3 = at 1 3 (CCZ234 ∷ []) (sym (wp0842 c4)) ▸
       at 0 2 (CCZ234 ∷ CCZ024 ∷ []) (wp0090 c4) ▸
       at 2 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 1 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸
       at 2 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 3 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 4 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 5 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸ done

  b4 : Chain (CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CS34 ∷ []) (CCZ234 ∷ Toff134 ∷ CCZ024 ∷ CS12 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12⁻ ∷ CS34 ∷ [])
  b4 = at 6 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 7 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 1 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 2 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 2 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 5 2 (CS12 ∷ Toff013 ∷ []) (sym (wl0247 (lit c4))) ▸
       at 4 2 (CS12 ∷ CCZ024 ∷ []) (wp0081 c4) ▸
       at 3 2 (CS12 ∷ Toff013 ∷ []) (sym (wl0247 (lit c4))) ▸ done

  b5 : Chain (CCZ234 ∷ Toff134 ∷ CCZ024 ∷ CS12 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12⁻ ∷ CS34 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CCZ024 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CS12⁻ ∷ CS34 ∷ [])
  b5 = at 2 2 (CS12 ∷ CCZ024 ∷ []) (wp0081 c4) ▸
       at 3 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 3 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 6 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp0843 c4) ▸
       at 5 2 (Toff034 ∷ CCZ234 ∷ CCZ024 ∷ []) (wp0845 c4) ▸
       at 8 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 7 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸
       at 8 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸ done

  b6 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CCZ024 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CS12⁻ ∷ CS34 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff034 ∷ Toff013 ∷ CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ CS34 ∷ [])
  b6 = at 9 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 10 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 11 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 12 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 13 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 7 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 4 2 (Toff034 ∷ Toff013 ∷ []) (wp0097 c4) ▸
       at 6 1 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (wl0245 (lit c4)) ▸ done

  b7 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff034 ∷ Toff013 ∷ CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ CS34 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ CCZ234 ∷ Toff134 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ CS34 ∷ [])
  b7 = at 5 2 (CS34 ∷ Toff013 ∷ []) (sym (wp0095 c4)) ▸
       at 6 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 7 2 (CS34⁻ ∷ Toff013 ∷ []) (sym (wp0094 c4)) ▸
       at 8 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 9 2 (CS23 ∷ Toff013 ∷ []) (sym (wl0246 (lit c4))) ▸
       at 5 5 (CCZ234 ∷ []) (sym (wl0245 (lit c4))) ▸
       at 6 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp0843 c4) ▸
       at 4 3 (CCZ234 ∷ []) (sym (wp0842 c4)) ▸ done

  b8 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ CCZ234 ∷ Toff134 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ CS34 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ CCZ024 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ CS34 ∷ [])
  b8 = at 3 2 (CCZ234 ∷ CCZ024 ∷ []) (wp0090 c4) ▸
       at 5 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 4 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸
       at 5 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 6 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 7 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 8 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 9 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸ done

  b9 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ CCZ024 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ CS34 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS34 ∷ [])
  b9 = at 10 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 4 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 5 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 5 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 8 2 (CS12⁻ ∷ Toff013 ∷ []) (sym (wl0244 (lit c4))) ▸
       at 7 2 (CS12⁻ ∷ CCZ024 ∷ []) (wp0087 c4) ▸
       at 6 2 (CS12⁻ ∷ Toff013 ∷ []) (sym (wl0244 (lit c4))) ▸
       at 5 2 (CS12⁻ ∷ CCZ024 ∷ []) (wp0087 c4) ▸ done

  b10 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS34 ∷ []) (Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CS34 ∷ Bx0-2431 ∷ [])
  b10 = at 6 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 6 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 9 2 (CS34 ∷ Toff013 ∷ []) (sym (wp0095 c4)) ▸
       at 8 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 7 2 (CS34 ∷ Toff013 ∷ []) (sym (wp0095 c4)) ▸
       at 6 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 7 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 0 3 (Toff134 ∷ CS12 ∷ CCZ234 ∷ []) (wl1037 (lit c4)) ▸ done

  b11 : Chain (Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CS34 ∷ Bx0-2431 ∷ []) (CS34 ∷ Sb0-2-43-1 ∷ [])
  b11 = at 2 2 [] (wl0305 (lit c4)) ▸
       at 0 5 (CS34 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (sym (wl1118 (lit c4))) ▸
       at 0 6 (CS34 ∷ Sb0-2-43-1 ∷ []) (sym (lem-nf-comm-CS-S1at2 c4)) ▸ done


-- tP @0214203143: 7 steps
lem-tP-at0214203143 : Ws → ⟪ (Toff204 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ Toff204 ∷ []) ⟫ʷ
lem-tP-at0214203143 c4 = run b0
  where
  b0 : Chain (Toff204 ∷ Toff213 ∷ []) (Toff213 ∷ Toff204 ∷ [])
  b0 = at 0 1 (K2 ∷ CCZ024 ∷ K2⁻ ∷ []) (sym (wp0014 c4)) ▸
       at 3 1 (K2 ∷ CCZ123 ∷ K2⁻ ∷ []) (sym (wl0174 (lit c4))) ▸
       at 2 2 [] (wl0175 (lit c4)) ▸
       at 1 2 (CCZ123 ∷ CCZ024 ∷ []) (lem-cQ-at0214203143 c4) ▸
       at 2 0 (K2⁻ ∷ K2 ∷ []) (sym (wl0175 (lit c4))) ▸
       at 0 3 (Toff213 ∷ []) (wl0174 (lit c4)) ▸
       at 1 3 (Toff204 ∷ []) (wp0014 c4) ▸ done


-- P-box @0214203143: 8 steps
lem-P-box-at0214203143 : Ws → ⟪ (Toff213 ∷ Bx2-4013 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4013 ∷ []) ⟫ʷ
lem-P-box-at0214203143 c4 = run b0
  where
  b0 : Chain (Toff213 ∷ Bx2-4013 ∷ Toff213 ∷ []) (Bx2-4013 ∷ [])
  b0 = at 1 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-box-tQ-at0214203143 c4) ▸
       at 0 2 (Toff204 ∷ Toff213 ∷ []) (sym (lem-tP-at0214203143 c4)) ▸
       at 1 2 (CCZ123 ∷ CZ13 ∷ Toff213 ∷ []) (sym (wl0912 (lit c4))) ▸
       at 3 2 (Toff204 ∷ Toff213 ∷ []) (sym (lem-tP-at0214203143 c4)) ▸
       at 4 3 (CCZ123 ∷ CZ13 ∷ []) (sym (wl0913 (lit c4))) ▸
       at 2 2 (Toff204 ∷ CZ13 ∷ []) (lem-comm-CZ13-TOFF204 (lit c4)) ▸
       at 3 3 (CCZ123 ∷ []) (sym (wl0914 (lit c4))) ▸
       at 0 4 (Bx2-4013 ∷ []) (sym (lem-box-tQ-at0214203143 c4)) ▸ done


-- VPQ @0214203143: 14 steps
lem-VPQ-at0214203143 : Ws → ⟪ (Toff204 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ CCZ123 ∷ Toff204 ∷ CCZ024 ∷ []) ⟫ʷ
lem-VPQ-at0214203143 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff204 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ []) (CS13⁻ ∷ CS04⁻ ∷ S2 ∷ Toff213 ∷ Toff204 ∷ S2⁻ ∷ [])
  b0 = at 0 2 (CS04⁻ ∷ S2 ∷ Toff204 ∷ S2⁻ ∷ []) (sym (wp0015 c4)) ▸
       at 4 2 (CS13⁻ ∷ S2 ∷ Toff213 ∷ S2⁻ ∷ []) (sym (wl0176 (lit c4))) ▸
       at 3 2 (CS13⁻ ∷ S2⁻ ∷ []) (sym (wl0177 (lit c4))) ▸
       at 2 2 (CS13⁻ ∷ Toff204 ∷ []) (lem-comm-TOFF204-CSd13 (lit c4)) ▸
       at 1 2 (CS13⁻ ∷ S2 ∷ []) (sym (wl0178 (lit c4))) ▸
       at 0 2 (CS13⁻ ∷ CS04⁻ ∷ []) (wp0016 c4) ▸
       at 4 2 [] (wl0179 (lit c4)) ▸
       at 3 2 (Toff213 ∷ Toff204 ∷ []) (lem-tP-at0214203143 c4) ▸ done

  b1 : Chain (CS13⁻ ∷ CS04⁻ ∷ S2 ∷ Toff213 ∷ Toff204 ∷ S2⁻ ∷ []) (Toff213 ∷ CCZ123 ∷ Toff204 ∷ CCZ024 ∷ [])
  b1 = at 4 0 (S2⁻ ∷ S2 ∷ []) (sym (wl0179 (lit c4))) ▸
       at 1 2 (S2 ∷ CS04⁻ ∷ []) (wp0017 c4) ▸
       at 2 2 (Toff213 ∷ CS04⁻ ∷ []) (lem-comm-CSd04-TOFF213 (lit c4)) ▸
       at 3 2 (S2⁻ ∷ CS04⁻ ∷ []) (wp0018 c4) ▸
       at 0 4 (Toff213 ∷ CCZ123 ∷ []) (wl0176 (lit c4)) ▸
       at 2 4 (Toff204 ∷ CCZ024 ∷ []) (wp0015 c4) ▸ done


-- QVQ @0214203143: 3 steps
lem-QVQ-at0214203143 : Ws → ⟪ (CCZ123 ∷ Toff204 ∷ CCZ024 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ Toff204 ∷ CCZ024 ∷ Toff213 ∷ []) ⟫ʷ
lem-QVQ-at0214203143 c4 = run b0
  where
  b0 : Chain (CCZ123 ∷ Toff204 ∷ CCZ024 ∷ CCZ123 ∷ []) (Toff213 ∷ Toff204 ∷ CCZ024 ∷ Toff213 ∷ [])
  b0 = at 0 0 (Toff213 ∷ Toff213 ∷ []) (sym (wl0180 (lit c4))) ▸
       at 1 4 (Toff204 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ []) (sym (lem-VPQ-at0214203143 c4)) ▸
       at 4 2 [] (wl0181 (lit c4)) ▸ done


-- box-cP @0214203143: 12 steps
lem-box-cP-at0214203143 : Ws → ⟪ (Bx2-4013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) ⟫ʷ
lem-box-cP-at0214203143 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx2-4013 ∷ []) (CCZ024 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ024 ∷ CCZ124 ∷ Toff412 ∷ CZ34 ∷ Toff412 ∷ CCZ124 ∷ CZ34 ∷ [])
  b0 = at 0 1 (CCZ024 ∷ Toff204 ∷ Bx4-213 ∷ Toff204 ∷ CCZ024 ∷ Bx4-213 ∷ []) (refl) ▸
       at 2 1 (CCZ124 ∷ Toff412 ∷ Bx2-43 ∷ Toff412 ∷ CCZ124 ∷ Bx2-43 ∷ []) (refl) ▸
       at 4 1 (CZ34 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 2 6 (CCZ123 ∷ []) (sym (wl0610 (lit c4))) ▸
       at 5 1 (CCZ124 ∷ Toff412 ∷ Bx2-43 ∷ Toff412 ∷ CCZ124 ∷ Bx2-43 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 10 1 (CZ34 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ024 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ024 ∷ CCZ124 ∷ Toff412 ∷ CZ34 ∷ Toff412 ∷ CCZ124 ∷ CZ34 ∷ []) (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ [])
  b1 = at 5 6 (CCZ123 ∷ []) (sym (wl0610 (lit c4))) ▸
       at 2 4 (Toff213 ∷ Toff204 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-QVQ-at0214203143 c4) ▸
       at 1 2 (Toff213 ∷ Toff204 ∷ []) (lem-tP-at0214203143 c4) ▸
       at 2 2 [] (wp0019 c4) ▸ done


-- pairs @0214203143: 4 steps
lem-pairs-at0214203143 : Ws → ⟪ (Bx2-4013 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1340 ∷ []) ⟫ʷ
lem-pairs-at0214203143 c4 = run b0
  where
  b0 : Chain (Bx2-4013 ∷ []) (Bx2-1340 ∷ [])
  b0 = at 0 1 (Toff213 ∷ Bx2-4013 ∷ Toff213 ∷ []) (sym (lem-P-box-at0214203143 c4)) ▸
       at 1 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0214203143 c4) ▸
       at 4 2 [] (wl0180 (lit c4)) ▸
       at 0 4 (Bx2-1340 ∷ []) (sym (lem-box-tQ-at02233440 c4)) ▸ done


-- box-perm-3421 @0210243143: 2 steps
lem-box-perm-3421-at0210243143 : Ws → ⟪ (Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1340 ∷ []) ⟫ʷ
lem-box-perm-3421-at0210243143 c4 = run b0
  where
  b0 : Chain (Bx2-0413 ∷ []) (Bx2-1340 ∷ [])
  b0 = at 0 1 (Bx2-4013 ∷ []) (lem-sym-ab-at0210243143 c4) ▸
       at 0 1 (Bx2-1340 ∷ []) (lem-pairs-at0214203143 c4) ▸ done


-- CXbc-box @02233440: 17 steps
lem-CXbc-box-at02233440 : Ws → ⟪ (CX34 ∷ Bx2-1340 ∷ CX34 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1340 ∷ CCZ013 ∷ []) ⟫ʷ
lem-CXbc-box-at02233440 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX34 ∷ Bx2-1340 ∷ CX34 ∷ []) (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CX34 ∷ CCZ023 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CCZ024 ∷ CX13 ∷ CS01 ∷ CX34 ∷ [])
  b0 = at 1 1 (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ []) (lem-box-tQ-at02233440 c4) ▸
       at 0 2 (Toff213 ∷ CX34 ∷ []) (wl0947 (lit c4)) ▸
       at 1 2 (CCZ024 ∷ CX34 ∷ CCZ023 ∷ []) (sym (wp0911 c4)) ▸
       at 3 2 (Toff213 ∷ CCZ023 ∷ CCZ013 ∷ []) (wl1119 (lit c4)) ▸
       at 2 2 (Toff213 ∷ CX34 ∷ []) (wl0947 (lit c4)) ▸
       at 5 1 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (wl0289 (lit c4)) ▸
       at 9 2 (CCZ024 ∷ CS01 ∷ []) (sym (wp0039 c4)) ▸
       at 8 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸ done

  b1 : Chain (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CX34 ∷ CCZ023 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CCZ024 ∷ CX13 ∷ CS01 ∷ CX34 ∷ []) (Bx2-1340 ∷ CX34 ∷ CCZ013 ∷ CX34 ∷ [])
  b1 = at 7 2 (CCZ024 ∷ CS03⁻ ∷ []) (sym (wp0032 c4)) ▸
       at 6 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸
       at 6 5 (CCZ013 ∷ []) (sym (wl0289 (lit c4))) ▸
       at 4 2 (CCZ024 ∷ CCZ023 ∷ []) (wp0669 c4) ▸
       at 3 2 (CCZ024 ∷ CX34 ∷ CCZ023 ∷ []) (sym (wp0911 c4)) ▸
       at 4 3 (CX34 ∷ []) (wp0912 c4) ▸
       at 0 4 (Bx2-1340 ∷ []) (sym (lem-box-tQ-at02233440 c4)) ▸ done

  b2 : Chain (Bx2-1340 ∷ CX34 ∷ CCZ013 ∷ CX34 ∷ []) (Bx2-1340 ∷ CCZ013 ∷ [])
  b2 = at 1 3 (CCZ013 ∷ []) (sym (wp0913 c4)) ▸ done


-- CXcb-box @02233440: 18 steps
lem-CXcb-box-at02233440 : Ws → ⟪ (CX43 ∷ Bx2-1340 ∷ CX43 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1340 ∷ CCZ014 ∷ []) ⟫ʷ
lem-CXcb-box-at02233440 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX43 ∷ Bx2-1340 ∷ CX43 ∷ []) (Toff213 ∷ CCZ024 ∷ CX43 ∷ Toff214 ∷ CS04 ∷ CX14 ∷ Toff213 ∷ CS04⁻ ∷ CX14 ∷ CS01 ∷ CCZ024 ∷ CX43 ∷ [])
  b0 = at 1 1 (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ []) (lem-box-tQ-at02233440 c4) ▸
       at 0 2 (Toff213 ∷ CX43 ∷ Toff214 ∷ []) (wl1120 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ Toff214 ∷ CCZ014 ∷ []) (sym (wp0042 c4)) ▸
       at 1 2 (CCZ024 ∷ CX43 ∷ []) (sym (wp0914 c4)) ▸
       at 4 1 (CS04 ∷ CX14 ∷ CS04⁻ ∷ CX14 ∷ CS01 ∷ []) (wp0046 c4) ▸
       at 8 2 (Toff213 ∷ CS01 ∷ []) (wl0193 (lit c4)) ▸
       at 7 2 (Toff213 ∷ CX14 ∷ []) (wl0944 (lit c4)) ▸
       at 6 2 (Toff213 ∷ CS04⁻ ∷ []) (lem-comm-CSd04-TOFF213 (lit c4)) ▸ done

  b1 : Chain (Toff213 ∷ CCZ024 ∷ CX43 ∷ Toff214 ∷ CS04 ∷ CX14 ∷ Toff213 ∷ CS04⁻ ∷ CX14 ∷ CS01 ∷ CCZ024 ∷ CX43 ∷ []) (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ CX43 ∷ CCZ014 ∷ CX43 ∷ [])
  b1 = at 5 2 (Toff213 ∷ CX14 ∷ []) (wl0944 (lit c4)) ▸
       at 4 2 (Toff213 ∷ CS04 ∷ []) (lem-comm-CS04-TOFF213 (lit c4)) ▸
       at 5 5 (CCZ014 ∷ []) (sym (wp0046 c4)) ▸
       at 3 2 (Toff213 ∷ Toff214 ∷ []) (sym (wl0197 (lit c4))) ▸
       at 2 2 (Toff213 ∷ CX43 ∷ Toff214 ∷ []) (wl1120 (lit c4)) ▸
       at 3 3 (CX43 ∷ []) (wl1121 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ CCZ014 ∷ []) (wp0038 c4) ▸
       at 3 2 (CCZ024 ∷ CX43 ∷ []) (sym (wp0914 c4)) ▸ done

  b2 : Chain (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ CX43 ∷ CCZ014 ∷ CX43 ∷ []) (Bx2-1340 ∷ CCZ014 ∷ [])
  b2 = at 0 4 (Bx2-1340 ∷ []) (sym (lem-box-tQ-at02233440 c4)) ▸
       at 1 3 (CCZ014 ∷ []) (sym (wp0915 c4)) ▸ done


-- SWbc-box @02233440: 11 steps
lem-SWbc-box-at02233440 : Ws → ⟪ (Sw34 ∷ Bx2-1340 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1340 ∷ []) ⟫ʷ
lem-SWbc-box-at02233440 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw34 ∷ Bx2-1340 ∷ Sw34 ∷ []) (CX34 ∷ Bx2-1340 ∷ CX34 ∷ CCZ013 ∷ CCZ014 ∷ CCZ013 ∷ CCZ014 ∷ CCZ013 ∷ [])
  b0 = at 0 1 (CX34 ∷ CX43 ∷ CX34 ∷ []) (sym (wl0547 (lit c4))) ▸
       at 4 1 (CX34 ∷ CX43 ∷ CX34 ∷ []) (sym (wl0547 (lit c4))) ▸
       at 2 3 (Bx2-1340 ∷ CCZ013 ∷ []) (lem-CXbc-box-at02233440 c4) ▸
       at 3 2 (CX43 ∷ CCZ014 ∷ CCZ013 ∷ []) (wp0916 c4) ▸
       at 1 3 (Bx2-1340 ∷ CCZ014 ∷ []) (lem-CXcb-box-at02233440 c4) ▸
       at 4 2 (CX34 ∷ CCZ013 ∷ []) (wp0523 c4) ▸
       at 3 2 (CX34 ∷ CCZ013 ∷ CCZ014 ∷ []) (wp0917 c4) ▸
       at 2 2 (CX34 ∷ CCZ013 ∷ CCZ014 ∷ []) (wp0917 c4) ▸ done

  b1 : Chain (CX34 ∷ Bx2-1340 ∷ CX34 ∷ CCZ013 ∷ CCZ014 ∷ CCZ013 ∷ CCZ014 ∷ CCZ013 ∷ []) (Bx2-1340 ∷ [])
  b1 = at 3 5 (CCZ013 ∷ []) (wp0918 c4) ▸
       at 0 3 (Bx2-1340 ∷ CCZ013 ∷ []) (lem-CXbc-box-at02233440 c4) ▸
       at 1 2 [] (wl0230 (lit c4)) ▸ done


-- nat-SWbc @02233440: 23 steps
lem-nat-SWbc-at02233440 : Ws → ⟪ (Sw34 ∷ Bx2-1340 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1430 ∷ []) ⟫ʷ
lem-nat-SWbc-at02233440 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw34 ∷ Bx2-1340 ∷ Sw34 ∷ []) (CCZ124 ∷ Toff214 ∷ CCZ123 ∷ Toff123 ∷ Bx2-10 ∷ Toff123 ∷ Sw34 ∷ CCZ124 ∷ Bx2-10 ∷ Toff213 ∷ CCZ123 ∷ Bx1-240 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff213 ∷ Bx1-240 ∷ Toff213 ∷ CCZ123 ∷ Bx1-240 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw34 ∷ []) (sym (wl1122 (lit c4))) ▸
       at 1 2 (Toff214 ∷ Sw34 ∷ []) (wl1123 (lit c4)) ▸
       at 3 1 (CCZ124 ∷ Toff124 ∷ Bx2-10 ∷ Toff124 ∷ CCZ124 ∷ Bx2-10 ∷ []) (refl) ▸
       at 2 2 (CCZ123 ∷ Sw34 ∷ []) (sym (wl1124 (lit c4))) ▸
       at 3 2 (Toff123 ∷ Sw34 ∷ []) (wl1125 (lit c4)) ▸
       at 4 2 (Bx2-10 ∷ Sw34 ∷ []) (sym (c₂ (CZ) (Swap ↑))) ▸
       at 5 2 (Toff123 ∷ Sw34 ∷ []) (wl1125 (lit c4)) ▸ done

  b1 : Chain (CCZ124 ∷ Toff214 ∷ CCZ123 ∷ Toff123 ∷ Bx2-10 ∷ Toff123 ∷ Sw34 ∷ CCZ124 ∷ Bx2-10 ∷ Toff213 ∷ CCZ123 ∷ Bx1-240 ∷ Sw34 ∷ []) (CCZ124 ∷ Toff214 ∷ CCZ123 ∷ Toff123 ∷ Bx2-10 ∷ Toff123 ∷ CCZ123 ∷ Bx2-10 ∷ Toff214 ∷ CCZ124 ∷ CCZ123 ∷ Toff123 ∷ Bx2-10 ∷ Sw34 ∷ Toff124 ∷ CCZ124 ∷ Bx2-10 ∷ Sw34 ∷ [])
  b1 = at 6 2 (CCZ123 ∷ Sw34 ∷ []) (sym (wl1124 (lit c4))) ▸
       at 7 2 (Bx2-10 ∷ Sw34 ∷ []) (sym (c₂ (CZ) (Swap ↑))) ▸
       at 8 2 (Toff214 ∷ Sw34 ∷ []) (wl1123 (lit c4)) ▸
       at 9 2 (CCZ124 ∷ Sw34 ∷ []) (sym (wl1122 (lit c4))) ▸
       at 11 1 (CCZ124 ∷ Toff124 ∷ Bx2-10 ∷ Toff124 ∷ CCZ124 ∷ Bx2-10 ∷ []) (refl) ▸
       at 10 2 (CCZ123 ∷ Sw34 ∷ []) (sym (wl1124 (lit c4))) ▸
       at 11 2 (Toff123 ∷ Sw34 ∷ []) (wl1125 (lit c4)) ▸
       at 12 2 (Bx2-10 ∷ Sw34 ∷ []) (sym (c₂ (CZ) (Swap ↑))) ▸ done

  b2 : Chain (CCZ124 ∷ Toff214 ∷ CCZ123 ∷ Toff123 ∷ Bx2-10 ∷ Toff123 ∷ CCZ123 ∷ Bx2-10 ∷ Toff214 ∷ CCZ124 ∷ CCZ123 ∷ Toff123 ∷ Bx2-10 ∷ Sw34 ∷ Toff124 ∷ CCZ124 ∷ Bx2-10 ∷ Sw34 ∷ []) (Bx2-1430 ∷ [])
  b2 = at 13 2 (Toff123 ∷ Sw34 ∷ []) (wl1125 (lit c4)) ▸
       at 14 2 (CCZ123 ∷ Sw34 ∷ []) (sym (wl1124 (lit c4))) ▸
       at 15 2 (Bx2-10 ∷ Sw34 ∷ []) (sym (c₂ (CZ) (Swap ↑))) ▸
       at 16 2 [] (wl0004 (lit c4)) ▸
       at 2 6 (Bx1-230 ∷ []) (refl) ▸
       at 5 6 (Bx1-230 ∷ []) (refl) ▸
       at 0 6 (Bx2-1430 ∷ []) (refl) ▸ done


-- sym-bc @02233440: 2 steps
lem-sym-bc-at02233440 : Ws → ⟪ (Bx2-1340 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1430 ∷ []) ⟫ʷ
lem-sym-bc-at02233440 c4 = run b0
  where
  b0 : Chain (Bx2-1340 ∷ []) (Bx2-1430 ∷ [])
  b0 = at 0 1 (Sw34 ∷ Bx2-1340 ∷ Sw34 ∷ []) (sym (lem-SWbc-box-at02233440 c4)) ▸
       at 0 3 (Bx2-1430 ∷ []) (lem-nat-SWbc-at02233440 c4) ▸ done


-- box-perm-1324 @02233440: 1 steps
lem-box-perm-1324-at02233440 : Ws → ⟪ (Bx2-1340 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1430 ∷ []) ⟫ʷ
lem-box-perm-1324-at02233440 c4 = run b0
  where
  b0 : Chain (Bx2-1340 ∷ []) (Bx2-1430 ∷ [])
  b0 = at 0 1 (Bx2-1430 ∷ []) (lem-sym-bc-at02233440 c4) ▸ done


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


-- tP @022440: 7 steps
lem-tP-at022440 : Ws → ⟪ (Toff214 ∷ Toff203 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ Toff214 ∷ []) ⟫ʷ
lem-tP-at022440 c4 = run b0
  where
  b0 : Chain (Toff214 ∷ Toff203 ∷ []) (Toff203 ∷ Toff214 ∷ [])
  b0 = at 0 1 (K2 ∷ CCZ124 ∷ K2⁻ ∷ []) (sym (wl0624 (lit c4))) ▸
       at 3 1 (K2 ∷ CCZ023 ∷ K2⁻ ∷ []) (sym (wl0625 (lit c4))) ▸
       at 2 2 [] (wl0175 (lit c4)) ▸
       at 1 2 (CCZ023 ∷ CCZ124 ∷ []) (lem-cQ-at022440 c4) ▸
       at 2 0 (K2⁻ ∷ K2 ∷ []) (sym (wl0175 (lit c4))) ▸
       at 0 3 (Toff203 ∷ []) (wl0625 (lit c4)) ▸
       at 1 3 (Toff214 ∷ []) (wl0624 (lit c4)) ▸ done


-- VPQ @022440: 14 steps
lem-VPQ-at022440 : Ws → ⟪ (Toff214 ∷ CCZ124 ∷ Toff203 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ CCZ023 ∷ Toff214 ∷ CCZ124 ∷ []) ⟫ʷ
lem-VPQ-at022440 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff214 ∷ CCZ124 ∷ Toff203 ∷ CCZ023 ∷ []) (CS03⁻ ∷ CS14⁻ ∷ S2 ∷ Toff203 ∷ Toff214 ∷ S2⁻ ∷ [])
  b0 = at 0 2 (CS14⁻ ∷ S2 ∷ Toff214 ∷ S2⁻ ∷ []) (sym (wl0629 (lit c4))) ▸
       at 4 2 (CS03⁻ ∷ S2 ∷ Toff203 ∷ S2⁻ ∷ []) (sym (wl0630 (lit c4))) ▸
       at 3 2 (CS03⁻ ∷ S2⁻ ∷ []) (sym (wl0631 (lit c4))) ▸
       at 2 2 (CS03⁻ ∷ Toff214 ∷ []) (lem-comm-TOFF214-CSd03 (lit c4)) ▸
       at 1 2 (CS03⁻ ∷ S2 ∷ []) (sym (wl0632 (lit c4))) ▸
       at 0 2 (CS03⁻ ∷ CS14⁻ ∷ []) (sym (wp0514 c4)) ▸
       at 4 2 [] (wl0179 (lit c4)) ▸
       at 3 2 (Toff203 ∷ Toff214 ∷ []) (lem-tP-at022440 c4) ▸ done

  b1 : Chain (CS03⁻ ∷ CS14⁻ ∷ S2 ∷ Toff203 ∷ Toff214 ∷ S2⁻ ∷ []) (Toff203 ∷ CCZ023 ∷ Toff214 ∷ CCZ124 ∷ [])
  b1 = at 4 0 (S2⁻ ∷ S2 ∷ []) (sym (wl0179 (lit c4))) ▸
       at 1 2 (S2 ∷ CS14⁻ ∷ []) (wl0633 (lit c4)) ▸
       at 2 2 (Toff203 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-TOFF203 (lit c4)) ▸
       at 3 2 (S2⁻ ∷ CS14⁻ ∷ []) (wl0634 (lit c4)) ▸
       at 0 4 (Toff203 ∷ CCZ023 ∷ []) (wl0630 (lit c4)) ▸
       at 2 4 (Toff214 ∷ CCZ124 ∷ []) (wl0629 (lit c4)) ▸ done


-- QVQ @022440: 3 steps
lem-QVQ-at022440 : Ws → ⟪ (CCZ023 ∷ Toff214 ∷ CCZ124 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ Toff214 ∷ CCZ124 ∷ Toff203 ∷ []) ⟫ʷ
lem-QVQ-at022440 c4 = run b0
  where
  b0 : Chain (CCZ023 ∷ Toff214 ∷ CCZ124 ∷ CCZ023 ∷ []) (Toff203 ∷ Toff214 ∷ CCZ124 ∷ Toff203 ∷ [])
  b0 = at 0 0 (Toff203 ∷ Toff203 ∷ []) (sym (wl0635 (lit c4))) ▸
       at 1 4 (Toff214 ∷ CCZ124 ∷ Toff203 ∷ CCZ023 ∷ []) (sym (lem-VPQ-at022440 c4)) ▸
       at 4 2 [] (wl0204 (lit c4)) ▸ done


-- box-cP @022440: 12 steps
lem-box-cP-at022440 : Ws → ⟪ (Bx2-1430 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ []) ⟫ʷ
lem-box-cP-at022440 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx2-1430 ∷ []) (CCZ124 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ CCZ124 ∷ CCZ123 ∷ Toff123 ∷ CZ01 ∷ Toff123 ∷ CCZ123 ∷ CZ01 ∷ [])
  b0 = at 0 1 (CCZ124 ∷ Toff214 ∷ Bx1-230 ∷ Toff214 ∷ CCZ124 ∷ Bx1-230 ∷ []) (refl) ▸
       at 2 1 (CCZ123 ∷ Toff123 ∷ Bx2-10 ∷ Toff123 ∷ CCZ123 ∷ Bx2-10 ∷ []) (refl) ▸
       at 4 1 (CZ01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 2 6 (CCZ023 ∷ []) (sym (wl1126 (lit c4))) ▸
       at 5 1 (CCZ123 ∷ Toff123 ∷ Bx2-10 ∷ Toff123 ∷ CCZ123 ∷ Bx2-10 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 10 1 (CZ01 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ124 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ CCZ124 ∷ CCZ123 ∷ Toff123 ∷ CZ01 ∷ Toff123 ∷ CCZ123 ∷ CZ01 ∷ []) (CCZ124 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ [])
  b1 = at 5 6 (CCZ023 ∷ []) (sym (wl1126 (lit c4))) ▸
       at 2 4 (Toff203 ∷ Toff214 ∷ CCZ124 ∷ Toff203 ∷ []) (lem-QVQ-at022440 c4) ▸
       at 1 2 (Toff203 ∷ Toff214 ∷ []) (lem-tP-at022440 c4) ▸
       at 2 2 [] (wl0636 (lit c4)) ▸ done


-- Xb-box @022440: 18 steps
lem-Xb-box-at022440 : Ws → ⟪ (X4 ∷ Bx2-1430 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1430 ∷ CCZ013 ∷ []) ⟫ʷ
lem-Xb-box-at022440 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ Bx2-1430 ∷ X4 ∷ []) (CCZ124 ∷ Toff203 ∷ X4 ∷ CZ12 ∷ CS03 ∷ CX13 ∷ CCZ124 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ Toff203 ∷ X4 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ []) (lem-box-cP-at022440 c4) ▸
       at 0 2 (CCZ124 ∷ X4 ∷ CZ12 ∷ []) (sym (wl1127 (lit c4))) ▸
       at 2 2 (Toff203 ∷ CZ12 ∷ CCZ013 ∷ []) (wl1128 (lit c4)) ▸
       at 1 2 (Toff203 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑) (X))) ▸
       at 4 1 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (wl0289 (lit c4)) ▸
       at 8 2 (CCZ124 ∷ CS01 ∷ []) (sym (wp0919 c4)) ▸
       at 7 2 (CCZ124 ∷ CX13 ∷ []) (sym (wl0280 (lit c4))) ▸
       at 6 2 (CCZ124 ∷ CS03⁻ ∷ []) (lem-comm-CSd03-CCZ124 (lit c4)) ▸ done

  b1 : Chain (CCZ124 ∷ Toff203 ∷ X4 ∷ CZ12 ∷ CS03 ∷ CX13 ∷ CCZ124 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ Toff203 ∷ X4 ∷ []) (CCZ124 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ X4 ∷ CCZ013 ∷ X4 ∷ [])
  b1 = at 5 2 (CCZ124 ∷ CX13 ∷ []) (sym (wl0280 (lit c4))) ▸
       at 4 2 (CCZ124 ∷ CS03 ∷ []) (lem-comm-CS03-CCZ124 (lit c4)) ▸
       at 5 5 (CCZ013 ∷ []) (sym (wl0289 (lit c4))) ▸
       at 3 2 (CCZ124 ∷ CZ12 ∷ []) (sym (wl1129 (lit c4))) ▸
       at 2 2 (CCZ124 ∷ X4 ∷ CZ12 ∷ []) (sym (wl1127 (lit c4))) ▸
       at 3 3 (X4 ∷ []) (wl1130 (lit c4)) ▸
       at 4 2 (Toff203 ∷ CCZ013 ∷ []) (wl1131 (lit c4)) ▸
       at 3 2 (Toff203 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑) (X))) ▸ done

  b2 : Chain (CCZ124 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ X4 ∷ CCZ013 ∷ X4 ∷ []) (Bx2-1430 ∷ CCZ013 ∷ [])
  b2 = at 0 4 (Bx2-1430 ∷ []) (sym (lem-box-cP-at022440 c4)) ▸
       at 1 3 (CCZ013 ∷ []) (sym (wp0024 c4)) ▸ done


-- box-tQ @022440: 13 steps
lem-box-tQ-at022440 : Ws → ⟪ (Bx2-1430 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ []) ⟫ʷ
lem-box-tQ-at022440 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx2-1430 ∷ []) (CCZ124 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ CCZ124 ∷ CCZ123 ∷ Toff123 ∷ CZ01 ∷ Toff123 ∷ CCZ123 ∷ CZ01 ∷ [])
  b0 = at 0 1 (CCZ124 ∷ Toff214 ∷ Bx1-230 ∷ Toff214 ∷ CCZ124 ∷ Bx1-230 ∷ []) (refl) ▸
       at 2 1 (CCZ123 ∷ Toff123 ∷ Bx2-10 ∷ Toff123 ∷ CCZ123 ∷ Bx2-10 ∷ []) (refl) ▸
       at 4 1 (CZ01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 2 6 (CCZ023 ∷ []) (sym (wl1126 (lit c4))) ▸
       at 5 1 (CCZ123 ∷ Toff123 ∷ Bx2-10 ∷ Toff123 ∷ CCZ123 ∷ Bx2-10 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 10 1 (CZ01 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ124 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ CCZ124 ∷ CCZ123 ∷ Toff123 ∷ CZ01 ∷ Toff123 ∷ CCZ123 ∷ CZ01 ∷ []) (Toff214 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ [])
  b1 = at 5 6 (CCZ023 ∷ []) (sym (wl1126 (lit c4))) ▸
       at 0 2 (Toff214 ∷ CCZ124 ∷ CZ14 ∷ []) (wl0622 (lit c4)) ▸
       at 2 2 (CCZ023 ∷ CZ14 ∷ []) (lem-comm-CZ14-CCZ023 (lit c4)) ▸
       at 1 2 (CCZ023 ∷ CCZ124 ∷ []) (lem-cQ-at022440 c4) ▸
       at 2 4 (Toff214 ∷ []) (wl0623 (lit c4)) ▸ done


-- CXbc-box @022440: 17 steps
lem-CXbc-box-at022440 : Ws → ⟪ (CX43 ∷ Bx2-1430 ∷ CX43 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1430 ∷ CCZ014 ∷ []) ⟫ʷ
lem-CXbc-box-at022440 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX43 ∷ Bx2-1430 ∷ CX43 ∷ []) (Toff214 ∷ CCZ023 ∷ Toff214 ∷ CX43 ∷ CCZ024 ∷ CS04 ∷ CX14 ∷ CS04⁻ ∷ CCZ023 ∷ CX14 ∷ CS01 ∷ CX43 ∷ [])
  b0 = at 1 1 (Toff214 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ []) (lem-box-tQ-at022440 c4) ▸
       at 0 2 (Toff214 ∷ CX43 ∷ []) (wl1132 (lit c4)) ▸
       at 1 2 (CCZ023 ∷ CX43 ∷ CCZ024 ∷ []) (sym (wp0920 c4)) ▸
       at 3 2 (Toff214 ∷ CCZ024 ∷ CCZ014 ∷ []) (wp0921 c4) ▸
       at 2 2 (Toff214 ∷ CX43 ∷ []) (wl1132 (lit c4)) ▸
       at 5 1 (CS04 ∷ CX14 ∷ CS04⁻ ∷ CX14 ∷ CS01 ∷ []) (wp0046 c4) ▸
       at 9 2 (CCZ023 ∷ CS01 ∷ []) (sym (wl0199 (lit c4))) ▸
       at 8 2 (CCZ023 ∷ CX14 ∷ []) (lem-comm-CX14-CCZ023 (lit c4)) ▸ done

  b1 : Chain (Toff214 ∷ CCZ023 ∷ Toff214 ∷ CX43 ∷ CCZ024 ∷ CS04 ∷ CX14 ∷ CS04⁻ ∷ CCZ023 ∷ CX14 ∷ CS01 ∷ CX43 ∷ []) (Bx2-1430 ∷ CX43 ∷ CCZ014 ∷ CX43 ∷ [])
  b1 = at 7 2 (CCZ023 ∷ CS04⁻ ∷ []) (sym (wp0047 c4)) ▸
       at 6 2 (CCZ023 ∷ CX14 ∷ []) (lem-comm-CX14-CCZ023 (lit c4)) ▸
       at 5 2 (CCZ023 ∷ CS04 ∷ []) (sym (wp0048 c4)) ▸
       at 6 5 (CCZ014 ∷ []) (sym (wp0046 c4)) ▸
       at 4 2 (CCZ023 ∷ CCZ024 ∷ []) (sym (wp0669 c4)) ▸
       at 3 2 (CCZ023 ∷ CX43 ∷ CCZ024 ∷ []) (sym (wp0920 c4)) ▸
       at 4 3 (CX43 ∷ []) (wp0922 c4) ▸
       at 0 4 (Bx2-1430 ∷ []) (sym (lem-box-tQ-at022440 c4)) ▸ done

  b2 : Chain (Bx2-1430 ∷ CX43 ∷ CCZ014 ∷ CX43 ∷ []) (Bx2-1430 ∷ CCZ014 ∷ [])
  b2 = at 1 3 (CCZ014 ∷ []) (sym (wp0915 c4)) ▸ done


-- CXcb-box @022440: 18 steps
lem-CXcb-box-at022440 : Ws → ⟪ (CX34 ∷ Bx2-1430 ∷ CX34 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1430 ∷ CCZ013 ∷ []) ⟫ʷ
lem-CXcb-box-at022440 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX34 ∷ Bx2-1430 ∷ CX34 ∷ []) (Toff214 ∷ CCZ023 ∷ CX34 ∷ Toff213 ∷ CS03 ∷ CX13 ∷ Toff214 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ CCZ023 ∷ CX34 ∷ [])
  b0 = at 1 1 (Toff214 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ []) (lem-box-tQ-at022440 c4) ▸
       at 0 2 (Toff214 ∷ CX34 ∷ Toff213 ∷ []) (wl1133 (lit c4)) ▸
       at 2 2 (CCZ023 ∷ Toff213 ∷ CCZ013 ∷ []) (sym (wl1134 (lit c4))) ▸
       at 1 2 (CCZ023 ∷ CX34 ∷ []) (sym (wp0680 c4)) ▸
       at 4 1 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (wl0289 (lit c4)) ▸
       at 8 2 (Toff214 ∷ CS01 ∷ []) (wp0923 c4) ▸
       at 7 2 (Toff214 ∷ CX13 ∷ []) (wl1135 (lit c4)) ▸
       at 6 2 (Toff214 ∷ CS03⁻ ∷ []) (lem-comm-CSd03-TOFF214 (lit c4)) ▸ done

  b1 : Chain (Toff214 ∷ CCZ023 ∷ CX34 ∷ Toff213 ∷ CS03 ∷ CX13 ∷ Toff214 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ CCZ023 ∷ CX34 ∷ []) (Toff214 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ CX34 ∷ CCZ013 ∷ CX34 ∷ [])
  b1 = at 5 2 (Toff214 ∷ CX13 ∷ []) (wl1135 (lit c4)) ▸
       at 4 2 (Toff214 ∷ CS03 ∷ []) (lem-comm-CS03-TOFF214 (lit c4)) ▸
       at 5 5 (CCZ013 ∷ []) (sym (wl0289 (lit c4))) ▸
       at 3 2 (Toff214 ∷ Toff213 ∷ []) (wl0197 (lit c4)) ▸
       at 2 2 (Toff214 ∷ CX34 ∷ Toff213 ∷ []) (wl1133 (lit c4)) ▸
       at 3 3 (CX34 ∷ []) (wl1136 (lit c4)) ▸
       at 4 2 (CCZ023 ∷ CCZ013 ∷ []) (wl0671 (lit c4)) ▸
       at 3 2 (CCZ023 ∷ CX34 ∷ []) (sym (wp0680 c4)) ▸ done

  b2 : Chain (Toff214 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ CX34 ∷ CCZ013 ∷ CX34 ∷ []) (Bx2-1430 ∷ CCZ013 ∷ [])
  b2 = at 0 4 (Bx2-1430 ∷ []) (sym (lem-box-tQ-at022440 c4)) ▸
       at 1 3 (CCZ013 ∷ []) (sym (wp0913 c4)) ▸ done


-- SWbc-box @022440: 11 steps
lem-SWbc-box-at022440 : Ws → ⟪ (Sw34 ∷ Bx2-1430 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1430 ∷ []) ⟫ʷ
lem-SWbc-box-at022440 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw34 ∷ Bx2-1430 ∷ Sw34 ∷ []) (CX43 ∷ Bx2-1430 ∷ CX43 ∷ CCZ014 ∷ CCZ013 ∷ CCZ014 ∷ CCZ013 ∷ CCZ014 ∷ [])
  b0 = at 0 1 (CX43 ∷ CX34 ∷ CX43 ∷ []) (sym (wl0649 (lit c4))) ▸
       at 4 1 (CX43 ∷ CX34 ∷ CX43 ∷ []) (sym (wl0649 (lit c4))) ▸
       at 2 3 (Bx2-1430 ∷ CCZ014 ∷ []) (lem-CXbc-box-at022440 c4) ▸
       at 3 2 (CX34 ∷ CCZ013 ∷ CCZ014 ∷ []) (wp0917 c4) ▸
       at 1 3 (Bx2-1430 ∷ CCZ013 ∷ []) (lem-CXcb-box-at022440 c4) ▸
       at 4 2 (CX43 ∷ CCZ014 ∷ []) (wp0810 c4) ▸
       at 3 2 (CX43 ∷ CCZ014 ∷ CCZ013 ∷ []) (wp0916 c4) ▸
       at 2 2 (CX43 ∷ CCZ014 ∷ CCZ013 ∷ []) (wp0916 c4) ▸ done

  b1 : Chain (CX43 ∷ Bx2-1430 ∷ CX43 ∷ CCZ014 ∷ CCZ013 ∷ CCZ014 ∷ CCZ013 ∷ CCZ014 ∷ []) (Bx2-1430 ∷ [])
  b1 = at 3 5 (CCZ014 ∷ []) (wp0924 c4) ▸
       at 0 3 (Bx2-1430 ∷ CCZ014 ∷ []) (lem-CXbc-box-at022440 c4) ▸
       at 1 2 [] (wp0161 c4) ▸ done


-- nat-SWbc @022440: 23 steps
lem-nat-SWbc-at022440 : Ws → ⟪ (Sw34 ∷ Bx2-1430 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1340 ∷ []) ⟫ʷ
lem-nat-SWbc-at022440 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw34 ∷ Bx2-1430 ∷ Sw34 ∷ []) (CCZ123 ∷ Toff213 ∷ CCZ124 ∷ Toff124 ∷ Bx2-10 ∷ Toff124 ∷ Sw34 ∷ CCZ123 ∷ Bx2-10 ∷ Toff214 ∷ CCZ124 ∷ Bx1-230 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff214 ∷ Bx1-230 ∷ Toff214 ∷ CCZ124 ∷ Bx1-230 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw34 ∷ []) (sym (wl1124 (lit c4))) ▸
       at 1 2 (Toff213 ∷ Sw34 ∷ []) (wl1137 (lit c4)) ▸
       at 3 1 (CCZ123 ∷ Toff123 ∷ Bx2-10 ∷ Toff123 ∷ CCZ123 ∷ Bx2-10 ∷ []) (refl) ▸
       at 2 2 (CCZ124 ∷ Sw34 ∷ []) (sym (wl1122 (lit c4))) ▸
       at 3 2 (Toff124 ∷ Sw34 ∷ []) (wl1138 (lit c4)) ▸
       at 4 2 (Bx2-10 ∷ Sw34 ∷ []) (sym (c₂ (CZ) (Swap ↑))) ▸
       at 5 2 (Toff124 ∷ Sw34 ∷ []) (wl1138 (lit c4)) ▸ done

  b1 : Chain (CCZ123 ∷ Toff213 ∷ CCZ124 ∷ Toff124 ∷ Bx2-10 ∷ Toff124 ∷ Sw34 ∷ CCZ123 ∷ Bx2-10 ∷ Toff214 ∷ CCZ124 ∷ Bx1-230 ∷ Sw34 ∷ []) (CCZ123 ∷ Toff213 ∷ CCZ124 ∷ Toff124 ∷ Bx2-10 ∷ Toff124 ∷ CCZ124 ∷ Bx2-10 ∷ Toff213 ∷ CCZ123 ∷ CCZ124 ∷ Toff124 ∷ Bx2-10 ∷ Sw34 ∷ Toff123 ∷ CCZ123 ∷ Bx2-10 ∷ Sw34 ∷ [])
  b1 = at 6 2 (CCZ124 ∷ Sw34 ∷ []) (sym (wl1122 (lit c4))) ▸
       at 7 2 (Bx2-10 ∷ Sw34 ∷ []) (sym (c₂ (CZ) (Swap ↑))) ▸
       at 8 2 (Toff213 ∷ Sw34 ∷ []) (wl1137 (lit c4)) ▸
       at 9 2 (CCZ123 ∷ Sw34 ∷ []) (sym (wl1124 (lit c4))) ▸
       at 11 1 (CCZ123 ∷ Toff123 ∷ Bx2-10 ∷ Toff123 ∷ CCZ123 ∷ Bx2-10 ∷ []) (refl) ▸
       at 10 2 (CCZ124 ∷ Sw34 ∷ []) (sym (wl1122 (lit c4))) ▸
       at 11 2 (Toff124 ∷ Sw34 ∷ []) (wl1138 (lit c4)) ▸
       at 12 2 (Bx2-10 ∷ Sw34 ∷ []) (sym (c₂ (CZ) (Swap ↑))) ▸ done

  b2 : Chain (CCZ123 ∷ Toff213 ∷ CCZ124 ∷ Toff124 ∷ Bx2-10 ∷ Toff124 ∷ CCZ124 ∷ Bx2-10 ∷ Toff213 ∷ CCZ123 ∷ CCZ124 ∷ Toff124 ∷ Bx2-10 ∷ Sw34 ∷ Toff123 ∷ CCZ123 ∷ Bx2-10 ∷ Sw34 ∷ []) (Bx2-1340 ∷ [])
  b2 = at 13 2 (Toff124 ∷ Sw34 ∷ []) (wl1138 (lit c4)) ▸
       at 14 2 (CCZ124 ∷ Sw34 ∷ []) (sym (wl1122 (lit c4))) ▸
       at 15 2 (Bx2-10 ∷ Sw34 ∷ []) (sym (c₂ (CZ) (Swap ↑))) ▸
       at 16 2 [] (wl0004 (lit c4)) ▸
       at 2 6 (Bx1-240 ∷ []) (refl) ▸
       at 5 6 (Bx1-240 ∷ []) (refl) ▸
       at 0 6 (Bx2-1340 ∷ []) (refl) ▸ done


-- sym-bc @022440: 2 steps
lem-sym-bc-at022440 : Ws → ⟪ (Bx2-1430 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1340 ∷ []) ⟫ʷ
lem-sym-bc-at022440 c4 = run b0
  where
  b0 : Chain (Bx2-1430 ∷ []) (Bx2-1340 ∷ [])
  b0 = at 0 1 (Sw34 ∷ Bx2-1430 ∷ Sw34 ∷ []) (sym (lem-SWbc-box-at022440 c4)) ▸
       at 0 3 (Bx2-1340 ∷ []) (lem-nat-SWbc-at022440 c4) ▸ done


-- box-perm-1324 @022440: 1 steps
lem-box-perm-1324-at022440 : Ws → ⟪ (Bx2-1430 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1340 ∷ []) ⟫ʷ
lem-box-perm-1324-at022440 c4 = run b0
  where
  b0 : Chain (Bx2-1430 ∷ []) (Bx2-1340 ∷ [])
  b0 = at 0 1 (Bx2-1340 ∷ []) (lem-sym-bc-at022440 c4) ▸ done


-- CKc-box @02233440: 61 steps
lem-CKc-box-at02233440 : Ws → ⟪ (Bx2-1340 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ CK40 ∷ CCZ013 ∷ Bx2-1340 ∷ []) ⟫ʷ
lem-CKc-box-at02233440 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (run b7)))))))
  where
  b0 : Chain (Bx2-1340 ∷ CK40 ∷ []) (X4 ∷ Bx2-1340 ∷ CCZ013 ∷ K0 ∷ CK40 ∷ S4 ∷ CCZ013 ∷ X4 ∷ CCZ013 ∷ [])
  b0 = at 1 0 (CCZ013 ∷ CCZ013 ∷ []) (sym (wl0230 (lit c4))) ▸
       at 0 1 (Bx2-1430 ∷ []) (lem-box-perm-1324-at02233440 c4) ▸
       at 0 2 (X4 ∷ Bx2-1430 ∷ X4 ∷ []) (sym (lem-Xb-box-at022440 c4)) ▸
       at 3 2 (CCZ013 ∷ CK40 ∷ CCZ013 ∷ CCZ013 ∷ []) (sym (wp0925 c4)) ▸
       at 2 2 (CCZ013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • CCZ • Swap ↑ ↑) (X))) ▸
       at 3 2 (K0 ∷ CK40 ∷ S4 ∷ X4 ∷ []) (sym (wp0610 c4)) ▸
       at 6 2 (CCZ013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • CCZ • Swap ↑ ↑) (X))) ▸
       at 1 1 (Bx2-1340 ∷ []) (lem-box-perm-1324-at022440 c4) ▸ done

  b1 : Chain (X4 ∷ Bx2-1340 ∷ CCZ013 ∷ K0 ∷ CK40 ∷ S4 ∷ CCZ013 ∷ X4 ∷ CCZ013 ∷ []) (X4 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ013 ∷ CCZ024 ∷ K0 ∷ CK40 ∷ S4 ∷ CCZ013 ∷ X4 ∷ CCZ013 ∷ [])
  b1 = at 1 1 (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ []) (lem-box-tQ-at02233440 c4) ▸
       at 5 1 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (wl0289 (lit c4)) ▸
       at 4 2 (CS03 ∷ CCZ024 ∷ []) (wp0021 c4) ▸
       at 5 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 6 2 (CS03⁻ ∷ CCZ024 ∷ []) (wp0032 c4) ▸
       at 7 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 8 2 (CS01 ∷ CCZ024 ∷ []) (wp0039 c4) ▸
       at 4 5 (CCZ013 ∷ []) (sym (wl0289 (lit c4))) ▸ done

  b2 : Chain (X4 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ013 ∷ CCZ024 ∷ K0 ∷ CK40 ∷ S4 ∷ CCZ013 ∷ X4 ∷ CCZ013 ∷ []) (X4 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ013 ∷ K0 ∷ Toff024 ∷ CCZ024 ∷ CZ02 ∷ CK40 ∷ CZ02 ∷ S4 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CCZ024 ∷ CS01 ∷ X4 ∷ CCZ013 ∷ [])
  b2 = at 5 2 (K0 ∷ Toff024 ∷ CCZ024 ∷ CCZ024 ∷ []) (wp0926 c4) ▸
       at 8 2 (CZ02 ∷ CK40 ∷ CZ02 ∷ CCZ024 ∷ []) (wp0927 c4) ▸
       at 11 2 (S4 ∷ CCZ024 ∷ []) (wp0617 c4) ▸
       at 13 1 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (wl0289 (lit c4)) ▸
       at 12 2 (CS03 ∷ CCZ024 ∷ []) (wp0021 c4) ▸
       at 13 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 14 2 (CS03⁻ ∷ CCZ024 ∷ []) (wp0032 c4) ▸
       at 15 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸ done

  b3 : Chain (X4 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ013 ∷ K0 ∷ Toff024 ∷ CCZ024 ∷ CZ02 ∷ CK40 ∷ CZ02 ∷ S4 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CCZ024 ∷ CS01 ∷ X4 ∷ CCZ013 ∷ []) (X4 ∷ Toff213 ∷ CCZ024 ∷ CCZ013 ∷ K0 ∷ CK40 ∷ S4 ∷ CCZ013 ∷ Toff213 ∷ CCZ024 ∷ X4 ∷ CCZ013 ∷ [])
  b3 = at 16 2 (CS01 ∷ CCZ024 ∷ []) (wp0039 c4) ▸
       at 12 5 (CCZ013 ∷ []) (sym (wl0289 (lit c4))) ▸
       at 5 7 (K0 ∷ CK40 ∷ S4 ∷ []) (sym (wp0928 c4)) ▸
       at 3 2 (CCZ013 ∷ Toff213 ∷ []) (sym (wl0186 (lit c4))) ▸
       at 4 2 (K0 ∷ Toff213 ∷ []) (sym (c₁ (K) (K ↑ • CCZ • K ↑ • iI))) ▸
       at 5 2 (CK40 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CK40 (lit c4)) ▸
       at 6 2 (S4 ∷ Toff213 ∷ []) (c₄ ((K ↑ • CCZ • K ↑ • iI) ↑) (S)) ▸
       at 7 2 (CCZ013 ∷ Toff213 ∷ []) (sym (wl0186 (lit c4))) ▸ done

  b4 : Chain (X4 ∷ Toff213 ∷ CCZ024 ∷ CCZ013 ∷ K0 ∷ CK40 ∷ S4 ∷ CCZ013 ∷ Toff213 ∷ CCZ024 ∷ X4 ∷ CCZ013 ∷ []) (X4 ∷ Toff213 ∷ CCZ013 ∷ K0 ∷ Toff024 ∷ CCZ024 ∷ CCZ024 ∷ CK40 ∷ S4 ∷ CCZ013 ∷ Toff213 ∷ CCZ024 ∷ X4 ∷ CCZ013 ∷ [])
  b4 = at 3 1 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (wl0289 (lit c4)) ▸
       at 2 2 (CS03 ∷ CCZ024 ∷ []) (wp0021 c4) ▸
       at 3 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 4 2 (CS03⁻ ∷ CCZ024 ∷ []) (wp0032 c4) ▸
       at 5 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 6 2 (CS01 ∷ CCZ024 ∷ []) (wp0039 c4) ▸
       at 2 5 (CCZ013 ∷ []) (sym (wl0289 (lit c4))) ▸
       at 3 2 (K0 ∷ Toff024 ∷ CCZ024 ∷ CCZ024 ∷ []) (wp0926 c4) ▸ done

  b5 : Chain (X4 ∷ Toff213 ∷ CCZ013 ∷ K0 ∷ Toff024 ∷ CCZ024 ∷ CCZ024 ∷ CK40 ∷ S4 ∷ CCZ013 ∷ Toff213 ∷ CCZ024 ∷ X4 ∷ CCZ013 ∷ []) (X4 ∷ Toff213 ∷ CCZ013 ∷ K0 ∷ Toff024 ∷ CCZ024 ∷ CZ02 ∷ CK40 ∷ CZ02 ∷ S4 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ X4 ∷ CCZ013 ∷ [])
  b5 = at 6 2 (CZ02 ∷ CK40 ∷ CZ02 ∷ CCZ024 ∷ []) (wp0927 c4) ▸
       at 9 2 (S4 ∷ CCZ024 ∷ []) (wp0617 c4) ▸
       at 11 1 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (wl0289 (lit c4)) ▸
       at 10 2 (CS03 ∷ CCZ024 ∷ []) (wp0021 c4) ▸
       at 11 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 12 2 (CS03⁻ ∷ CCZ024 ∷ []) (wp0032 c4) ▸
       at 13 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 14 2 (CS01 ∷ CCZ024 ∷ []) (wp0039 c4) ▸ done

  b6 : Chain (X4 ∷ Toff213 ∷ CCZ013 ∷ K0 ∷ Toff024 ∷ CCZ024 ∷ CZ02 ∷ CK40 ∷ CZ02 ∷ S4 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ X4 ∷ CCZ013 ∷ []) (X4 ∷ CCZ013 ∷ K0 ∷ CK40 ∷ S4 ∷ CCZ013 ∷ Bx2-1340 ∷ X4 ∷ CCZ013 ∷ [])
  b6 = at 10 5 (CCZ013 ∷ []) (sym (wl0289 (lit c4))) ▸
       at 3 7 (K0 ∷ CK40 ∷ S4 ∷ []) (sym (wp0928 c4)) ▸
       at 1 2 (CCZ013 ∷ Toff213 ∷ []) (sym (wl0186 (lit c4))) ▸
       at 2 2 (K0 ∷ Toff213 ∷ []) (sym (c₁ (K) (K ↑ • CCZ • K ↑ • iI))) ▸
       at 3 2 (CK40 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CK40 (lit c4)) ▸
       at 4 2 (S4 ∷ Toff213 ∷ []) (c₄ ((K ↑ • CCZ • K ↑ • iI) ↑) (S)) ▸
       at 5 2 (CCZ013 ∷ Toff213 ∷ []) (sym (wl0186 (lit c4))) ▸
       at 6 4 (Bx2-1340 ∷ []) (sym (lem-box-tQ-at02233440 c4)) ▸ done

  b7 : Chain (X4 ∷ CCZ013 ∷ K0 ∷ CK40 ∷ S4 ∷ CCZ013 ∷ Bx2-1340 ∷ X4 ∷ CCZ013 ∷ []) (CCZ013 ∷ CK40 ∷ CCZ013 ∷ Bx2-1340 ∷ [])
  b7 = at 6 1 (Bx2-1430 ∷ []) (sym (lem-box-perm-1324-at022440 c4)) ▸
       at 0 6 (CCZ013 ∷ CK40 ∷ CCZ013 ∷ X4 ∷ []) (sym (wp0929 c4)) ▸
       at 3 3 (Bx2-1430 ∷ CCZ013 ∷ []) (lem-Xb-box-at022440 c4) ▸
       at 4 2 [] (wl0230 (lit c4)) ▸
       at 3 1 (Bx2-1340 ∷ []) (lem-box-perm-1324-at022440 c4) ▸ done


-- tP @02233440: 7 steps
lem-tP-at02233440 : Ws → ⟪ (Toff213 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ Toff213 ∷ []) ⟫ʷ
lem-tP-at02233440 c4 = run b0
  where
  b0 : Chain (Toff213 ∷ Toff204 ∷ []) (Toff204 ∷ Toff213 ∷ [])
  b0 = at 0 1 (K2 ∷ CCZ123 ∷ K2⁻ ∷ []) (sym (wl0174 (lit c4))) ▸
       at 3 1 (K2 ∷ CCZ024 ∷ K2⁻ ∷ []) (sym (wp0014 c4)) ▸
       at 2 2 [] (wl0175 (lit c4)) ▸
       at 1 2 (CCZ024 ∷ CCZ123 ∷ []) (lem-cQ-at02233440 c4) ▸
       at 2 0 (K2⁻ ∷ K2 ∷ []) (sym (wl0175 (lit c4))) ▸
       at 0 3 (Toff204 ∷ []) (wp0014 c4) ▸
       at 1 3 (Toff213 ∷ []) (wl0174 (lit c4)) ▸ done


-- P-box @02233440: 8 steps
lem-P-box-at02233440 : Ws → ⟪ (Toff204 ∷ Bx2-1340 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1340 ∷ []) ⟫ʷ
lem-P-box-at02233440 c4 = run b0
  where
  b0 : Chain (Toff204 ∷ Bx2-1340 ∷ Toff204 ∷ []) (Bx2-1340 ∷ [])
  b0 = at 1 1 (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ []) (lem-box-tQ-at02233440 c4) ▸
       at 0 2 (Toff213 ∷ Toff204 ∷ []) (sym (lem-tP-at02233440 c4)) ▸
       at 1 2 (CCZ024 ∷ CZ04 ∷ Toff204 ∷ []) (sym (wp0780 c4)) ▸
       at 3 2 (Toff213 ∷ Toff204 ∷ []) (sym (lem-tP-at02233440 c4)) ▸
       at 4 3 (CCZ024 ∷ CZ04 ∷ []) (sym (wp0781 c4)) ▸
       at 2 2 (Toff213 ∷ CZ04 ∷ []) (lem-comm-CZ04-TOFF213 (lit c4)) ▸
       at 3 3 (CCZ024 ∷ []) (sym (wp0782 c4)) ▸
       at 0 4 (Bx2-1340 ∷ []) (sym (lem-box-tQ-at02233440 c4)) ▸ done


-- VPQ @02233440: 14 steps
lem-VPQ-at02233440 : Ws → ⟪ (Toff213 ∷ CCZ123 ∷ Toff204 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ []) ⟫ʷ
lem-VPQ-at02233440 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff213 ∷ CCZ123 ∷ Toff204 ∷ CCZ024 ∷ []) (CS04⁻ ∷ CS13⁻ ∷ S2 ∷ Toff204 ∷ Toff213 ∷ S2⁻ ∷ [])
  b0 = at 0 2 (CS13⁻ ∷ S2 ∷ Toff213 ∷ S2⁻ ∷ []) (sym (wl0176 (lit c4))) ▸
       at 4 2 (CS04⁻ ∷ S2 ∷ Toff204 ∷ S2⁻ ∷ []) (sym (wp0015 c4)) ▸
       at 3 2 (CS04⁻ ∷ S2⁻ ∷ []) (sym (wp0018 c4)) ▸
       at 2 2 (CS04⁻ ∷ Toff213 ∷ []) (lem-comm-TOFF213-CSd04 (lit c4)) ▸
       at 1 2 (CS04⁻ ∷ S2 ∷ []) (sym (wp0017 c4)) ▸
       at 0 2 (CS04⁻ ∷ CS13⁻ ∷ []) (sym (wp0016 c4)) ▸
       at 4 2 [] (wl0179 (lit c4)) ▸
       at 3 2 (Toff204 ∷ Toff213 ∷ []) (lem-tP-at02233440 c4) ▸ done

  b1 : Chain (CS04⁻ ∷ CS13⁻ ∷ S2 ∷ Toff204 ∷ Toff213 ∷ S2⁻ ∷ []) (Toff204 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ [])
  b1 = at 4 0 (S2⁻ ∷ S2 ∷ []) (sym (wl0179 (lit c4))) ▸
       at 1 2 (S2 ∷ CS13⁻ ∷ []) (wl0178 (lit c4)) ▸
       at 2 2 (Toff204 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-TOFF204 (lit c4)) ▸
       at 3 2 (S2⁻ ∷ CS13⁻ ∷ []) (wl0177 (lit c4)) ▸
       at 0 4 (Toff204 ∷ CCZ024 ∷ []) (wp0015 c4) ▸
       at 2 4 (Toff213 ∷ CCZ123 ∷ []) (wl0176 (lit c4)) ▸ done


-- QVQ @02233440: 3 steps
lem-QVQ-at02233440 : Ws → ⟪ (CCZ024 ∷ Toff213 ∷ CCZ123 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ Toff213 ∷ CCZ123 ∷ Toff204 ∷ []) ⟫ʷ
lem-QVQ-at02233440 c4 = run b0
  where
  b0 : Chain (CCZ024 ∷ Toff213 ∷ CCZ123 ∷ CCZ024 ∷ []) (Toff204 ∷ Toff213 ∷ CCZ123 ∷ Toff204 ∷ [])
  b0 = at 0 0 (Toff204 ∷ Toff204 ∷ []) (sym (wp0019 c4)) ▸
       at 1 4 (Toff213 ∷ CCZ123 ∷ Toff204 ∷ CCZ024 ∷ []) (sym (lem-VPQ-at02233440 c4)) ▸
       at 4 2 [] (wp0135 c4) ▸ done


-- box-cP @02233440: 12 steps
lem-box-cP-at02233440 : Ws → ⟪ (Bx2-1340 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ []) ⟫ʷ
lem-box-cP-at02233440 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx2-1340 ∷ []) (CCZ123 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ CCZ124 ∷ Toff124 ∷ CZ01 ∷ Toff124 ∷ CCZ124 ∷ CZ01 ∷ [])
  b0 = at 0 1 (CCZ123 ∷ Toff213 ∷ Bx1-240 ∷ Toff213 ∷ CCZ123 ∷ Bx1-240 ∷ []) (refl) ▸
       at 2 1 (CCZ124 ∷ Toff124 ∷ Bx2-10 ∷ Toff124 ∷ CCZ124 ∷ Bx2-10 ∷ []) (refl) ▸
       at 4 1 (CZ01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 2 6 (CCZ024 ∷ []) (sym (wp0767 c4)) ▸
       at 5 1 (CCZ124 ∷ Toff124 ∷ Bx2-10 ∷ Toff124 ∷ CCZ124 ∷ Bx2-10 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 10 1 (CZ01 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ123 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ CCZ124 ∷ Toff124 ∷ CZ01 ∷ Toff124 ∷ CCZ124 ∷ CZ01 ∷ []) (CCZ123 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ [])
  b1 = at 5 6 (CCZ024 ∷ []) (sym (wp0767 c4)) ▸
       at 2 4 (Toff204 ∷ Toff213 ∷ CCZ123 ∷ Toff204 ∷ []) (lem-QVQ-at02233440 c4) ▸
       at 1 2 (Toff204 ∷ Toff213 ∷ []) (lem-tP-at02233440 c4) ▸
       at 2 2 [] (wl0180 (lit c4)) ▸ done


-- pairs @02233440: 4 steps
lem-pairs-at02233440 : Ws → ⟪ (Bx2-1340 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4013 ∷ []) ⟫ʷ
lem-pairs-at02233440 c4 = run b0
  where
  b0 : Chain (Bx2-1340 ∷ []) (Bx2-4013 ∷ [])
  b0 = at 0 1 (Toff204 ∷ Bx2-1340 ∷ Toff204 ∷ []) (sym (lem-P-box-at02233440 c4)) ▸
       at 1 1 (CCZ123 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ []) (lem-box-cP-at02233440 c4) ▸
       at 4 2 [] (wp0019 c4) ▸
       at 0 4 (Bx2-4013 ∷ []) (sym (lem-box-tQ-at0214203143 c4)) ▸ done


-- box-perm-4312 @02233440: 2 steps
lem-box-perm-4312-at02233440 : Ws → ⟪ (Bx2-1340 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ []) ⟫ʷ
lem-box-perm-4312-at02233440 c4 = run b0
  where
  b0 : Chain (Bx2-1340 ∷ []) (Bx2-0413 ∷ [])
  b0 = at 0 1 (Bx2-4013 ∷ []) (lem-pairs-at02233440 c4) ▸
       at 0 1 (Bx2-0413 ∷ []) (lem-sym-ab-at0214203143 c4) ▸ done


-- nf-X-CS0@0: 115 steps
lem-nf-X-CS0at0 : Ws → ⟪ (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ CCZ013 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ CCZ013 ∷ S4 ∷ CS14 ∷ Bx2-0413 ∷ []) ⟫ʷ
lem-nf-X-CS0at0 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (run b14))))))))))))))
  where
  b0 : Chain (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CS14 ∷ []) (CCZ014 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ CCZ014 ∷ CCZ024 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ Toff213 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CS14 ∷ [])
  b0 = at 0 2 (CCZ014 ∷ []) (lem-S2-SBOX⟨2·0·41·3⟩ c4) ▸
       at 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 1 (CS03 ∷ []) (refl) ▸
       at 5 1 (CS03⁻ ∷ []) (refl) ▸
       at 1 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 4 2 (Toff214 ∷ Toff314 ∷ Toff213 ∷ []) (wl0747 (lit c4)) ▸
       at 3 2 (Toff214 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp0654 c4) ▸
       at 6 1 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (sym (wl0190 (lit c4))) ▸ done

  b1 : Chain (CCZ014 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ CCZ014 ∷ CCZ024 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ Toff213 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CS14 ∷ []) (CCZ014 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ CCZ014 ∷ Toff314 ∷ CCZ024 ∷ Toff213 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CS14 ∷ [])
  b1 = at 5 2 (K3 ∷ CCZ024 ∷ []) (wp0037 c4) ▸
       at 6 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 7 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 8 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 9 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 10 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 11 2 (K3⁻ ∷ CCZ024 ∷ []) (wp0033 c4) ▸
       at 5 7 (Toff314 ∷ []) (wl0190 (lit c4)) ▸ done

  b2 : Chain (CCZ014 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ CCZ014 ∷ Toff314 ∷ CCZ024 ∷ Toff213 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CS14 ∷ []) (CCZ014 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff213 ∷ Toff314 ∷ CCZ024 ∷ Toff213 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CS14 ∷ [])
  b2 = at 2 2 (Toff214 ∷ Toff213 ∷ []) (wl0197 (lit c4)) ▸
       at 4 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4) ▸
       at 3 2 (CS14 ∷ Toff213 ∷ []) (sym (wl0195 (lit c4))) ▸
       at 4 2 (CX04 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX04 (lit c4)) ▸
       at 5 2 (CS14⁻ ∷ Toff213 ∷ []) (sym (wl0194 (lit c4))) ▸
       at 6 2 (CX04 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX04 (lit c4)) ▸
       at 7 2 (CS01 ∷ Toff213 ∷ []) (sym (wl0193 (lit c4))) ▸
       at 3 5 (CCZ014 ∷ []) (sym (wp0041 c4)) ▸ done

  b3 : Chain (CCZ014 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff213 ∷ Toff314 ∷ CCZ024 ∷ Toff213 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CS14 ∷ []) (CCZ014 ∷ CCZ014 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CCZ024 ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CS14 ∷ [])
  b3 = at 4 2 (Toff214 ∷ Toff314 ∷ Toff213 ∷ []) (wl0747 (lit c4)) ▸
       at 2 3 (CCZ014 ∷ []) (sym (wp0044 c4)) ▸
       at 1 2 (CCZ014 ∷ CCZ024 ∷ []) (sym (wp0038 c4)) ▸
       at 3 1 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (sym (wl0190 (lit c4))) ▸
       at 2 2 (K3 ∷ CCZ024 ∷ []) (wp0037 c4) ▸
       at 3 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 4 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 5 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸ done

  b4 : Chain (CCZ014 ∷ CCZ014 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CCZ024 ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CS14 ∷ []) (CCZ014 ∷ CCZ014 ∷ Toff314 ∷ CCZ024 ∷ Toff213 ∷ CS03 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03⁻ ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CS14 ∷ [])
  b4 = at 6 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 7 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 8 2 (K3⁻ ∷ CCZ024 ∷ []) (wp0033 c4) ▸
       at 2 7 (Toff314 ∷ []) (wl0190 (lit c4)) ▸
       at 3 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 3 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 6 2 (CS03 ∷ Toff213 ∷ []) (sym (wl0196 (lit c4))) ▸
       at 5 2 (CS03 ∷ CCZ024 ∷ []) (wp0021 c4) ▸ done

  b5 : Chain (CCZ014 ∷ CCZ014 ∷ Toff314 ∷ CCZ024 ∷ Toff213 ∷ CS03 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03⁻ ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CS14 ∷ []) (CCZ014 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ CCZ014 ∷ K3 ∷ CCZ024 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ Toff213 ∷ CS03⁻ ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CS14 ∷ [])
  b5 = at 4 2 (CS03 ∷ Toff213 ∷ []) (sym (wl0196 (lit c4))) ▸
       at 3 2 (CS03 ∷ CCZ024 ∷ []) (wp0021 c4) ▸
       at 4 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 4 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 7 2 (Toff214 ∷ Toff314 ∷ Toff213 ∷ []) (wl0747 (lit c4)) ▸
       at 6 2 (Toff214 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp0654 c4) ▸
       at 9 1 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (sym (wl0190 (lit c4))) ▸
       at 8 2 (K3 ∷ CCZ024 ∷ []) (wp0037 c4) ▸ done

  b6 : Chain (CCZ014 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ CCZ014 ∷ K3 ∷ CCZ024 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ Toff213 ∷ CS03⁻ ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CS14 ∷ []) (CCZ014 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ024 ∷ Toff214 ∷ Toff213 ∷ CCZ014 ∷ Toff314 ∷ CCZ024 ∷ Toff213 ∷ CS03⁻ ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CS14 ∷ [])
  b6 = at 9 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 10 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 11 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 12 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 13 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 14 2 (K3⁻ ∷ CCZ024 ∷ []) (wp0033 c4) ▸
       at 8 7 (Toff314 ∷ []) (wl0190 (lit c4)) ▸
       at 5 2 (Toff214 ∷ Toff213 ∷ []) (wl0197 (lit c4)) ▸ done

  b7 : Chain (CCZ014 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ024 ∷ Toff214 ∷ Toff213 ∷ CCZ014 ∷ Toff314 ∷ CCZ024 ∷ Toff213 ∷ CS03⁻ ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CS14 ∷ []) (CCZ014 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ Toff314 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS03⁻ ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CS14 ∷ [])
  b7 = at 7 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4) ▸
       at 6 2 (CS14 ∷ Toff213 ∷ []) (sym (wl0195 (lit c4))) ▸
       at 7 2 (CX04 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX04 (lit c4)) ▸
       at 8 2 (CS14⁻ ∷ Toff213 ∷ []) (sym (wl0194 (lit c4))) ▸
       at 9 2 (CX04 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX04 (lit c4)) ▸
       at 10 2 (CS01 ∷ Toff213 ∷ []) (sym (wl0193 (lit c4))) ▸
       at 6 5 (CCZ014 ∷ []) (sym (wp0041 c4)) ▸
       at 7 2 (Toff214 ∷ Toff314 ∷ Toff213 ∷ []) (wl0747 (lit c4)) ▸ done

  b8 : Chain (CCZ014 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ Toff314 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS03⁻ ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CS14 ∷ []) (CCZ014 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ K3⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS03⁻ ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CS14 ∷ [])
  b8 = at 5 3 (CCZ014 ∷ []) (sym (wp0044 c4)) ▸
       at 4 2 (CCZ014 ∷ CCZ024 ∷ []) (sym (wp0038 c4)) ▸
       at 6 1 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (sym (wl0190 (lit c4))) ▸
       at 5 2 (K3 ∷ CCZ024 ∷ []) (wp0037 c4) ▸
       at 6 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 7 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 8 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 9 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸ done

  b9 : Chain (CCZ014 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ K3⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS03⁻ ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CS14 ∷ []) (CCZ014 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CCZ024 ∷ CS03⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CS14 ∷ [])
  b9 = at 10 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 11 2 (K3⁻ ∷ CCZ024 ∷ []) (wp0033 c4) ▸
       at 5 7 (Toff314 ∷ []) (wl0190 (lit c4)) ▸
       at 6 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 6 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 9 2 (CS03⁻ ∷ Toff213 ∷ []) (sym (wl0191 (lit c4))) ▸
       at 8 2 (CS03⁻ ∷ CCZ024 ∷ []) (wp0032 c4) ▸
       at 7 2 (CS03⁻ ∷ Toff213 ∷ []) (sym (wl0191 (lit c4))) ▸ done

  b10 : Chain (CCZ014 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CCZ024 ∷ CS03⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CS14 ∷ []) (CCZ014 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ CCZ013 ∷ CK40 ∷ CCZ013 ∷ CCZ024 ∷ Toff213 ∷ CS04 ∷ CCZ024 ∷ Toff213 ∷ CS04 ∷ CK40 ∷ S4 ∷ CS14 ∷ [])
  b10 = at 6 2 (CS03⁻ ∷ CCZ024 ∷ []) (wp0032 c4) ▸
       at 7 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 7 1 (Bx2-1340 ∷ []) (lem-box-perm-3421-at0210243143 c4) ▸
       at 7 2 (CCZ013 ∷ CK40 ∷ CCZ013 ∷ Bx2-1340 ∷ []) (lem-CKc-box-at02233440 c4) ▸
       at 10 1 (Bx2-0413 ∷ []) (lem-box-perm-4312-at02233440 c4) ▸
       at 10 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 13 2 (CS04 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CS04 (lit c4)) ▸
       at 12 2 (CS04 ∷ CCZ024 ∷ []) (wp0906 c4) ▸ done

  b11 : Chain (CCZ014 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ CCZ013 ∷ CK40 ∷ CCZ013 ∷ CCZ024 ∷ Toff213 ∷ CS04 ∷ CCZ024 ∷ Toff213 ∷ CS04 ∷ CK40 ∷ S4 ∷ CS14 ∷ []) (CCZ014 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ CCZ013 ∷ CK40 ∷ CCZ013 ∷ CS04 ∷ CS04 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CK40 ∷ S4 ∷ CS14 ∷ [])
  b11 = at 11 2 (CS04 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CS04 (lit c4)) ▸
       at 10 2 (CS04 ∷ CCZ024 ∷ []) (wp0906 c4) ▸
       at 11 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 11 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 14 2 (CS04 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CS04 (lit c4)) ▸
       at 13 2 (CS04 ∷ CCZ024 ∷ []) (wp0906 c4) ▸
       at 12 2 (CS04 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CS04 (lit c4)) ▸
       at 11 2 (CS04 ∷ CCZ024 ∷ []) (wp0906 c4) ▸ done

  b12 : Chain (CCZ014 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ CCZ013 ∷ CK40 ∷ CCZ013 ∷ CS04 ∷ CS04 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CK40 ∷ S4 ∷ CS14 ∷ []) (CCZ014 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ CCZ013 ∷ CK40 ∷ CCZ013 ∷ CS04 ∷ CS04 ∷ CCZ013 ∷ CK40 ∷ CCZ013 ∷ CCZ024 ∷ S4 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS14 ∷ [])
  b12 = at 12 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 12 1 (Bx2-1340 ∷ []) (lem-box-perm-3421-at0210243143 c4) ▸
       at 12 2 (CCZ013 ∷ CK40 ∷ CCZ013 ∷ Bx2-1340 ∷ []) (lem-CKc-box-at02233440 c4) ▸
       at 15 1 (Bx2-0413 ∷ []) (lem-box-perm-4312-at02233440 c4) ▸
       at 15 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 18 2 (S4 ∷ Toff213 ∷ []) (sym (wl0727 (lit c4))) ▸
       at 17 2 (S4 ∷ CCZ024 ∷ []) (wp0617 c4) ▸
       at 16 2 (S4 ∷ Toff213 ∷ []) (sym (wl0727 (lit c4))) ▸ done

  b13 : Chain (CCZ014 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ CCZ013 ∷ CK40 ∷ CCZ013 ∷ CS04 ∷ CS04 ∷ CCZ013 ∷ CK40 ∷ CCZ013 ∷ CCZ024 ∷ S4 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS14 ∷ []) (CCZ014 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ CCZ013 ∷ CK40 ∷ CCZ013 ∷ CS04 ∷ CS04 ∷ CCZ013 ∷ CK40 ∷ CCZ013 ∷ S4 ∷ CS14 ∷ Bx2-0413 ∷ [])
  b13 = at 15 2 (S4 ∷ CCZ024 ∷ []) (wp0617 c4) ▸
       at 16 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 16 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 19 2 (CS14 ∷ Toff213 ∷ []) (sym (wl0195 (lit c4))) ▸
       at 18 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 17 2 (CS14 ∷ Toff213 ∷ []) (sym (wl0195 (lit c4))) ▸
       at 16 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 17 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸ done

  b14 : Chain (CCZ014 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ CCZ013 ∷ CK40 ∷ CCZ013 ∷ CS04 ∷ CS04 ∷ CCZ013 ∷ CK40 ∷ CCZ013 ∷ S4 ∷ CS14 ∷ Bx2-0413 ∷ []) (Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ CCZ013 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ CCZ013 ∷ S4 ∷ CS14 ∷ Bx2-0413 ∷ [])
  b14 = at 0 2 [] (wp0161 c4) ▸
       at 7 3 (CS04 ∷ CS04 ∷ CCZ013 ∷ []) (wp0930 c4) ▸
       at 9 2 [] (wl0230 (lit c4)) ▸ done


-- F1-X-CS0@0: 86 steps
lem-F1-X-CS0at0 : Ws → ⟪ (CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CS14 ∷ []) ⟫ʷ
lem-F1-X-CS0at0 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (run b10))))))))))
  where
  b0 : Chain (CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb2-0-41-3 ∷ []) (CX40 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ CCZ014 ∷ CCZ024 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ Toff213 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b0 = at 5 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 7 1 (CS03 ∷ []) (refl) ▸
       at 9 1 (CS03⁻ ∷ []) (refl) ▸
       at 0 5 (CX40 ∷ []) (wp0931 c4) ▸
       at 1 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 4 2 (Toff214 ∷ Toff314 ∷ Toff213 ∷ []) (wl0747 (lit c4)) ▸
       at 3 2 (Toff214 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp0654 c4) ▸
       at 6 1 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (sym (wl0190 (lit c4))) ▸ done

  b1 : Chain (CX40 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ CCZ014 ∷ CCZ024 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ Toff213 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (CX40 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ CCZ014 ∷ Toff314 ∷ CCZ024 ∷ Toff213 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b1 = at 5 2 (K3 ∷ CCZ024 ∷ []) (wp0037 c4) ▸
       at 6 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 7 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 8 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 9 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 10 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 11 2 (K3⁻ ∷ CCZ024 ∷ []) (wp0033 c4) ▸
       at 5 7 (Toff314 ∷ []) (wl0190 (lit c4)) ▸ done

  b2 : Chain (CX40 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ CCZ014 ∷ Toff314 ∷ CCZ024 ∷ Toff213 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (CX40 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff213 ∷ Toff314 ∷ CCZ024 ∷ Toff213 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b2 = at 2 2 (Toff214 ∷ Toff213 ∷ []) (wl0197 (lit c4)) ▸
       at 4 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4) ▸
       at 3 2 (CS14 ∷ Toff213 ∷ []) (sym (wl0195 (lit c4))) ▸
       at 4 2 (CX04 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX04 (lit c4)) ▸
       at 5 2 (CS14⁻ ∷ Toff213 ∷ []) (sym (wl0194 (lit c4))) ▸
       at 6 2 (CX04 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX04 (lit c4)) ▸
       at 7 2 (CS01 ∷ Toff213 ∷ []) (sym (wl0193 (lit c4))) ▸
       at 3 5 (CCZ014 ∷ []) (sym (wp0041 c4)) ▸ done

  b3 : Chain (CX40 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff213 ∷ Toff314 ∷ CCZ024 ∷ Toff213 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (CX40 ∷ CCZ014 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CCZ024 ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b3 = at 4 2 (Toff214 ∷ Toff314 ∷ Toff213 ∷ []) (wl0747 (lit c4)) ▸
       at 2 3 (CCZ014 ∷ []) (sym (wp0044 c4)) ▸
       at 1 2 (CCZ014 ∷ CCZ024 ∷ []) (sym (wp0038 c4)) ▸
       at 3 1 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (sym (wl0190 (lit c4))) ▸
       at 2 2 (K3 ∷ CCZ024 ∷ []) (wp0037 c4) ▸
       at 3 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 4 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 5 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸ done

  b4 : Chain (CX40 ∷ CCZ014 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CCZ024 ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (CX40 ∷ CCZ014 ∷ Toff314 ∷ CCZ024 ∷ Toff213 ∷ CS03 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b4 = at 6 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 7 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 8 2 (K3⁻ ∷ CCZ024 ∷ []) (wp0033 c4) ▸
       at 2 7 (Toff314 ∷ []) (wl0190 (lit c4)) ▸
       at 3 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 3 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 6 2 (CS03 ∷ Toff213 ∷ []) (sym (wl0196 (lit c4))) ▸
       at 5 2 (CS03 ∷ CCZ024 ∷ []) (wp0021 c4) ▸ done

  b5 : Chain (CX40 ∷ CCZ014 ∷ Toff314 ∷ CCZ024 ∷ Toff213 ∷ CS03 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03⁻ ∷ []) (CX40 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ CCZ014 ∷ K3 ∷ CCZ024 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ Toff213 ∷ CS03⁻ ∷ [])
  b5 = at 4 2 (CS03 ∷ Toff213 ∷ []) (sym (wl0196 (lit c4))) ▸
       at 3 2 (CS03 ∷ CCZ024 ∷ []) (wp0021 c4) ▸
       at 4 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 4 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 7 2 (Toff214 ∷ Toff314 ∷ Toff213 ∷ []) (wl0747 (lit c4)) ▸
       at 6 2 (Toff214 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp0654 c4) ▸
       at 9 1 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (sym (wl0190 (lit c4))) ▸
       at 8 2 (K3 ∷ CCZ024 ∷ []) (wp0037 c4) ▸ done

  b6 : Chain (CX40 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ CCZ014 ∷ K3 ∷ CCZ024 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ Toff213 ∷ CS03⁻ ∷ []) (CX40 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ024 ∷ Toff214 ∷ Toff213 ∷ CCZ014 ∷ Toff314 ∷ CCZ024 ∷ Toff213 ∷ CS03⁻ ∷ [])
  b6 = at 9 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 10 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 11 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 12 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 13 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 14 2 (K3⁻ ∷ CCZ024 ∷ []) (wp0033 c4) ▸
       at 8 7 (Toff314 ∷ []) (wl0190 (lit c4)) ▸
       at 5 2 (Toff214 ∷ Toff213 ∷ []) (wl0197 (lit c4)) ▸ done

  b7 : Chain (CX40 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ024 ∷ Toff214 ∷ Toff213 ∷ CCZ014 ∷ Toff314 ∷ CCZ024 ∷ Toff213 ∷ CS03⁻ ∷ []) (CX40 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ Toff314 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS03⁻ ∷ [])
  b7 = at 7 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4) ▸
       at 6 2 (CS14 ∷ Toff213 ∷ []) (sym (wl0195 (lit c4))) ▸
       at 7 2 (CX04 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX04 (lit c4)) ▸
       at 8 2 (CS14⁻ ∷ Toff213 ∷ []) (sym (wl0194 (lit c4))) ▸
       at 9 2 (CX04 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX04 (lit c4)) ▸
       at 10 2 (CS01 ∷ Toff213 ∷ []) (sym (wl0193 (lit c4))) ▸
       at 6 5 (CCZ014 ∷ []) (sym (wp0041 c4)) ▸
       at 7 2 (Toff214 ∷ Toff314 ∷ Toff213 ∷ []) (wl0747 (lit c4)) ▸ done

  b8 : Chain (CX40 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ Toff314 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS03⁻ ∷ []) (CX40 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ K3⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS03⁻ ∷ [])
  b8 = at 5 3 (CCZ014 ∷ []) (sym (wp0044 c4)) ▸
       at 4 2 (CCZ014 ∷ CCZ024 ∷ []) (sym (wp0038 c4)) ▸
       at 6 1 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (sym (wl0190 (lit c4))) ▸
       at 5 2 (K3 ∷ CCZ024 ∷ []) (wp0037 c4) ▸
       at 6 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 7 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 8 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 9 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸ done

  b9 : Chain (CX40 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ K3⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS03⁻ ∷ []) (CX40 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CCZ024 ∷ CS03⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ [])
  b9 = at 10 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 11 2 (K3⁻ ∷ CCZ024 ∷ []) (wp0033 c4) ▸
       at 5 7 (Toff314 ∷ []) (wl0190 (lit c4)) ▸
       at 6 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 6 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 9 2 (CS03⁻ ∷ Toff213 ∷ []) (sym (wl0191 (lit c4))) ▸
       at 8 2 (CS03⁻ ∷ CCZ024 ∷ []) (wp0032 c4) ▸
       at 7 2 (CS03⁻ ∷ Toff213 ∷ []) (sym (wl0191 (lit c4))) ▸ done

  b10 : Chain (CX40 ∷ CCZ014 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CCZ024 ∷ CS03⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CS14 ∷ [])
  b10 = at 6 2 (CS03⁻ ∷ CCZ024 ∷ []) (wp0032 c4) ▸
       at 7 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 1 3 (Toff314 ∷ CS03 ∷ CCZ014 ∷ []) (wp0651 c4) ▸
       at 3 2 [] (wp0161 c4) ▸
       at 0 5 (Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ CCZ013 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ CCZ013 ∷ S4 ∷ CS14 ∷ []) (wp0932 c4) ▸
       at 0 14 (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CS14 ∷ []) (sym (lem-nf-X-CS0at0 c4)) ▸ done


-- box-perm-3421 @243243: 2 steps
lem-box-perm-3421-at243243 : Ws → ⟪ (Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2341 ∷ []) ⟫ʷ
lem-box-perm-3421-at243243 c4 = run b0
  where
  b0 : Chain (Bx0-1423 ∷ []) (Bx0-2341 ∷ [])
  b0 = at 0 1 (Bx0-4123 ∷ []) (lem-sym-ab-at243243 c4) ▸
       at 0 1 (Bx0-2341 ∷ []) (lem-pairs-at14213243 c4) ▸ done


-- box-perm-1324 @12233441: 1 steps
lem-box-perm-1324-at12233441 : Ws → ⟪ (Bx0-2341 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ []) ⟫ʷ
lem-box-perm-1324-at12233441 c4 = run b0
  where
  b0 : Chain (Bx0-2341 ∷ []) (Bx0-2431 ∷ [])
  b0 = at 0 1 (Bx0-2431 ∷ []) (lem-sym-bc-at12233441 c4) ▸ done

