{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D067 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0230 ; wl0256 ; wl0263 ; wl0348 ; wl0460 ; wl0461 ; wl0499 ; wl0501 ; wl0516 ; wl0541 ; wp0007 ; wp0053 ; wp0061 ; wp0065 ; wp0106 ; wp0107 ; wp0108 ; wp0161 ; wp0311 ; wp0376 ; wp0391 ; wl0327 ; wl0645 ; wl0666 ; wp0072 ; wp0299 ; wp0484 ; wp0485 ; wp0486 ; wp0491 ; wp0492 ; wp0493 ; wp0538 ; wp0539 ; wl0196 ; wl0245 ; wl0305 ; wl0448 ; wl0778 ; wl0779 ; wl0806 ; wl0807 ; wl0808 ; wl0871 ; wl0872 ; wp0034 ; wp0036 ; wp0038 ; wp0041 ; wp0062 ; wp0064 ; wp0090 ; wp0095 ; wp0298 ; wp0352 ; wp0702 ; wp0716 ; wl0183 ; wl0184 ; wl0185 ; wl0186 ; wl0187 ; wl0190 ; wl0217 ; wl0221 ; wl0222 ; wl0241 ; wl0244 ; wl0246 ; wl0247 ; wl0469 ; wl0703 ; wl0745 ; wl0906 ; wl0942 ; wl0979 ; wl0981 ; wl0983 ; wl0986 ; wl1025 ; wl1026 ; wl1027 ; wl1028 ; wl1029 ; wl1030 ; wl1037 ; wp0020 ; wp0021 ; wp0022 ; wp0023 ; wp0033 ; wp0035 ; wp0037 ; wp0063 ; wp0081 ; wp0087 ; wp0088 ; wp0089 ; wp0094 ; wp0097 ; wp0277 ; wp0657 ; wp0659 ; wp0663 ; wp0673 ; wp0768 ; wp0785 ; wp0786 ; wp0787 ; wp0828 ; wp0829 ; wp0830 ; wp0831 ; wp0832 ; wp0833 ; wp0834 ; wp0842 ; wp0843 ; wp0845 ; wl0191 ; wl0193 ; wl0194 ; wl0195 ; wl0197 ; wl0214 ; wl0219 ; wl0220 ; wl0325 ; wl0445 ; wl0446 ; wl0447 ; wl0449 ; wl0450 ; wl1000 ; wl1083 ; wl1084 ; wl1085 ; wp0032 ; wp0044 ; wp0060 ; wp0066 ; wp0069 ; wp0070 ; wp0074 ; wp0122 ; wp0300 ; wp0651 ; wp0883 ; wp0884 ; wp0885 ; wl0747 ; wp0654 ; wp0805 ; wp0806 ; wp0931 ; wp0932 ; wl1142 ; wl1143 ; wl1147 ; wl1148 ; wl1169 ; wp0954)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-inv-SBOX⟨2·0·41·3⟩ ; lem-invr-SBOX⟨2·0·41·3⟩)
open import Examples.Groups.Clifford+CS.Five.D.D006 using (lem-box-tQ ; lem-box-tQ-at0330)
open import Examples.Groups.Clifford+CS.Five.D.D014 using (lem-box-cP-at032032 ; lem-box-cP-at04203243)
open import Examples.Groups.Clifford+CS.Five.D.D016 using (lem-box-cP-at0210243143 ; lem-box-cP-at0314203142 ; lem-box-cP-at122441 ; lem-box-cP-at243243 ; lem-box-perm-2314-at03102132)
open import Examples.Groups.Clifford+CS.Five.D.D018 using (lem-CSdu-box-3-at043043 ; lem-CSu-box-3-at043043 ; lem-box-perm-1324-at043043 ; lem-box-perm-3124 ; lem-box-perm-3124-at0330 ; lem-box2-at043043)
open import Examples.Groups.Clifford+CS.Five.D.D019 using (lem-CSdu-box-3-at0210243143 ; lem-CSdu-box-3-at0314213042 ; lem-CSdu-box-3-at122441 ; lem-CSu-box-3-at0210243143 ; lem-CSu-box-3-at0314213042 ; lem-CSu-box-3-at122441 ; lem-box-perm-1324-at0314213042 ; lem-box-perm-2314-at0210243143 ; lem-box-perm-3124-at0214213043 ; lem-box2-at0314213042)
open import Examples.Groups.Clifford+CS.Five.D.D020 using (lem-box-perm-1324-at0330 ; lem-box-perm-2314-at132132)
open import Examples.Groups.Clifford+CS.Five.D.D025 using (lem-F0-R ; lem-F0-R-at14213243 ; lem-F5-01 ; lem-box-perm-1342-at0210243143 ; lem-box-perm-1423-at021021 ; lem-box-perm-2431 ; lem-box-perm-4132-at122441)
open import Examples.Groups.Clifford+CS.Five.D.D026 using (lem-AX-S23)
open import Examples.Groups.Clifford+CS.Five.D.D037 using (lem-F0-B ; lem-F0-B-at14213243 ; lem-XCKX-box-2-at0210243143 ; lem-XCKX-box-2-at122441 ; lem-XCKX-box-2-at243243 ; lem-box-box-1-at03102132 ; lem-box-box-2)
open import Examples.Groups.Clifford+CS.Five.D.D038 using (lem-F4-CS0-CS2)
open import Examples.Groups.Clifford+CS.Five.D.D039 using (lem-nf-X-CS0at0 ; lem-nf-X-CS0at1 ; lem-nf-X-CS0at2 ; lem-nf-X-CS1at0 ; lem-nf-X-CS1at1)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CS13-CCZ024 ; lem-comm-CS24-CCZ013 ; lem-comm-CSd13-CCZ024 ; lem-comm-CSd24-CCZ013 ; lem-comm-CX04-TOFF213 ; lem-comm-CX12-CCZ034 ; lem-comm-CX13-CCZ024 ; lem-comm-CZ13-CCZ024 ; lem-comm-TOFF013-CSd24)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-CCZ014-CX23 ; lem-comm-CCZ024-CX13 ; lem-comm-CCZ034-CS12 ; lem-comm-CX04-TOFF312 ; lem-comm-TOFF013-CS24 ; lem-comm-TOFF013-CX24 ; lem-comm-TOFF213-CX04)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-comm-TOFF023-CX14)

-- CXuA-S: 44 steps
lem-CXuA-S : Ws → ⟪ (CX34 ∷ Sb3-0-12-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-12-4 ∷ CX34 ∷ []) ⟫ʷ
lem-CXuA-S c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (run b5)))))
  where
  b0 : Chain (CX34 ∷ Sb3-0-12-4 ∷ []) (Bx3-1204 ∷ Bx4-1203 ∷ Toff412 ∷ CS04 ∷ Toff412 ∷ Bx4-1203 ∷ CS04⁻ ∷ CX34 ∷ [])
  b0 = at 1 1 (Bx3-0124 ∷ Toff412 ∷ Sb3-0-4-2 ∷ Toff412 ∷ Sb⁻3-0-4-2 ∷ []) (refl) ▸
       at 3 1 (CS04 ∷ []) (refl) ▸
       at 5 1 (CS04⁻ ∷ []) (refl) ▸
       at 1 1 (Bx3-1204 ∷ []) (lem-box-perm-2314-at03102132 c4) ▸
       at 2 0 (CX34 ∷ CX34 ∷ []) (sym (wl0541 (lit c4))) ▸
       at 0 3 (Bx3-1204 ∷ Bx4-1203 ∷ []) (lem-F0-B c4) ▸
       at 2 5 (Toff412 ∷ CS04 ∷ Toff412 ∷ CS04⁻ ∷ Bx4-1203 ∷ CX34 ∷ []) (lem-F0-R c4) ▸
       at 5 2 (Bx4-1203 ∷ CS04⁻ ∷ []) (lem-CSdu-box-3-at043043 c4) ▸ done

  b1 : Chain (Bx3-1204 ∷ Bx4-1203 ∷ Toff412 ∷ CS04 ∷ Toff412 ∷ Bx4-1203 ∷ CS04⁻ ∷ CX34 ∷ []) (Bx3-1204 ∷ Bx4-1203 ∷ Toff412 ∷ CS04 ∷ CCZ014 ∷ Toff412 ∷ CS12 ∷ Toff423 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ CCZ014 ∷ Toff423 ∷ CS04⁻ ∷ CX34 ∷ [])
  b1 = at 5 1 (Bx4-1023 ∷ []) (lem-box-perm-1324-at043043 c4) ▸
       at 5 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at04203243 c4) ▸
       at 4 2 (CCZ014 ∷ Toff412 ∷ CCZ012 ∷ []) (sym (wp0376 c4)) ▸
       at 6 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wl0348 (lit c4)) ▸
       at 10 2 (Toff423 ∷ CS02 ∷ []) (wp0311 c4) ▸
       at 9 2 (Toff423 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Toffᵗ)) ▸
       at 8 2 (Toff423 ∷ CS12⁻ ∷ []) (wl0460 (lit c4)) ▸
       at 7 2 (Toff423 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Toffᵗ)) ▸ done

  b2 : Chain (Bx3-1204 ∷ Bx4-1203 ∷ Toff412 ∷ CS04 ∷ CCZ014 ∷ Toff412 ∷ CS12 ∷ Toff423 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ CCZ014 ∷ Toff423 ∷ CS04⁻ ∷ CX34 ∷ []) (Bx3-1204 ∷ Bx4-1203 ∷ Toff412 ∷ Bx4-1203 ∷ CS04 ∷ Toff412 ∷ CS04⁻ ∷ CX34 ∷ [])
  b2 = at 6 2 (Toff423 ∷ CS12 ∷ []) (wl0461 (lit c4)) ▸
       at 7 5 (CCZ012 ∷ []) (sym (wl0348 (lit c4))) ▸
       at 5 2 (Toff423 ∷ Toff412 ∷ []) (wl0516 (lit c4)) ▸
       at 6 3 (CCZ014 ∷ Toff412 ∷ []) (sym (wp0391 c4)) ▸
       at 7 2 (Toff423 ∷ Toff412 ∷ []) (wl0516 (lit c4)) ▸
       at 4 4 (Bx4-1023 ∷ []) (sym (lem-box-cP-at04203243 c4)) ▸
       at 4 1 (Bx4-1203 ∷ []) (sym (lem-box-perm-1324-at043043 c4)) ▸
       at 3 2 (Bx4-1203 ∷ CS04 ∷ []) (lem-CSu-box-3-at043043 c4) ▸ done

  b3 : Chain (Bx3-1204 ∷ Bx4-1203 ∷ Toff412 ∷ Bx4-1203 ∷ CS04 ∷ Toff412 ∷ CS04⁻ ∷ CX34 ∷ []) (Bx3-1204 ∷ Bx4-1203 ∷ CCZ014 ∷ Toff412 ∷ CS12 ∷ Toff423 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ CCZ014 ∷ Toff423 ∷ CS04 ∷ Toff412 ∷ CS04⁻ ∷ CX34 ∷ [])
  b3 = at 3 1 (Bx4-1023 ∷ []) (lem-box-perm-1324-at043043 c4) ▸
       at 3 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at04203243 c4) ▸
       at 2 2 (CCZ014 ∷ Toff412 ∷ CCZ012 ∷ []) (sym (wp0376 c4)) ▸
       at 4 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wl0348 (lit c4)) ▸
       at 8 2 (Toff423 ∷ CS02 ∷ []) (wp0311 c4) ▸
       at 7 2 (Toff423 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Toffᵗ)) ▸
       at 6 2 (Toff423 ∷ CS12⁻ ∷ []) (wl0460 (lit c4)) ▸
       at 5 2 (Toff423 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Toffᵗ)) ▸ done

  b4 : Chain (Bx3-1204 ∷ Bx4-1203 ∷ CCZ014 ∷ Toff412 ∷ CS12 ∷ Toff423 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ CCZ014 ∷ Toff423 ∷ CS04 ∷ Toff412 ∷ CS04⁻ ∷ CX34 ∷ []) (Bx3-1204 ∷ Toff412 ∷ CS04 ∷ Toff412 ∷ CS04⁻ ∷ CX34 ∷ [])
  b4 = at 4 2 (Toff423 ∷ CS12 ∷ []) (wl0461 (lit c4)) ▸
       at 5 5 (CCZ012 ∷ []) (sym (wl0348 (lit c4))) ▸
       at 3 2 (Toff423 ∷ Toff412 ∷ []) (wl0516 (lit c4)) ▸
       at 4 3 (CCZ014 ∷ Toff412 ∷ []) (sym (wp0391 c4)) ▸
       at 5 2 (Toff423 ∷ Toff412 ∷ []) (wl0516 (lit c4)) ▸
       at 2 4 (Bx4-1023 ∷ []) (sym (lem-box-cP-at04203243 c4)) ▸
       at 2 1 (Bx4-1203 ∷ []) (sym (lem-box-perm-1324-at043043 c4)) ▸
       at 1 2 [] (lem-box2-at043043 c4) ▸ done

  b5 : Chain (Bx3-1204 ∷ Toff412 ∷ CS04 ∷ Toff412 ∷ CS04⁻ ∷ CX34 ∷ []) (Sb3-0-12-4 ∷ CX34 ∷ [])
  b5 = at 0 1 (Bx3-0124 ∷ []) (lem-box-perm-3124-at0330 c4) ▸
       at 2 1 (Sb3-0-4-2 ∷ []) (refl) ▸
       at 4 1 (Sb⁻3-0-4-2 ∷ []) (refl) ▸
       at 0 5 (Sb3-0-12-4 ∷ []) (refl) ▸ done

-- F4-K0-CS1: 11 steps
lem-F4-K0-CS1 : Ws → ⟪ (X4 ∷ CK40 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K0-CS1 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (X4 ∷ CK40 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  b0 = at 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 5 1 (CS13 ∷ []) (refl) ▸
       at 7 1 (CS13⁻ ∷ []) (refl) ▸
       at 0 4 (Bx0-1423 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (lem-XCKX-box-2-at243243 c4) ▸
       at 1 4 (Toff324 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (sym (wp0484 c4)) ▸
       at 2 4 (CS13 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (sym (wp0485 c4)) ▸
       at 3 4 (Toff324 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (sym (wp0484 c4)) ▸
       at 4 4 (CS13⁻ ∷ X4 ∷ CK40 ∷ X4 ∷ []) (sym (wp0486 c4)) ▸ done

  b1 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CK40 ∷ X4 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  b1 = at 2 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 0 5 (Sb0-1-42-3 ∷ []) (refl) ▸ done

-- F4-K0-CS2: 11 steps
lem-F4-K0-CS2 : Ws → ⟪ (X4 ∷ CK40 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K0-CS2 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (X4 ∷ CK40 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  b0 = at 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 5 1 (CS12 ∷ []) (refl) ▸
       at 7 1 (CS12⁻ ∷ []) (refl) ▸
       at 0 4 (Bx0-2431 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (lem-XCKX-box-2-at122441 c4) ▸
       at 1 4 (Toff134 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (sym (wp0491 c4)) ▸
       at 2 4 (CS12 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (sym (wp0492 c4)) ▸
       at 3 4 (Toff134 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (sym (wp0491 c4)) ▸
       at 4 4 (CS12⁻ ∷ X4 ∷ CK40 ∷ X4 ∷ []) (sym (wp0493 c4)) ▸ done

  b1 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CK40 ∷ X4 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  b1 = at 2 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 0 5 (Sb0-2-43-1 ∷ []) (refl) ▸ done

-- F4-K2-CS0: 11 steps
lem-F4-K2-CS0 : Ws → ⟪ (X4 ∷ CK42 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K2-CS0 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (X4 ∷ CK42 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  b0 = at 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 5 1 (CS03 ∷ []) (refl) ▸
       at 7 1 (CS03⁻ ∷ []) (refl) ▸
       at 0 4 (Bx2-0413 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lem-XCKX-box-2-at0210243143 c4) ▸
       at 1 4 (Toff314 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (sym (wl0666 (lit c4))) ▸
       at 2 4 (CS03 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (sym (wp0538 c4)) ▸
       at 3 4 (Toff314 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (sym (wl0666 (lit c4))) ▸
       at 4 4 (CS03⁻ ∷ X4 ∷ CK42 ∷ X4 ∷ []) (sym (wp0539 c4)) ▸ done

  b1 : Chain (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CK42 ∷ X4 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  b1 = at 2 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 4 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 0 5 (Sb2-0-41-3 ∷ []) (refl) ▸ done

-- CXuA-S @14213243: 44 steps
lem-CXuA-S-at14213243 : Ws → ⟪ (CX23 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ CX23 ∷ []) ⟫ʷ
lem-CXuA-S-at14213243 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (run b5)))))
  where
  b0 : Chain (CX23 ∷ Sb2-0-41-3 ∷ []) (Bx2-4103 ∷ Bx3-4102 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ Bx3-4102 ∷ CS03⁻ ∷ CX23 ∷ [])
  b0 = at 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 1 (CS03 ∷ []) (refl) ▸
       at 5 1 (CS03⁻ ∷ []) (refl) ▸
       at 1 1 (Bx2-4103 ∷ []) (lem-box-perm-2314-at0210243143 c4) ▸
       at 2 0 (CX23 ∷ CX23 ∷ []) (sym (wl0806 (lit c4))) ▸
       at 0 3 (Bx2-4103 ∷ Bx3-4102 ∷ []) (lem-F0-B-at14213243 c4) ▸
       at 2 5 (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Bx3-4102 ∷ CX23 ∷ []) (lem-F0-R-at14213243 c4) ▸
       at 5 2 (Bx3-4102 ∷ CS03⁻ ∷ []) (lem-CSdu-box-3-at0314213042 c4) ▸ done

  b1 : Chain (Bx2-4103 ∷ Bx3-4102 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ Bx3-4102 ∷ CS03⁻ ∷ CX23 ∷ []) (Bx2-4103 ∷ Bx3-4102 ∷ Toff314 ∷ CS03 ∷ CCZ034 ∷ Toff314 ∷ CS14 ∷ Toff312 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ CCZ034 ∷ Toff312 ∷ CS03⁻ ∷ CX23 ∷ [])
  b1 = at 5 1 (Bx3-4012 ∷ []) (lem-box-perm-1324-at0314213042 c4) ▸
       at 5 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0314203142 c4) ▸
       at 4 2 (CCZ034 ∷ Toff314 ∷ CCZ014 ∷ []) (sym (wp0702 c4)) ▸
       at 6 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4) ▸
       at 10 2 (Toff312 ∷ CS01 ∷ []) (wl0501 (lit c4)) ▸
       at 9 2 (Toff312 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF312 (lit c4)) ▸
       at 8 2 (Toff312 ∷ CS14⁻ ∷ []) (wl0778 (lit c4)) ▸
       at 7 2 (Toff312 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF312 (lit c4)) ▸ done

  b2 : Chain (Bx2-4103 ∷ Bx3-4102 ∷ Toff314 ∷ CS03 ∷ CCZ034 ∷ Toff314 ∷ CS14 ∷ Toff312 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ CCZ034 ∷ Toff312 ∷ CS03⁻ ∷ CX23 ∷ []) (Bx2-4103 ∷ Bx3-4102 ∷ Toff314 ∷ Bx3-4102 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CX23 ∷ [])
  b2 = at 6 2 (Toff312 ∷ CS14 ∷ []) (wl0499 (lit c4)) ▸
       at 7 5 (CCZ014 ∷ []) (sym (wp0041 c4)) ▸
       at 5 2 (Toff312 ∷ Toff314 ∷ []) (sym (wl0779 (lit c4))) ▸
       at 6 3 (CCZ034 ∷ Toff314 ∷ []) (sym (wp0716 c4)) ▸
       at 7 2 (Toff312 ∷ Toff314 ∷ []) (sym (wl0779 (lit c4))) ▸
       at 4 4 (Bx3-4012 ∷ []) (sym (lem-box-cP-at0314203142 c4)) ▸
       at 4 1 (Bx3-4102 ∷ []) (sym (lem-box-perm-1324-at0314213042 c4)) ▸
       at 3 2 (Bx3-4102 ∷ CS03 ∷ []) (lem-CSu-box-3-at0314213042 c4) ▸ done

  b3 : Chain (Bx2-4103 ∷ Bx3-4102 ∷ Toff314 ∷ Bx3-4102 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CX23 ∷ []) (Bx2-4103 ∷ Bx3-4102 ∷ CCZ034 ∷ Toff314 ∷ CS14 ∷ Toff312 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ CCZ034 ∷ Toff312 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CX23 ∷ [])
  b3 = at 3 1 (Bx3-4012 ∷ []) (lem-box-perm-1324-at0314213042 c4) ▸
       at 3 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0314203142 c4) ▸
       at 2 2 (CCZ034 ∷ Toff314 ∷ CCZ014 ∷ []) (sym (wp0702 c4)) ▸
       at 4 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4) ▸
       at 8 2 (Toff312 ∷ CS01 ∷ []) (wl0501 (lit c4)) ▸
       at 7 2 (Toff312 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF312 (lit c4)) ▸
       at 6 2 (Toff312 ∷ CS14⁻ ∷ []) (wl0778 (lit c4)) ▸
       at 5 2 (Toff312 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF312 (lit c4)) ▸ done

  b4 : Chain (Bx2-4103 ∷ Bx3-4102 ∷ CCZ034 ∷ Toff314 ∷ CS14 ∷ Toff312 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ CCZ034 ∷ Toff312 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CX23 ∷ []) (Bx2-4103 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CX23 ∷ [])
  b4 = at 4 2 (Toff312 ∷ CS14 ∷ []) (wl0499 (lit c4)) ▸
       at 5 5 (CCZ014 ∷ []) (sym (wp0041 c4)) ▸
       at 3 2 (Toff312 ∷ Toff314 ∷ []) (sym (wl0779 (lit c4))) ▸
       at 4 3 (CCZ034 ∷ Toff314 ∷ []) (sym (wp0716 c4)) ▸
       at 5 2 (Toff312 ∷ Toff314 ∷ []) (sym (wl0779 (lit c4))) ▸
       at 2 4 (Bx3-4012 ∷ []) (sym (lem-box-cP-at0314203142 c4)) ▸
       at 2 1 (Bx3-4102 ∷ []) (sym (lem-box-perm-1324-at0314213042 c4)) ▸
       at 1 2 [] (lem-box2-at0314213042 c4) ▸ done

  b5 : Chain (Bx2-4103 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CX23 ∷ []) (Sb2-0-41-3 ∷ CX23 ∷ [])
  b5 = at 0 1 (Bx2-0413 ∷ []) (lem-box-perm-3124-at0214213043 c4) ▸
       at 2 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 4 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 0 5 (Sb2-0-41-3 ∷ []) (refl) ▸ done

-- F4-CS2-CS0: 284 steps
lem-F4-CS2-CS0 : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS2-CS0 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (run b35)))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (X4 ∷ Sb0-2-43-1 ∷ CCZ024 ∷ Toff213 ∷ X4 ∷ CZ02 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b0 = at 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 5 1 (CS03 ∷ []) (refl) ▸
       at 7 1 (CS03⁻ ∷ []) (refl) ▸
       at 3 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 2 2 (CCZ024 ∷ X4 ∷ CZ02 ∷ []) (sym (wp0020 c4)) ▸
       at 4 2 (Toff213 ∷ CZ02 ∷ CCZ013 ∷ []) (wl0183 (lit c4)) ▸
       at 3 2 (Toff213 ∷ X4 ∷ []) (sym (c₄ ((K ↑ • CCZ • K ↑ • iI) ↑) (X))) ▸
       at 6 1 (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ []) (wl0184 (lit c4)) ▸ done

  b1 : Chain (X4 ∷ Sb0-2-43-1 ∷ CCZ024 ∷ Toff213 ∷ X4 ∷ CZ02 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (X4 ∷ Sb0-2-43-1 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ X4 ∷ CZ02 ∷ CZ02 ∷ CCZ013 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b1 = at 10 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸
       at 9 2 (CCZ024 ∷ CX01 ∷ []) (sym (wp0022 c4)) ▸
       at 8 2 (CCZ024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-CCZ024 (lit c4)) ▸
       at 7 2 (CCZ024 ∷ CX01 ∷ []) (sym (wp0022 c4)) ▸
       at 6 2 (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 (lit c4)) ▸
       at 7 5 (CCZ013 ∷ []) (sym (wl0184 (lit c4))) ▸
       at 5 2 (CCZ024 ∷ CZ02 ∷ []) (sym (wp0023 c4)) ▸
       at 4 2 (CCZ024 ∷ X4 ∷ CZ02 ∷ []) (sym (wp0020 c4)) ▸ done

  b2 : Chain (X4 ∷ Sb0-2-43-1 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ X4 ∷ CZ02 ∷ CZ02 ∷ CCZ013 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS12⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b2 = at 5 3 (X4 ∷ []) (wl0185 (lit c4)) ▸
       at 6 2 (Toff213 ∷ CCZ013 ∷ []) (wl0186 (lit c4)) ▸
       at 5 2 (Toff213 ∷ X4 ∷ []) (sym (c₄ ((K ↑ • CCZ • K ↑ • iI) ↑) (X))) ▸
       at 2 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 5 1 (CS12⁻ ∷ []) (refl) ▸
       at 5 2 (Bx2-0413 ∷ CS12⁻ ∷ []) (lem-CSdu-box-3-at0210243143 c4) ▸
       at 5 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸ done

  b3 : Chain (X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS12⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ CCZ024 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS12⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b3 = at 4 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 10 2 (CCZ024 ∷ K1⁻ ∷ []) (sym (wp0088 c4)) ▸
       at 9 2 (CCZ024 ∷ CS14 ∷ []) (sym (wp0034 c4)) ▸
       at 8 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 7 2 (CCZ024 ∷ CS34⁻ ∷ []) (sym (wp0035 c4)) ▸
       at 6 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 4 2 (CCZ024 ∷ K1 ∷ []) (sym (wp0089 c4)) ▸ done

  b4 : Chain (X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ CCZ024 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS12⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ CCZ024 ∷ Toff213 ∷ K1 ∷ CS34 ∷ CX13 ∷ CCZ024 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff234 ∷ CCZ034 ∷ Toff213 ∷ CS12⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b4 = at 5 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 5 2 (Toff213 ∷ Toff134 ∷ Toff234 ∷ []) (wl1025 (lit c4)) ▸
       at 7 2 (CCZ024 ∷ Toff234 ∷ CCZ034 ∷ []) (sym (wp0768 c4)) ▸
       at 6 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 12 2 (CCZ024 ∷ K1⁻ ∷ []) (sym (wp0088 c4)) ▸
       at 11 2 (CCZ024 ∷ CS14 ∷ []) (sym (wp0034 c4)) ▸
       at 10 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 9 2 (CCZ024 ∷ CS34⁻ ∷ []) (sym (wp0035 c4)) ▸ done

  b5 : Chain (X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ CCZ024 ∷ Toff213 ∷ K1 ∷ CS34 ∷ CX13 ∷ CCZ024 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff234 ∷ CCZ034 ∷ Toff213 ∷ CS12⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff134 ∷ Toff234 ∷ CS34 ∷ CX04 ∷ Toff213 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ CS12⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b5 = at 8 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 7 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 6 2 (CCZ024 ∷ K1 ∷ []) (sym (wp0089 c4)) ▸
       at 7 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 9 1 (CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ []) (wp0352 c4) ▸
       at 13 2 (Toff213 ∷ CS03 ∷ []) (wl0196 (lit c4)) ▸
       at 12 2 (Toff213 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF213 (lit c4)) ▸
       at 11 2 (Toff213 ∷ CS34⁻ ∷ []) (wl0807 (lit c4)) ▸ done

  b6 : Chain (X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff134 ∷ Toff234 ∷ CS34 ∷ CX04 ∷ Toff213 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ CS12⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (X4 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Bx2-0413 ∷ Toff134 ∷ CCZ034 ∷ CS12⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b6 = at 10 2 (Toff213 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF213 (lit c4)) ▸
       at 9 2 (Toff213 ∷ CS34 ∷ []) (wl0808 (lit c4)) ▸
       at 10 5 (CCZ034 ∷ []) (sym (wp0352 c4)) ▸
       at 8 2 (Toff213 ∷ Toff234 ∷ []) (sym (wl0942 (lit c4))) ▸
       at 7 2 (Toff213 ∷ Toff134 ∷ Toff234 ∷ []) (wl1025 (lit c4)) ▸
       at 8 3 (Toff134 ∷ []) (wl0979 (lit c4)) ▸
       at 4 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 3 1 (CS12 ∷ []) (refl) ▸ done

  b7 : Chain (X4 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Bx2-0413 ∷ Toff134 ∷ CCZ034 ∷ CS12⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (X4 ∷ Bx0-2431 ∷ K1 ∷ CS34 ∷ CCZ024 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS12 ∷ Toff134 ∷ CCZ034 ∷ CS12⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b7 = at 3 2 (Bx2-0413 ∷ CS12 ∷ []) (lem-CSu-box-3-at0210243143 c4) ▸
       at 3 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 2 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 8 2 (CCZ024 ∷ K1⁻ ∷ []) (sym (wp0088 c4)) ▸
       at 7 2 (CCZ024 ∷ CS14 ∷ []) (sym (wp0034 c4)) ▸
       at 6 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ CS34⁻ ∷ []) (sym (wp0035 c4)) ▸
       at 4 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸ done

  b8 : Chain (X4 ∷ Bx0-2431 ∷ K1 ∷ CS34 ∷ CCZ024 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS12 ∷ Toff134 ∷ CCZ034 ∷ CS12⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (X4 ∷ Bx0-2431 ∷ CCZ024 ∷ Toff213 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ K1⁻ ∷ Toff234 ∷ CCZ034 ∷ Toff213 ∷ CS12 ∷ Toff134 ∷ CCZ034 ∷ CS12⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b8 = at 3 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 2 2 (CCZ024 ∷ K1 ∷ []) (sym (wp0089 c4)) ▸
       at 3 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 3 2 (Toff213 ∷ Toff134 ∷ Toff234 ∷ []) (wl1025 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ Toff234 ∷ CCZ034 ∷ []) (sym (wp0768 c4)) ▸
       at 4 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 10 2 (CCZ024 ∷ K1⁻ ∷ []) (sym (wp0088 c4)) ▸
       at 9 2 (CCZ024 ∷ CS14 ∷ []) (sym (wp0034 c4)) ▸ done

  b9 : Chain (X4 ∷ Bx0-2431 ∷ CCZ024 ∷ Toff213 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ K1⁻ ∷ Toff234 ∷ CCZ034 ∷ Toff213 ∷ CS12 ∷ Toff134 ∷ CCZ034 ∷ CS12⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (X4 ∷ Bx0-2431 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff134 ∷ Toff234 ∷ CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ Toff213 ∷ CS03 ∷ CS12 ∷ Toff134 ∷ CCZ034 ∷ CS12⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b9 = at 8 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 7 2 (CCZ024 ∷ CS34⁻ ∷ []) (sym (wp0035 c4)) ▸
       at 6 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 4 2 (CCZ024 ∷ K1 ∷ []) (sym (wp0089 c4)) ▸
       at 5 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 7 1 (CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ []) (wp0352 c4) ▸
       at 11 2 (Toff213 ∷ CS03 ∷ []) (wl0196 (lit c4)) ▸ done

  b10 : Chain (X4 ∷ Bx0-2431 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff134 ∷ Toff234 ∷ CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ Toff213 ∷ CS03 ∷ CS12 ∷ Toff134 ∷ CCZ034 ∷ CS12⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (X4 ∷ Bx0-2431 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff134 ∷ CCZ034 ∷ CS12 ∷ Toff134 ∷ CCZ034 ∷ CS12⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b10 = at 10 2 (Toff213 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF213 (lit c4)) ▸
       at 9 2 (Toff213 ∷ CS34⁻ ∷ []) (wl0807 (lit c4)) ▸
       at 8 2 (Toff213 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF213 (lit c4)) ▸
       at 7 2 (Toff213 ∷ CS34 ∷ []) (wl0808 (lit c4)) ▸
       at 8 5 (CCZ034 ∷ []) (sym (wp0352 c4)) ▸
       at 6 2 (Toff213 ∷ Toff234 ∷ []) (sym (wl0942 (lit c4))) ▸
       at 5 2 (Toff213 ∷ Toff134 ∷ Toff234 ∷ []) (wl1025 (lit c4)) ▸
       at 6 3 (Toff134 ∷ []) (wl0979 (lit c4)) ▸ done

  b11 : Chain (X4 ∷ Bx0-2431 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff134 ∷ CCZ034 ∷ CS12 ∷ Toff134 ∷ CCZ034 ∷ CS12⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (CCZ024 ∷ X4 ∷ CZ02 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Bx0-2431 ∷ Toff134 ∷ CCZ034 ∷ CS12 ∷ Toff134 ∷ CCZ034 ∷ CS12⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b11 = at 2 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-box-perm-4132-at122441 c4) ▸
       at 2 1 (Bx2-0134 ∷ []) (lem-box-perm-1342-at0210243143 c4) ▸
       at 1 2 (Bx2-0134 ∷ Bx0-1234 ∷ []) (lem-box-box-2 c4) ▸
       at 1 1 (Bx2-0413 ∷ []) (lem-box-perm-1423-at021021 c4) ▸
       at 2 1 (Bx0-2431 ∷ []) (lem-box-perm-2431 c4) ▸
       at 1 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 0 2 (CCZ024 ∷ X4 ∷ CZ02 ∷ []) (sym (wp0020 c4)) ▸ done

  b12 : Chain (CCZ024 ∷ X4 ∷ CZ02 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Bx0-2431 ∷ Toff134 ∷ CCZ034 ∷ CS12 ∷ Toff134 ∷ CCZ034 ∷ CS12⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (CCZ024 ∷ Toff213 ∷ X4 ∷ CZ02 ∷ CCZ024 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Toff213 ∷ Bx0-2431 ∷ Toff134 ∷ CCZ034 ∷ CS12 ∷ Toff134 ∷ CCZ034 ∷ CS12⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b12 = at 2 2 (Toff213 ∷ CZ02 ∷ CCZ013 ∷ []) (wl0183 (lit c4)) ▸
       at 1 2 (Toff213 ∷ X4 ∷ []) (sym (c₄ ((K ↑ • CCZ • K ↑ • iI) ↑) (X))) ▸
       at 4 1 (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ []) (wl0184 (lit c4)) ▸
       at 8 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸
       at 7 2 (CCZ024 ∷ CX01 ∷ []) (sym (wp0022 c4)) ▸
       at 6 2 (CCZ024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-CCZ024 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ CX01 ∷ []) (sym (wp0022 c4)) ▸
       at 4 2 (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 (lit c4)) ▸ done

  b13 : Chain (CCZ024 ∷ Toff213 ∷ X4 ∷ CZ02 ∷ CCZ024 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Toff213 ∷ Bx0-2431 ∷ Toff134 ∷ CCZ034 ∷ CS12 ∷ Toff134 ∷ CCZ034 ∷ CS12⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ X4 ∷ CCZ013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CCZ034 ∷ CS12 ∷ Toff134 ∷ CCZ034 ∷ CS12⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b13 = at 5 5 (CCZ013 ∷ []) (sym (wl0184 (lit c4))) ▸
       at 3 2 (CCZ024 ∷ CZ02 ∷ []) (sym (wp0023 c4)) ▸
       at 2 2 (CCZ024 ∷ X4 ∷ CZ02 ∷ []) (sym (wp0020 c4)) ▸
       at 3 3 (X4 ∷ []) (wl0185 (lit c4)) ▸
       at 4 2 (Toff213 ∷ CCZ013 ∷ []) (wl0186 (lit c4)) ▸
       at 3 2 (Toff213 ∷ X4 ∷ []) (sym (c₄ ((K ↑ • CCZ • K ↑ • iI) ↑) (X))) ▸
       at 0 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 3 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸ done

  b14 : Chain (Bx2-0413 ∷ X4 ∷ CCZ013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CCZ034 ∷ CS12 ∷ Toff134 ∷ CCZ034 ∷ CS12⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ X4 ∷ CCZ024 ∷ Toff013 ∷ CZ13 ∷ CCZ013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CCZ034 ∷ CS12 ∷ Toff134 ∷ CCZ034 ∷ CS12⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b14 = at 2 1 (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ []) (wl0184 (lit c4)) ▸
       at 6 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸
       at 5 2 (CCZ024 ∷ CX01 ∷ []) (sym (wp0022 c4)) ▸
       at 4 2 (CCZ024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-CCZ024 (lit c4)) ▸
       at 3 2 (CCZ024 ∷ CX01 ∷ []) (sym (wp0022 c4)) ▸
       at 2 2 (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 (lit c4)) ▸
       at 3 5 (CCZ013 ∷ []) (sym (wl0184 (lit c4))) ▸
       at 3 2 (Toff013 ∷ CZ13 ∷ CCZ013 ∷ []) (wl0906 (lit c4)) ▸ done

  b15 : Chain (Bx2-0413 ∷ X4 ∷ CCZ024 ∷ Toff013 ∷ CZ13 ∷ CCZ013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CCZ034 ∷ CS12 ∷ Toff134 ∷ CCZ034 ∷ CS12⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ X4 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ CZ13 ∷ CCZ013 ∷ Toff013 ∷ Toff134 ∷ CCZ034 ∷ CS12 ∷ Toff134 ∷ CCZ034 ∷ CS12⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b15 = at 5 1 (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ []) (wl0184 (lit c4)) ▸
       at 9 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸
       at 8 2 (CCZ024 ∷ CX01 ∷ []) (sym (wp0022 c4)) ▸
       at 7 2 (CCZ024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-CCZ024 (lit c4)) ▸
       at 6 2 (CCZ024 ∷ CX01 ∷ []) (sym (wp0022 c4)) ▸
       at 5 2 (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 (lit c4)) ▸
       at 6 5 (CCZ013 ∷ []) (sym (wl0184 (lit c4))) ▸
       at 4 2 (CCZ024 ∷ CZ13 ∷ []) (lem-comm-CZ13-CCZ024 (lit c4)) ▸ done

  b16 : Chain (Bx2-0413 ∷ X4 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ CZ13 ∷ CCZ013 ∷ Toff013 ∷ Toff134 ∷ CCZ034 ∷ CS12 ∷ Toff134 ∷ CCZ034 ∷ CS12⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ CCZ034 ∷ CS12 ∷ Toff134 ∷ CCZ034 ∷ CS12⁻ ∷ X4 ∷ CCZ013 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b16 = at 5 3 (Toff013 ∷ CCZ013 ∷ []) (wl1026 (lit c4)) ▸
       at 2 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 3 3 (Toff134 ∷ CCZ034 ∷ CCZ013 ∷ CCZ034 ∷ []) (wp0828 c4) ▸
       at 6 2 (CS12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CS12 (lit c4)) ▸
       at 5 2 (CS12 ∷ CCZ013 ∷ []) (wl0645 (lit c4)) ▸
       at 6 4 (Toff134 ∷ CCZ034 ∷ CCZ013 ∷ []) (wp0829 c4) ▸
       at 8 2 (CS12⁻ ∷ CCZ013 ∷ []) (wl0703 (lit c4)) ▸
       at 9 2 (X4 ∷ CCZ013 ∷ []) (wp0830 c4) ▸ done

  b17 : Chain (Bx2-0413 ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ CCZ034 ∷ CS12 ∷ Toff134 ∷ CCZ034 ∷ CS12⁻ ∷ X4 ∷ CCZ013 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ X4 ∷ Sb0-2-43-1 ∷ CX13 ∷ Toff314 ∷ X4 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b17 = at 10 2 [] (wl0230 (lit c4)) ▸
       at 4 2 (CS12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CS12 (lit c4)) ▸
       at 5 2 (Toff134 ∷ CCZ034 ∷ []) (wp0831 c4) ▸
       at 6 2 [] (wp0007 c4) ▸
       at 4 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 6 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 2 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 3 2 (CX13 ∷ Toff314 ∷ X4 ∷ []) (sym (wl0745 (lit c4))) ▸ done

  b18 : Chain (Bx2-0413 ∷ X4 ∷ Sb0-2-43-1 ∷ CX13 ∷ Toff314 ∷ X4 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ X4 ∷ CCZ024 ∷ Toff013 ∷ CX10 ∷ CCZ124 ∷ CCZ024 ∷ CX13 ∷ Toff014 ∷ Toff314 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b18 = at 2 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 4 1 (CS12 ∷ []) (refl) ▸
       at 6 1 (CS12⁻ ∷ []) (refl) ▸
       at 3 6 (CX13 ∷ Toff314 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (sym (wl1027 (lit c4))) ▸
       at 2 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 5 2 (CX10 ∷ CX13 ∷ Toff013 ∷ []) (sym (wl1028 (lit c4))) ▸
       at 7 2 (Toff014 ∷ Toff314 ∷ Toff013 ∷ []) (wp0832 c4) ▸
       at 4 2 (CX10 ∷ CCZ124 ∷ CCZ024 ∷ []) (wp0673 c4) ▸ done

  b19 : Chain (Bx2-0413 ∷ X4 ∷ CCZ024 ∷ Toff013 ∷ CX10 ∷ CCZ124 ∷ CCZ024 ∷ CX13 ∷ Toff014 ∷ Toff314 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ X4 ∷ CCZ024 ∷ Toff013 ∷ CX10 ∷ CCZ124 ∷ CX13 ∷ Toff014 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ K3⁻ ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b19 = at 6 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 7 2 (Toff014 ∷ CCZ124 ∷ CCZ024 ∷ []) (wp0833 c4) ▸
       at 10 1 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (sym (wl0190 (lit c4))) ▸
       at 9 2 (K3 ∷ CCZ024 ∷ []) (wp0037 c4) ▸
       at 10 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 11 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 12 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 13 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸ done

  b20 : Chain (Bx2-0413 ∷ X4 ∷ CCZ024 ∷ Toff013 ∷ CX10 ∷ CCZ124 ∷ CX13 ∷ Toff014 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ K3⁻ ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ X4 ∷ CCZ024 ∷ CX10 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ Toff013 ∷ CX12 ∷ CS14 ∷ CX13 ∷ Toff014 ∷ CCZ124 ∷ Toff314 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b20 = at 14 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 15 2 (K3⁻ ∷ CCZ024 ∷ []) (wp0033 c4) ▸
       at 9 7 (Toff314 ∷ []) (wl0190 (lit c4)) ▸
       at 3 2 (CX10 ∷ Toff013 ∷ []) (sym (wl1029 (lit c4))) ▸
       at 5 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 4 2 (CS24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CS24 (lit c4)) ▸
       at 5 2 (CX12 ∷ Toff013 ∷ []) (sym (wl0872 (lit c4))) ▸
       at 6 2 (CS24⁻ ∷ Toff013 ∷ []) (lem-comm-TOFF013-CSd24 (lit c4)) ▸ done

  b21 : Chain (Bx2-0413 ∷ X4 ∷ CCZ024 ∷ CX10 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ Toff013 ∷ CX12 ∷ CS14 ∷ CX13 ∷ Toff014 ∷ CCZ124 ∷ Toff314 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ X4 ∷ CCZ024 ∷ CX10 ∷ CCZ124 ∷ CX10 ∷ CX13 ∷ Toff014 ∷ CS24 ∷ CX12 ∷ Toff013 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ Toff314 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b21 = at 7 2 (CX12 ∷ Toff013 ∷ []) (sym (wl0872 (lit c4))) ▸
       at 8 2 (CS14 ∷ Toff013 ∷ []) (sym (wp0785 c4)) ▸
       at 4 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 5 2 (CX10 ∷ CX13 ∷ Toff013 ∷ []) (sym (wl1028 (lit c4))) ▸
       at 7 2 (Toff014 ∷ Toff013 ∷ []) (wp0786 c4) ▸
       at 9 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 8 2 (CS24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CS24 (lit c4)) ▸
       at 9 2 (CX12 ∷ Toff013 ∷ []) (sym (wl0872 (lit c4))) ▸ done

  b22 : Chain (Bx2-0413 ∷ X4 ∷ CCZ024 ∷ CX10 ∷ CCZ124 ∷ CX10 ∷ CX13 ∷ Toff014 ∷ CS24 ∷ CX12 ∷ Toff013 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ Toff314 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ X4 ∷ CCZ024 ∷ CX13 ∷ Toff314 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b22 = at 10 2 (CS24⁻ ∷ Toff013 ∷ []) (lem-comm-TOFF013-CSd24 (lit c4)) ▸
       at 11 2 (CX12 ∷ Toff013 ∷ []) (sym (wl0872 (lit c4))) ▸
       at 12 2 (CS14 ∷ Toff013 ∷ []) (sym (wp0785 c4)) ▸
       at 8 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 9 2 (Toff014 ∷ Toff314 ∷ Toff013 ∷ []) (wp0832 c4) ▸
       at 3 3 (CCZ124 ∷ []) (sym (wp0663 c4)) ▸
       at 5 3 (CCZ124 ∷ []) (sym (wp0787 c4)) ▸
       at 3 4 (CX13 ∷ Toff314 ∷ []) (wl1030 (lit c4)) ▸ done

  b23 : Chain (Bx2-0413 ∷ X4 ∷ CCZ024 ∷ CX13 ∷ Toff314 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ X4 ∷ CX13 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ CCZ024 ∷ K3⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b23 = at 2 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 4 1 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (sym (wl0190 (lit c4))) ▸
       at 3 2 (K3 ∷ CCZ024 ∷ []) (wp0037 c4) ▸
       at 4 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 5 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 6 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 7 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 8 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸ done

  b24 : Chain (Bx2-0413 ∷ X4 ∷ CX13 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ CCZ024 ∷ K3⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ Toff314 ∷ X4 ∷ Sb0-2-43-1 ∷ CS03 ∷ X4 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b24 = at 9 2 (K3⁻ ∷ CCZ024 ∷ []) (wp0033 c4) ▸
       at 3 7 (Toff314 ∷ []) (wl0190 (lit c4)) ▸
       at 4 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 6 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 8 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 4 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 1 3 (Toff314 ∷ X4 ∷ []) (sym (wl0187 (lit c4))) ▸
       at 4 2 (CS03 ∷ X4 ∷ []) (sym (wp0657 c4)) ▸ done

  b25 : Chain (Bx2-0413 ∷ Toff314 ∷ X4 ∷ Sb0-2-43-1 ∷ CS03 ∷ X4 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ Toff314 ∷ X4 ∷ CS03 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b25 = at 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 5 1 (CS12 ∷ []) (refl) ▸
       at 7 1 (CS12⁻ ∷ []) (refl) ▸
       at 7 2 (CS03 ∷ CS12⁻ ∷ []) (sym (wl0986 (lit c4))) ▸
       at 6 2 (CS03 ∷ Toff134 ∷ []) (sym (wp0277 c4)) ▸
       at 5 2 (CS03 ∷ CS12 ∷ []) (sym (wl0983 (lit c4))) ▸
       at 4 2 (CS03 ∷ Toff134 ∷ []) (sym (wp0277 c4)) ▸
       at 3 2 (CS03 ∷ Bx0-2431 ∷ []) (sym (lem-CSu-box-3-at122441 c4)) ▸ done

  b26 : Chain (Bx2-0413 ∷ Toff314 ∷ X4 ∷ CS03 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CX13 ∷ Toff314 ∷ X4 ∷ CS03⁻ ∷ [])
  b26 = at 6 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 8 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 4 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 2 2 (CS03 ∷ X4 ∷ []) (sym (wp0657 c4)) ▸
       at 5 2 (CX13 ∷ Toff314 ∷ X4 ∷ []) (sym (wl0745 (lit c4))) ▸
       at 4 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 6 1 (CS12 ∷ []) (refl) ▸
       at 8 1 (CS12⁻ ∷ []) (refl) ▸ done

  b27 : Chain (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CX13 ∷ Toff314 ∷ X4 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ X4 ∷ CCZ024 ∷ Toff013 ∷ CX10 ∷ CCZ124 ∷ CX13 ∷ Toff014 ∷ CCZ124 ∷ CCZ024 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS03⁻ ∷ [])
  b27 = at 5 6 (CX13 ∷ Toff314 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (sym (wl1027 (lit c4))) ▸
       at 4 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 7 2 (CX10 ∷ CX13 ∷ Toff013 ∷ []) (sym (wl1028 (lit c4))) ▸
       at 9 2 (Toff014 ∷ Toff314 ∷ Toff013 ∷ []) (wp0832 c4) ▸
       at 6 2 (CX10 ∷ CCZ124 ∷ CCZ024 ∷ []) (wp0673 c4) ▸
       at 8 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 9 2 (Toff014 ∷ CCZ124 ∷ CCZ024 ∷ []) (wp0833 c4) ▸
       at 12 1 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (sym (wl0190 (lit c4))) ▸ done

  b28 : Chain (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ X4 ∷ CCZ024 ∷ Toff013 ∷ CX10 ∷ CCZ124 ∷ CX13 ∷ Toff014 ∷ CCZ124 ∷ CCZ024 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ X4 ∷ CCZ024 ∷ Toff013 ∷ CX10 ∷ CCZ124 ∷ CX13 ∷ Toff014 ∷ CCZ124 ∷ Toff314 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS03⁻ ∷ [])
  b28 = at 11 2 (K3 ∷ CCZ024 ∷ []) (wp0037 c4) ▸
       at 12 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 13 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 14 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 15 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 16 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 17 2 (K3⁻ ∷ CCZ024 ∷ []) (wp0033 c4) ▸
       at 11 7 (Toff314 ∷ []) (wl0190 (lit c4)) ▸ done

  b29 : Chain (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ X4 ∷ CCZ024 ∷ Toff013 ∷ CX10 ∷ CCZ124 ∷ CX13 ∷ Toff014 ∷ CCZ124 ∷ Toff314 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ X4 ∷ CCZ024 ∷ CX10 ∷ CCZ124 ∷ Toff013 ∷ CX13 ∷ Toff014 ∷ CCZ124 ∷ Toff314 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS03⁻ ∷ [])
  b29 = at 5 2 (CX10 ∷ Toff013 ∷ []) (sym (wl1029 (lit c4))) ▸
       at 7 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 6 2 (CS24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CS24 (lit c4)) ▸
       at 7 2 (CX12 ∷ Toff013 ∷ []) (sym (wl0872 (lit c4))) ▸
       at 8 2 (CS24⁻ ∷ Toff013 ∷ []) (lem-comm-TOFF013-CSd24 (lit c4)) ▸
       at 9 2 (CX12 ∷ Toff013 ∷ []) (sym (wl0872 (lit c4))) ▸
       at 10 2 (CS14 ∷ Toff013 ∷ []) (sym (wp0785 c4)) ▸
       at 6 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸ done

  b30 : Chain (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ X4 ∷ CCZ024 ∷ CX10 ∷ CCZ124 ∷ Toff013 ∷ CX13 ∷ Toff014 ∷ CCZ124 ∷ Toff314 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ X4 ∷ CCZ024 ∷ CX10 ∷ CCZ124 ∷ CX10 ∷ CX13 ∷ Toff014 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ Toff013 ∷ Toff314 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS03⁻ ∷ [])
  b30 = at 7 2 (CX10 ∷ CX13 ∷ Toff013 ∷ []) (sym (wl1028 (lit c4))) ▸
       at 9 2 (Toff014 ∷ Toff013 ∷ []) (wp0786 c4) ▸
       at 11 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 10 2 (CS24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CS24 (lit c4)) ▸
       at 11 2 (CX12 ∷ Toff013 ∷ []) (sym (wl0872 (lit c4))) ▸
       at 12 2 (CS24⁻ ∷ Toff013 ∷ []) (lem-comm-TOFF013-CSd24 (lit c4)) ▸
       at 13 2 (CX12 ∷ Toff013 ∷ []) (sym (wl0872 (lit c4))) ▸
       at 14 2 (CS14 ∷ Toff013 ∷ []) (sym (wp0785 c4)) ▸ done

  b31 : Chain (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ X4 ∷ CCZ024 ∷ CX10 ∷ CCZ124 ∷ CX10 ∷ CX13 ∷ Toff014 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ Toff013 ∷ Toff314 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ X4 ∷ CX13 ∷ K3 ∷ CCZ024 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS03⁻ ∷ [])
  b31 = at 10 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 11 2 (Toff014 ∷ Toff314 ∷ Toff013 ∷ []) (wp0832 c4) ▸
       at 5 3 (CCZ124 ∷ []) (sym (wp0663 c4)) ▸
       at 7 3 (CCZ124 ∷ []) (sym (wp0787 c4)) ▸
       at 5 4 (CX13 ∷ Toff314 ∷ []) (wl1030 (lit c4)) ▸
       at 4 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 6 1 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (sym (wl0190 (lit c4))) ▸
       at 5 2 (K3 ∷ CCZ024 ∷ []) (wp0037 c4) ▸ done

  b32 : Chain (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ X4 ∷ CX13 ∷ K3 ∷ CCZ024 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ X4 ∷ CX13 ∷ Toff314 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS03⁻ ∷ [])
  b32 = at 6 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 7 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 8 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 9 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 10 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 11 2 (K3⁻ ∷ CCZ024 ∷ []) (wp0033 c4) ▸
       at 5 7 (Toff314 ∷ []) (wl0190 (lit c4)) ▸
       at 6 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸ done

  b33 : Chain (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ X4 ∷ CX13 ∷ Toff314 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CS03⁻ ∷ X4 ∷ [])
  b33 = at 8 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 10 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 6 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 3 3 (Toff314 ∷ X4 ∷ []) (sym (wl0187 (lit c4))) ▸
       at 6 2 (CS03⁻ ∷ X4 ∷ []) (sym (wp0659 c4)) ▸
       at 5 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 7 1 (CS12 ∷ []) (refl) ▸
       at 9 1 (CS12⁻ ∷ []) (refl) ▸ done

  b34 : Chain (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CS03⁻ ∷ X4 ∷ []) (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ X4 ∷ CS03⁻ ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  b34 = at 9 2 (CS03⁻ ∷ CS12⁻ ∷ []) (sym (wl0469 (lit c4))) ▸
       at 8 2 (CS03⁻ ∷ Toff134 ∷ []) (sym (wp0834 c4)) ▸
       at 7 2 (CS03⁻ ∷ CS12 ∷ []) (sym (wl0981 (lit c4))) ▸
       at 6 2 (CS03⁻ ∷ Toff134 ∷ []) (sym (wp0834 c4)) ▸
       at 5 2 (CS03⁻ ∷ Bx0-2431 ∷ []) (sym (lem-CSdu-box-3-at122441 c4)) ▸
       at 8 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 10 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 6 5 (Sb0-2-43-1 ∷ []) (refl) ▸ done

  b35 : Chain (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ X4 ∷ CS03⁻ ∷ Sb0-2-43-1 ∷ X4 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  b35 = at 4 2 (CS03⁻ ∷ X4 ∷ []) (sym (wp0659 c4)) ▸
       at 2 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 4 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 0 5 (Sb2-0-41-3 ∷ []) (refl) ▸ done

-- F2-CS0-CS2: 16 steps
lem-F2-CS0-CS2 : Ws → ⟪ (Sb2-0-41-3 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-F2-CS0-CS2 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb2-0-41-3 ∷ Sb0-2-43-1 ∷ []) (X4 ∷ Sb⁻2-0-41-3 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb⁻2-0-41-3 ∷ X4 ∷ CS01 ∷ [])
  b0 = at 0 0 (X4 ∷ X4 ∷ []) (sym (wl1083 (lit c4))) ▸
       at 1 0 (Sb⁻2-0-41-3 ∷ Sb2-0-41-3 ∷ []) (sym (lem-invr-SBOX⟨2·0·41·3⟩ c4)) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (sym (wl1083 (lit c4))) ▸
       at 3 4 (CS01 ∷ []) (lem-F5-01 c4) ▸
       at 3 2 (Sb0-2-43-1 ∷ CS01 ∷ []) (lem-AX-S23 c4) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (sym (wl1083 (lit c4))) ▸
       at 5 0 (Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ []) (sym (lem-inv-SBOX⟨2·0·41·3⟩ c4)) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (sym (wl1083 (lit c4))) ▸ done

  b1 : Chain (X4 ∷ Sb⁻2-0-41-3 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb⁻2-0-41-3 ∷ X4 ∷ CS01 ∷ []) (Sb0-2-43-1 ∷ Sb2-0-41-3 ∷ [])
  b1 = at 3 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS0-CS2 c4)) ▸
       at 2 2 [] (wl1083 (lit c4)) ▸
       at 1 2 [] (lem-invr-SBOX⟨2·0·41·3⟩ c4) ▸
       at 0 2 [] (wl1083 (lit c4)) ▸
       at 4 1 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F5-01 c4)) ▸
       at 3 2 [] (wl1083 (lit c4)) ▸
       at 2 2 [] (lem-invr-SBOX⟨2·0·41·3⟩ c4) ▸
       at 1 2 [] (wl1083 (lit c4)) ▸ done

-- Tu-box: 83 steps
lem-Tu-box : Ws → ⟪ (Toff301 ∷ Bx0-1234 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ Bx3-1204 ∷ []) ⟫ʷ
lem-Tu-box c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (run b10))))))))))
  where
  b0 : Chain (Toff301 ∷ Bx0-1234 ∷ Toff301 ∷ []) (Toff012 ∷ Toff312 ∷ CCZ034 ∷ Toff012 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ Toff312 ∷ CCZ124 ∷ CCZ034 ∷ CCZ014 ∷ [])
  b0 = at 1 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-box-tQ c4) ▸
       at 0 2 (Toff012 ∷ Toff312 ∷ Toff301 ∷ []) (sym (wl1084 (lit c4))) ▸
       at 2 2 (CCZ034 ∷ CCZ014 ∷ Toff301 ∷ []) (sym (wp0883 c4)) ▸
       at 4 2 (Toff012 ∷ Toff312 ∷ Toff301 ∷ []) (sym (wl1084 (lit c4))) ▸
       at 6 3 (CCZ034 ∷ CCZ014 ∷ []) (sym (wp0884 c4)) ▸
       at 3 2 (Toff012 ∷ CCZ014 ∷ CCZ124 ∷ []) (wp0122 c4) ▸
       at 5 2 (Toff312 ∷ CCZ124 ∷ []) (wl0871 (lit c4)) ▸
       at 4 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4) ▸ done

  b1 : Chain (Toff012 ∷ Toff312 ∷ CCZ034 ∷ Toff012 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ Toff312 ∷ CCZ124 ∷ CCZ034 ∷ CCZ014 ∷ []) (Toff012 ∷ Toff312 ∷ CCZ034 ∷ Toff012 ∷ Toff312 ∷ CCZ124 ∷ CCZ034 ∷ [])
  b1 = at 8 2 (Toff312 ∷ CS01 ∷ []) (wl0501 (lit c4)) ▸
       at 7 2 (Toff312 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF312 (lit c4)) ▸
       at 6 2 (Toff312 ∷ CS14⁻ ∷ []) (wl0778 (lit c4)) ▸
       at 5 2 (Toff312 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF312 (lit c4)) ▸
       at 4 2 (Toff312 ∷ CS14 ∷ []) (wl0499 (lit c4)) ▸
       at 5 5 (CCZ014 ∷ []) (sym (wp0041 c4)) ▸
       at 5 2 (CCZ124 ∷ CCZ014 ∷ []) (wp0066 c4) ▸
       at 6 3 (CCZ034 ∷ []) (wp0885 c4) ▸ done

  b2 : Chain (Toff012 ∷ Toff312 ∷ CCZ034 ∷ Toff012 ∷ Toff312 ∷ CCZ124 ∷ CCZ034 ∷ []) (Toff012 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ Toff012 ∷ CCZ034 ∷ CCZ124 ∷ [])
  b2 = at 5 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 9 2 (CCZ034 ∷ CS14 ∷ []) (sym (wp0106 c4)) ▸
       at 8 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸
       at 7 2 (CCZ034 ∷ CS24⁻ ∷ []) (sym (wp0107 c4)) ▸
       at 6 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸
       at 5 2 (CCZ034 ∷ CS24 ∷ []) (sym (wp0108 c4)) ▸
       at 6 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 3 2 (Toff312 ∷ Toff012 ∷ []) (wl1085 (lit c4)) ▸ done

  b3 : Chain (Toff012 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ Toff012 ∷ CCZ034 ∷ CCZ124 ∷ []) (CCZ013 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Toff324 ∷ K0⁻ ∷ CCZ123 ∷ CCZ124 ∷ CCZ013 ∷ Toff324 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ CCZ124 ∷ [])
  b3 = at 4 0 (CCZ034 ∷ CCZ034 ∷ []) (sym (wp0007 c4)) ▸
       at 1 4 (Bx3-1204 ∷ []) (sym (lem-box-tQ-at0330 c4)) ▸
       at 1 1 (Bx3-1024 ∷ []) (lem-box-perm-1324-at0330 c4) ▸
       at 1 1 (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ []) (lem-box-cP-at032032 c4) ▸
       at 0 2 (CCZ013 ∷ Toff012 ∷ CCZ123 ∷ []) (sym (wl0325 (lit c4))) ▸
       at 2 2 (Toff324 ∷ CCZ123 ∷ CCZ124 ∷ []) (wl0445 (lit c4)) ▸
       at 1 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0⁻ ∷ []) (sym (wl0446 (lit c4))) ▸
       at 7 2 (Toff324 ∷ K0⁻ ∷ []) (c₁ (K • iI) ((K ↑ • CCZ • K ↑ • iI) ↑)) ▸ done

  b4 : Chain (CCZ013 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Toff324 ∷ K0⁻ ∷ CCZ123 ∷ CCZ124 ∷ CCZ013 ∷ Toff324 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ CCZ124 ∷ []) (CCZ013 ∷ Toff324 ∷ Toff012 ∷ CCZ123 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ CCZ013 ∷ Toff324 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ CCZ124 ∷ [])
  b4 = at 6 2 (Toff324 ∷ CS02 ∷ []) (wp0298 c4) ▸
       at 5 2 (Toff324 ∷ CX01 ∷ []) (c₂ (CX₀₁) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 4 2 (Toff324 ∷ CS12⁻ ∷ []) (wl0447 (lit c4)) ▸
       at 3 2 (Toff324 ∷ CX01 ∷ []) (c₂ (CX₀₁) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 2 2 (Toff324 ∷ CS12 ∷ []) (wl0214 (lit c4)) ▸
       at 1 2 (Toff324 ∷ K0 ∷ []) (c₁ (K) ((K ↑ • CCZ • K ↑ • iI) ↑)) ▸
       at 2 7 (Toff012 ∷ []) (wl0446 (lit c4)) ▸
       at 4 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸ done

  b5 : Chain (CCZ013 ∷ Toff324 ∷ Toff012 ∷ CCZ123 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ CCZ013 ∷ Toff324 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ CCZ124 ∷ []) (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff012 ∷ CCZ123 ∷ CCZ123 ∷ CCZ124 ∷ Toff324 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ CCZ124 ∷ [])
  b5 = at 8 2 (CCZ013 ∷ CS14 ∷ []) (sym (wp0299 c4)) ▸
       at 7 2 (CCZ013 ∷ CX12 ∷ []) (sym (wl0448 (lit c4))) ▸
       at 6 2 (CCZ013 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-CCZ013 (lit c4)) ▸
       at 5 2 (CCZ013 ∷ CX12 ∷ []) (sym (wl0448 (lit c4))) ▸
       at 4 2 (CCZ013 ∷ CS24 ∷ []) (lem-comm-CS24-CCZ013 (lit c4)) ▸
       at 5 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 3 2 (CCZ013 ∷ CCZ123 ∷ []) (sym (wl0327 (lit c4))) ▸
       at 2 2 (CCZ013 ∷ Toff012 ∷ CCZ123 ∷ []) (sym (wl0325 (lit c4))) ▸ done

  b6 : Chain (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff012 ∷ CCZ123 ∷ CCZ123 ∷ CCZ124 ∷ Toff324 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ CCZ124 ∷ []) (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ K0 ∷ CS12 ∷ Toff324 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0⁻ ∷ CCZ124 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ CCZ124 ∷ [])
  b6 = at 3 3 (Toff012 ∷ []) (wl0449 (lit c4)) ▸
       at 4 2 (Toff324 ∷ CCZ124 ∷ []) (wl0450 (lit c4)) ▸
       at 3 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0⁻ ∷ []) (sym (wl0446 (lit c4))) ▸
       at 9 2 (Toff324 ∷ K0⁻ ∷ []) (c₁ (K • iI) ((K ↑ • CCZ • K ↑ • iI) ↑)) ▸
       at 8 2 (Toff324 ∷ CS02 ∷ []) (wp0298 c4) ▸
       at 7 2 (Toff324 ∷ CX01 ∷ []) (c₂ (CX₀₁) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 6 2 (Toff324 ∷ CS12⁻ ∷ []) (wl0447 (lit c4)) ▸
       at 5 2 (Toff324 ∷ CX01 ∷ []) (c₂ (CX₀₁) (K ↑ • CCZ • K ↑ • iI)) ▸ done

  b7 : Chain (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ K0 ∷ CS12 ∷ Toff324 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0⁻ ∷ CCZ124 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ CCZ124 ∷ []) (Bx3-1204 ∷ Toff012 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CCZ034 ∷ CX12 ∷ CS14 ∷ Toff012 ∷ CCZ034 ∷ CCZ124 ∷ [])
  b7 = at 4 2 (Toff324 ∷ CS12 ∷ []) (wl0214 (lit c4)) ▸
       at 3 2 (Toff324 ∷ K0 ∷ []) (c₁ (K) ((K ↑ • CCZ • K ↑ • iI) ↑)) ▸
       at 4 7 (Toff012 ∷ []) (wl0446 (lit c4)) ▸
       at 0 4 (Bx3-1024 ∷ []) (sym (lem-box-cP-at032032 c4)) ▸
       at 0 1 (Bx3-1204 ∷ []) (sym (lem-box-perm-1324-at0330 c4)) ▸
       at 2 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 6 2 (CCZ034 ∷ CS14 ∷ []) (sym (wp0106 c4)) ▸
       at 5 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸ done

  b8 : Chain (Bx3-1204 ∷ Toff012 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CCZ034 ∷ CX12 ∷ CS14 ∷ Toff012 ∷ CCZ034 ∷ CCZ124 ∷ []) (Bx3-1204 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CCZ034 ∷ CX12 ∷ CS14 ∷ CCZ124 ∷ [])
  b8 = at 4 2 (CCZ034 ∷ CS24⁻ ∷ []) (sym (wp0107 c4)) ▸
       at 3 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸
       at 2 2 (CCZ034 ∷ CS24 ∷ []) (sym (wp0108 c4)) ▸
       at 3 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 3 2 (Toff012 ∷ CCZ124 ∷ []) (wp0300 c4) ▸
       at 4 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 8 2 (CCZ034 ∷ CS14 ∷ []) (sym (wp0106 c4)) ▸
       at 7 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸ done

  b9 : Chain (Bx3-1204 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CCZ034 ∷ CX12 ∷ CS14 ∷ CCZ124 ∷ []) (Bx3-0124 ∷ Bx0-3124 ∷ [])
  b9 = at 6 2 (CCZ034 ∷ CS24⁻ ∷ []) (sym (wp0107 c4)) ▸
       at 5 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸
       at 4 2 (CCZ034 ∷ CS24 ∷ []) (sym (wp0108 c4)) ▸
       at 5 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 5 2 [] (wl0263 (lit c4)) ▸
       at 1 4 (Bx0-1234 ∷ []) (sym (lem-box-tQ c4)) ▸
       at 0 1 (Bx3-0124 ∷ []) (lem-box-perm-3124-at0330 c4) ▸
       at 1 1 (Bx0-3124 ∷ []) (lem-box-perm-3124 c4) ▸ done

  b10 : Chain (Bx3-0124 ∷ Bx0-3124 ∷ []) (Bx0-1234 ∷ Bx3-1204 ∷ [])
  b10 = at 0 2 (Bx0-3124 ∷ Bx3-0124 ∷ []) (lem-box-box-1-at03102132 c4) ▸
       at 0 1 (Bx0-1234 ∷ []) (lem-box-perm-2314-at132132 c4) ▸
       at 1 1 (Bx3-1204 ∷ []) (lem-box-perm-2314-at03102132 c4) ▸ done

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

-- F1-X-CS0@1: 86 steps
lem-F1-X-CS0at1 : Ws → ⟪ (CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS24 ∷ []) ⟫ʷ
lem-F1-X-CS0at1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (run b10))))))))))
  where
  b0 : Chain (CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ []) (CX41 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ124 ∷ CCZ014 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b0 = at 5 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 7 1 (CS13 ∷ []) (refl) ▸
       at 9 1 (CS13⁻ ∷ []) (refl) ▸
       at 0 5 (CX41 ∷ []) (wl1142 (lit c4)) ▸
       at 1 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 4 2 (Toff024 ∷ Toff324 ∷ Toff023 ∷ []) (wp0805 c4) ▸
       at 3 2 (Toff024 ∷ CCZ124 ∷ CCZ014 ∷ []) (wp0806 c4) ▸
       at 6 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸ done

  b1 : Chain (CX41 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ124 ∷ CCZ014 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (CX41 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b1 = at 5 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸
       at 6 2 (CS34 ∷ CCZ014 ∷ []) (wp0064 c4) ▸
       at 7 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 8 2 (CS34⁻ ∷ CCZ014 ∷ []) (wp0063 c4) ▸
       at 9 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 10 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸
       at 11 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸
       at 5 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸ done

  b2 : Chain (CX41 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (CX41 ∷ CCZ014 ∷ Toff024 ∷ CCZ124 ∷ Toff023 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b2 = at 2 2 (Toff024 ∷ Toff023 ∷ []) (wp0072 c4) ▸
       at 4 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 3 2 (CS24 ∷ Toff023 ∷ []) (sym (wp0070 c4)) ▸
       at 4 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 5 2 (CS24⁻ ∷ Toff023 ∷ []) (sym (wp0069 c4)) ▸
       at 6 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 7 2 (CS12 ∷ Toff023 ∷ []) (sym (wl0221 (lit c4))) ▸
       at 3 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸ done

  b3 : Chain (CX41 ∷ CCZ014 ∷ Toff024 ∷ CCZ124 ∷ Toff023 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (CX41 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CCZ014 ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b3 = at 4 2 (Toff024 ∷ Toff324 ∷ Toff023 ∷ []) (wp0805 c4) ▸
       at 2 3 (CCZ124 ∷ []) (sym (wp0074 c4)) ▸
       at 1 2 (CCZ124 ∷ CCZ014 ∷ []) (wp0066 c4) ▸
       at 3 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 2 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸
       at 3 2 (CS34 ∷ CCZ014 ∷ []) (wp0064 c4) ▸
       at 4 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 5 2 (CS34⁻ ∷ CCZ014 ∷ []) (wp0063 c4) ▸ done

  b4 : Chain (CX41 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CCZ014 ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (CX41 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b4 = at 6 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 7 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸
       at 8 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸
       at 2 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 3 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 3 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 6 2 (CS13 ∷ Toff023 ∷ []) (sym (wl0222 (lit c4))) ▸
       at 5 2 (CS13 ∷ CCZ014 ∷ []) (wp0053 c4) ▸ done

  b5 : Chain (CX41 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13⁻ ∷ []) (CX41 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ124 ∷ K3 ∷ CCZ014 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CS13⁻ ∷ [])
  b5 = at 4 2 (CS13 ∷ Toff023 ∷ []) (sym (wl0222 (lit c4))) ▸
       at 3 2 (CS13 ∷ CCZ014 ∷ []) (wp0053 c4) ▸
       at 4 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 4 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 7 2 (Toff024 ∷ Toff324 ∷ Toff023 ∷ []) (wp0805 c4) ▸
       at 6 2 (Toff024 ∷ CCZ124 ∷ CCZ014 ∷ []) (wp0806 c4) ▸
       at 9 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 8 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸ done

  b6 : Chain (CX41 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ124 ∷ K3 ∷ CCZ014 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CS13⁻ ∷ []) (CX41 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff024 ∷ Toff023 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ [])
  b6 = at 9 2 (CS34 ∷ CCZ014 ∷ []) (wp0064 c4) ▸
       at 10 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 11 2 (CS34⁻ ∷ CCZ014 ∷ []) (wp0063 c4) ▸
       at 12 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 13 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸
       at 14 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸
       at 8 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 5 2 (Toff024 ∷ Toff023 ∷ []) (wp0072 c4) ▸ done

  b7 : Chain (CX41 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff024 ∷ Toff023 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ []) (CX41 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff024 ∷ CCZ124 ∷ Toff024 ∷ Toff324 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ [])
  b7 = at 7 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 6 2 (CS24 ∷ Toff023 ∷ []) (sym (wp0070 c4)) ▸
       at 7 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 8 2 (CS24⁻ ∷ Toff023 ∷ []) (sym (wp0069 c4)) ▸
       at 9 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 10 2 (CS12 ∷ Toff023 ∷ []) (sym (wl0221 (lit c4))) ▸
       at 6 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 7 2 (Toff024 ∷ Toff324 ∷ Toff023 ∷ []) (wp0805 c4) ▸ done

  b8 : Chain (CX41 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff024 ∷ CCZ124 ∷ Toff024 ∷ Toff324 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ []) (CX41 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CCZ014 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ [])
  b8 = at 5 3 (CCZ124 ∷ []) (sym (wp0074 c4)) ▸
       at 4 2 (CCZ124 ∷ CCZ014 ∷ []) (wp0066 c4) ▸
       at 6 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 5 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸
       at 6 2 (CS34 ∷ CCZ014 ∷ []) (wp0064 c4) ▸
       at 7 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 8 2 (CS34⁻ ∷ CCZ014 ∷ []) (wp0063 c4) ▸
       at 9 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸ done

  b9 : Chain (CX41 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CCZ014 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ []) (CX41 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ CS13⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ [])
  b9 = at 10 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸
       at 11 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸
       at 5 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 6 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 6 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 9 2 (CS13⁻ ∷ Toff023 ∷ []) (sym (wl0219 (lit c4))) ▸
       at 8 2 (CS13⁻ ∷ CCZ014 ∷ []) (wp0060 c4) ▸
       at 7 2 (CS13⁻ ∷ Toff023 ∷ []) (sym (wl0219 (lit c4))) ▸ done

  b10 : Chain (CX41 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ CS13⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS24 ∷ [])
  b10 = at 6 2 (CS13⁻ ∷ CCZ014 ∷ []) (wp0060 c4) ▸
       at 7 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 1 3 (Toff324 ∷ CS13 ∷ CCZ124 ∷ []) (wl1000 (lit c4)) ▸
       at 3 2 [] (wl0263 (lit c4)) ▸
       at 0 5 (Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ CCZ123 ∷ S4 ∷ CS24 ∷ []) (wl1143 (lit c4)) ▸
       at 0 14 (Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS24 ∷ []) (sym (lem-nf-X-CS0at1 c4)) ▸ done

-- F1-X-CS0@2: 86 steps
lem-F1-X-CS0at2 : Ws → ⟪ (CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS34 ∷ []) ⟫ʷ
lem-F1-X-CS0at2 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (run b10))))))))))
  where
  b0 : Chain (CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ []) (CX42 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ CCZ024 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b0 = at 5 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 7 1 (CS12 ∷ []) (refl) ▸
       at 9 1 (CS12⁻ ∷ []) (refl) ▸
       at 0 5 (CX42 ∷ []) (wl1147 (lit c4)) ▸
       at 1 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 4 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp0843 c4) ▸
       at 3 2 (Toff034 ∷ CCZ234 ∷ CCZ024 ∷ []) (wp0845 c4) ▸
       at 6 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸ done

  b1 : Chain (CX42 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ CCZ024 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (CX42 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b1 = at 5 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸
       at 6 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 7 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 8 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 9 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 10 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 11 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 5 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸ done

  b2 : Chain (CX42 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (CX42 ∷ CCZ024 ∷ Toff034 ∷ CCZ234 ∷ Toff013 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b2 = at 2 2 (Toff034 ∷ Toff013 ∷ []) (wp0097 c4) ▸
       at 4 1 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (wl0245 (lit c4)) ▸
       at 3 2 (CS34 ∷ Toff013 ∷ []) (sym (wp0095 c4)) ▸
       at 4 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 5 2 (CS34⁻ ∷ Toff013 ∷ []) (sym (wp0094 c4)) ▸
       at 6 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 7 2 (CS23 ∷ Toff013 ∷ []) (sym (wl0246 (lit c4))) ▸
       at 3 5 (CCZ234 ∷ []) (sym (wl0245 (lit c4))) ▸ done

  b3 : Chain (CX42 ∷ CCZ024 ∷ Toff034 ∷ CCZ234 ∷ Toff013 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (CX42 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CCZ024 ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b3 = at 4 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp0843 c4) ▸
       at 2 3 (CCZ234 ∷ []) (sym (wp0842 c4)) ▸
       at 1 2 (CCZ234 ∷ CCZ024 ∷ []) (wp0090 c4) ▸
       at 3 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 2 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸
       at 3 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 4 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 5 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸ done

  b4 : Chain (CX42 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CCZ024 ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (CX42 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b4 = at 6 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 7 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 8 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 2 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 3 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 3 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 6 2 (CS12 ∷ Toff013 ∷ []) (sym (wl0247 (lit c4))) ▸
       at 5 2 (CS12 ∷ CCZ024 ∷ []) (wp0081 c4) ▸ done

  b5 : Chain (CX42 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12⁻ ∷ []) (CX42 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ K1 ∷ CCZ024 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CS12⁻ ∷ [])
  b5 = at 4 2 (CS12 ∷ Toff013 ∷ []) (sym (wl0247 (lit c4))) ▸
       at 3 2 (CS12 ∷ CCZ024 ∷ []) (wp0081 c4) ▸
       at 4 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 4 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 7 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp0843 c4) ▸
       at 6 2 (Toff034 ∷ CCZ234 ∷ CCZ024 ∷ []) (wp0845 c4) ▸
       at 9 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 8 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸ done

  b6 : Chain (CX42 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ K1 ∷ CCZ024 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CS12⁻ ∷ []) (CX42 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff034 ∷ Toff013 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ [])
  b6 = at 9 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 10 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 11 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 12 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 13 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 14 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 8 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 5 2 (Toff034 ∷ Toff013 ∷ []) (wp0097 c4) ▸ done

  b7 : Chain (CX42 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff034 ∷ Toff013 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ []) (CX42 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff034 ∷ CCZ234 ∷ Toff034 ∷ Toff134 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ [])
  b7 = at 7 1 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (wl0245 (lit c4)) ▸
       at 6 2 (CS34 ∷ Toff013 ∷ []) (sym (wp0095 c4)) ▸
       at 7 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 8 2 (CS34⁻ ∷ Toff013 ∷ []) (sym (wp0094 c4)) ▸
       at 9 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 10 2 (CS23 ∷ Toff013 ∷ []) (sym (wl0246 (lit c4))) ▸
       at 6 5 (CCZ234 ∷ []) (sym (wl0245 (lit c4))) ▸
       at 7 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp0843 c4) ▸ done

  b8 : Chain (CX42 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff034 ∷ CCZ234 ∷ Toff034 ∷ Toff134 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ []) (CX42 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ [])
  b8 = at 5 3 (CCZ234 ∷ []) (sym (wp0842 c4)) ▸
       at 4 2 (CCZ234 ∷ CCZ024 ∷ []) (wp0090 c4) ▸
       at 6 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 5 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸
       at 6 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 7 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 8 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 9 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸ done

  b9 : Chain (CX42 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ []) (CX42 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ CS12⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ [])
  b9 = at 10 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 11 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 5 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 6 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 6 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 9 2 (CS12⁻ ∷ Toff013 ∷ []) (sym (wl0244 (lit c4))) ▸
       at 8 2 (CS12⁻ ∷ CCZ024 ∷ []) (wp0087 c4) ▸
       at 7 2 (CS12⁻ ∷ Toff013 ∷ []) (sym (wl0244 (lit c4))) ▸ done

  b10 : Chain (CX42 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ CS12⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS34 ∷ [])
  b10 = at 6 2 (CS12⁻ ∷ CCZ024 ∷ []) (wp0087 c4) ▸
       at 7 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 1 3 (Toff134 ∷ CS12 ∷ CCZ234 ∷ []) (wl1037 (lit c4)) ▸
       at 3 2 [] (wl0305 (lit c4)) ▸
       at 0 5 (Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CS34 ∷ []) (wl1148 (lit c4)) ▸
       at 0 14 (Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS34 ∷ []) (sym (lem-nf-X-CS0at2 c4)) ▸ done

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
