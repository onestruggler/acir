{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D006 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Lits using (lw0 ; lw1 ; lw2 ; lw3 ; lw4)
open import Examples.Groups.Clifford+CS.Five.Resps using (pw0 ; pw1 ; pw2 ; pw3 ; pw4)
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-K0-pass-ci ; lem-beta-T-at243243 ; lem-c124-beta ; lem-sym23)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-beta-inv-at0210243143 ; lem-sym12-at0214203143 ; lem-sym23-at0214203143 ; lem-sym23-at0214213043)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-F0 ; lem-X1-beta ; lem-c124-beta-at2332 ; lem-sym12-at12213443 ; lem-sym23-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-sym12-at0210243143 ; lem-sym34-at233442)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-CS12-beta-at2332 ; lem-CX23-beta-at0210243143 ; lem-CX23-beta-at02243043 ; lem-SB2 ; lem-T312-beta-at02142140 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0210243143 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ324-at2332 ; lem-auto-BOX⟨0·1234⟩-∣-CS14-at0210243143 ; lem-auto-BOX⟨0·1234⟩-∣-CS21 ; lem-auto-BOX⟨0·1234⟩-∣-CS23 ; lem-auto-BOX⟨0·1234⟩-∣-CSd14-at0210243143 ; lem-sym12-at0214213043 ; lem-sym12-at02243043 ; lem-sym34-at0214213043 ; lem-sym34-at02142140)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-1-BOX⟨0·2134⟩ ; lem-nat-1-CCZ023 ; lem-nat-1-CCZ034 ; lem-nat-2-BOX⟨0·1234⟩ ; lem-nat-2-BOX⟨0·1324⟩ ; lem-nat-3-BOX⟨0·1243⟩ ; lem-nat-3-BOX⟨0·1423⟩)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-1-CCZ013 ; lem-nat-3-BOX⟨0·1324⟩)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-2-BOX⟨0·3124⟩ ; lem-nat-2-CCZ124 ; lem-nat-2-CCZ134)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-0-BOX⟨1·4023⟩ ; lem-nat-1-BOX⟨2·4013⟩ ; lem-nat-3-BOX⟨0·4123⟩)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-0-CCZ034 ; lem-nat-0-CCZ134)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-1-BOX⟨0·1234⟩ ; lem-nat-2-BOX⟨0·2134⟩ ; lem-nat-3-BOX⟨0·3124⟩)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-nat-0-BOX⟨0·4123⟩ ; lem-nat-1-BOX⟨1·4023⟩)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-0-BOX⟨0·1423⟩ ; lem-nat-1-BOX⟨1·0423⟩)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-nat-0-BOX⟨0·1234⟩ ; lem-nat-0-BOX⟨1·0423⟩ ; lem-nat-1-BOX⟨2·0413⟩ ; lem-nat-3-BOX⟨0·1234⟩ ; lem-nat-3-CCZ123 ; lem-nat-3-CCZ124)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-nat-2-BOX⟨0·1243⟩ ; lem-nat-2-BOX⟨0·1342⟩ ; lem-nat-2-BOX⟨0·3142⟩)
open import Examples.Groups.Clifford+CS.Five.D.R012 using (lem-nat-1-BOX⟨0·1342⟩ ; lem-nat-1-BOX⟨0·2341⟩ ; lem-nat-1-CS01 ; lem-nat-1-CS02)
open import Examples.Groups.Clifford+CS.Five.D.R013 using (lem-nat-0-BOX⟨0·1324⟩ ; lem-nat-1-BOX⟨1·0324⟩ ; lem-nat-2-CS12 ; lem-nat-2-CS13 ; lem-nat-2-TOFF014 ; lem-nat-3-CS13 ; lem-nat-3-CS14)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-nat-0-CS04 ; lem-nat-0-CS14 ; lem-nat-1-CS04 ; lem-nat-1-SBOX⟨1·0·42·3⟩ ; lem-nat-1-SBOX⟨3·0·41·2⟩ ; lem-nat-2-BOX⟨0·1432⟩ ; lem-nat-2-SBOX⟨1·0·43·2⟩ ; lem-nat-3-CS23 ; lem-nat-3-CS24)
open import Examples.Groups.Clifford+CS.Five.D.R015 using (lem-nat-0-BOX⟨0·1342⟩ ; lem-nat-0-SBOX⟨0·1·34·2⟩ ; lem-nat-0-SBOX⟨2·0·34·1⟩ ; lem-nat-1-SBOX⟨0·2·34·1⟩ ; lem-nat-1-SBOX⟨2·1·34·0⟩ ; lem-nat-2-SBOX⟨3·0·42·1⟩ ; lem-nat-3-SBOX⟨1·0·34·2⟩ ; lem-nat-3-SBOX⟨2·0·43·1⟩)
open import Examples.Groups.Clifford+CS.Five.D.R016 using (lem-nat-0-BOX⟨1·0324⟩ ; lem-nat-0-BOX⟨1·0342⟩ ; lem-nat-0-BOX⟨1·3042⟩ ; lem-nat-0-SBOX⟨1·2·34·0⟩ ; lem-nat-1-BOX⟨1·0342⟩ ; lem-nat-1-BOX⟨2·0341⟩ ; lem-nat-1-BOX⟨2·3041⟩)
-- auto BOX(0;1234) | CCZ324 @243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ324-at243243 : Complete 4 → ⟪ (Bx0-1423 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Bx0-1423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ324-at243243 c4 = run b0
  where
  b0 : Chain (Bx0-1423 ∷ CCZ234 ∷ []) (CCZ234 ∷ Bx0-1423 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ c4) ▸
       at 2 2 (CCZ234 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ234 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ324-at2332 c4) ▸
       at 0 2 (CCZ234 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ324 @0110243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ324-at0110243243 : Complete 4 → ⟪ (Bx1-0423 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Bx1-0423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ324-at0110243243 c4 = run b0
  where
  b0 : Chain (Bx1-0423 ∷ CCZ234 ∷ []) (CCZ234 ∷ Bx1-0423 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ c4) ▸
       at 2 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 1 2 (CCZ234 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ324-at243243 c4) ▸
       at 0 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 1 2 (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ324 @0210243143: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ324-at0210243143 : Complete 4 → ⟪ (Bx2-0413 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Bx2-0413 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ324-at0210243143 c4 = run b0
  where
  b0 : Chain (Bx2-0413 ∷ CCZ134 ∷ []) (CCZ134 ∷ Bx2-0413 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ c4) ▸
       at 2 2 (CCZ234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ134 ∷ []) (CCZ234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ234 ∷ Bx1-0423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ324-at0110243243 c4) ▸
       at 0 2 (CCZ134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ234 ∷ []) (CCZ134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0423⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CS23 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS23-at2332 : Complete 4 → ⟪ (Bx0-1324 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS23-at2332 c4 = run b0
  where
  b0 : Chain (Bx0-1324 ∷ CS23 ∷ []) (CS23 ∷ Bx0-1324 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ c4) ▸
       at 2 2 (CS23 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CS23 ∷ []) (CS23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS23 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS23 c4) ▸
       at 0 2 (CS23 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CS23 ∷ []) (CS23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CS23 @243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS23-at243243 : Complete 4 → ⟪ (Bx0-1423 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ Bx0-1423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS23-at243243 c4 = run b0
  where
  b0 : Chain (Bx0-1423 ∷ CS24 ∷ []) (CS24 ∷ Bx0-1423 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ c4) ▸
       at 2 2 (CS23 ∷ Sw34 ∷ []) (lem-nat-3-CS24 c4) ▸
       at 1 2 (CS23 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS23-at2332 c4) ▸
       at 0 2 (CS24 ∷ Sw34 ∷ []) (lem-nat-3-CS23 c4) ▸
       at 1 2 (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CS23 @0110243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS23-at0110243243 : Complete 4 → ⟪ (Bx1-0423 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ Bx1-0423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS23-at0110243243 c4 = run b0
  where
  b0 : Chain (Bx1-0423 ∷ CS24 ∷ []) (CS24 ∷ Bx1-0423 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ c4) ▸
       at 2 2 (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑)) ▸
       at 1 2 (CS24 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS23-at243243 c4) ▸
       at 0 2 (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑)) ▸
       at 1 2 (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CS23 @0210243143: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS23-at0210243143 : Complete 4 → ⟪ (Bx2-0413 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ Bx2-0413 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS23-at0210243143 c4 = run b0
  where
  b0 : Chain (Bx2-0413 ∷ CS14 ∷ []) (CS14 ∷ Bx2-0413 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ c4) ▸
       at 2 2 (CS24 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS14 ∷ []) (CS24 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS24 ∷ Bx1-0423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS23-at0110243243 c4) ▸
       at 0 2 (CS14 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS24 ∷ []) (CS14 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0423⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- F1 X-CS0 [nf of rhs]: 36 steps
lem-F1-X-CS0-nf-of-rhs : Complete 4 → ⟪ (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CCZ014 ∷ CCZ014 ∷ CS03 ∷ Toff314 ∷ CCZ014 ∷ CS03⁻ ∷ CX40 ∷ CCZ134 ∷ CS14 ∷ Bx2-0413 ∷ []) ⟫ʷ
lem-F1-X-CS0-nf-of-rhs c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (run b4))))
  where
  b0 : Chain (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CS14 ∷ []) (CCZ014 ∷ Toff314 ∷ Toff314 ∷ Bx2-4103 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CX40 ∷ CS14 ∷ [])
  b0 = at 0 2 (CCZ014 ∷ []) (lem-SB2 c4) ▸
       at 2 5 (CX40 ∷ []) (pw1 c4 (CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ []) (CX40 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 1 (CS03 ∷ []) (refl) ▸
       at 5 1 (CS03⁻ ∷ []) (refl) ▸
       at 1 0 (Toff314 ∷ Toff314 ∷ []) (lw0 c4 [] (Toff314 ∷ Toff314 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Bx2-4013 ∷ []) (lem-sym12-at0210243143 c4) ▸
       at 3 1 (Bx2-4103 ∷ []) (lem-sym23-at0214203143 c4) ▸ done

  b1 : Chain (CCZ014 ∷ Toff314 ∷ Toff314 ∷ Bx2-4103 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CX40 ∷ CS14 ∷ []) (CCZ014 ∷ Toff314 ∷ CCZ014 ∷ CS03 ∷ Toff314 ∷ Toff314 ∷ Bx2-0413 ∷ Toff314 ∷ CS03⁻ ∷ CX40 ∷ CS14 ∷ [])
  b1 = at 3 1 (Bx2-4130 ∷ []) (lem-sym34-at0214213043 c4) ▸
       at 2 3 (Bx2-4130 ∷ CCZ014 ∷ []) (lem-T312-beta-at02142140 c4) ▸
       at 2 1 (Bx2-4103 ∷ []) (lem-sym34-at02142140 c4) ▸
       at 2 1 (Bx2-4013 ∷ []) (lem-sym23-at0214213043 c4) ▸
       at 2 1 (Bx2-0413 ∷ []) (lem-sym12-at0214203143 c4) ▸
       at 2 2 (CCZ014 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0210243143 c4) ▸
       at 3 2 (CS03 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS14-at0210243143 c4) ▸
       at 4 0 (Toff314 ∷ Toff314 ∷ []) (lw0 c4 [] (Toff314 ∷ Toff314 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (CCZ014 ∷ Toff314 ∷ CCZ014 ∷ CS03 ∷ Toff314 ∷ Toff314 ∷ Bx2-0413 ∷ Toff314 ∷ CS03⁻ ∷ CX40 ∷ CS14 ∷ []) (CCZ014 ∷ Toff314 ∷ CCZ014 ∷ CS03 ∷ Toff314 ∷ CCZ014 ∷ Bx2-0413 ∷ CS03⁻ ∷ CX40 ∷ CS14 ∷ [])
  b2 = at 6 1 (Bx2-4013 ∷ []) (lem-sym12-at0210243143 c4) ▸
       at 6 1 (Bx2-4103 ∷ []) (lem-sym23-at0214203143 c4) ▸
       at 6 1 (Bx2-4130 ∷ []) (lem-sym34-at0214213043 c4) ▸
       at 5 3 (Bx2-4130 ∷ CCZ014 ∷ []) (lem-T312-beta-at02142140 c4) ▸
       at 5 1 (Bx2-4103 ∷ []) (lem-sym34-at02142140 c4) ▸
       at 5 1 (Bx2-4013 ∷ []) (lem-sym23-at0214213043 c4) ▸
       at 5 1 (Bx2-0413 ∷ []) (lem-sym12-at0214203143 c4) ▸
       at 5 2 (CCZ014 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0210243143 c4) ▸ done

  b3 : Chain (CCZ014 ∷ Toff314 ∷ CCZ014 ∷ CS03 ∷ Toff314 ∷ CCZ014 ∷ Bx2-0413 ∷ CS03⁻ ∷ CX40 ∷ CS14 ∷ []) (CCZ014 ∷ Toff314 ∷ CCZ014 ∷ CS03 ∷ Toff314 ∷ CCZ014 ∷ CS03⁻ ∷ CX40 ∷ Bx2-4013 ∷ CCZ134 ∷ CS14 ∷ [])
  b3 = at 6 2 (CS03⁻ ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd14-at0210243143 c4) ▸
       at 7 0 (CX40 ∷ CX40 ∷ []) (pw1 c4 [] (CX40 ∷ CX40 ∷ []) tt tt Eq.refl) ▸
       at 9 1 (Bx2-4013 ∷ []) (lem-sym12-at0210243143 c4) ▸
       at 9 1 (Bx2-4103 ∷ []) (lem-sym23-at0214203143 c4) ▸
       at 9 1 (Bx2-1403 ∷ []) (lem-sym12-at0214213043 c4) ▸
       at 8 3 (Bx2-1403 ∷ CCZ134 ∷ []) (lem-CX23-beta-at02243043 c4) ▸
       at 8 1 (Bx2-4103 ∷ []) (lem-sym12-at02243043 c4) ▸
       at 8 1 (Bx2-4013 ∷ []) (lem-sym23-at0214213043 c4) ▸ done

  b4 : Chain (CCZ014 ∷ Toff314 ∷ CCZ014 ∷ CS03 ∷ Toff314 ∷ CCZ014 ∷ CS03⁻ ∷ CX40 ∷ Bx2-4013 ∷ CCZ134 ∷ CS14 ∷ []) (Toff314 ∷ CCZ014 ∷ CCZ014 ∷ CS03 ∷ Toff314 ∷ CCZ014 ∷ CS03⁻ ∷ CX40 ∷ CCZ134 ∷ CS14 ∷ Bx2-0413 ∷ [])
  b4 = at 8 1 (Bx2-0413 ∷ []) (lem-sym12-at0214203143 c4) ▸
       at 8 2 (CCZ134 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ324-at0210243143 c4) ▸
       at 9 2 (CS14 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS23-at0210243143 c4) ▸
       at 0 2 (Toff314 ∷ CCZ014 ∷ []) (pw2 c4 (CCZ014 ∷ Toff314 ∷ []) (Toff314 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸ done


-- F1 X-CS0: 26 steps
lem-F1-X-CS0 : Complete 4 → ⟪ (CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CS14 ∷ []) ⟫ʷ
lem-F1-X-CS0 c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb2-0-41-3 ∷ []) (CX40 ∷ Toff314 ∷ Toff314 ∷ Bx2-4130 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b0 = at 0 5 (CX40 ∷ []) (pw1 c4 (CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ []) (CX40 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 1 (CS03 ∷ []) (refl) ▸
       at 5 1 (CS03⁻ ∷ []) (refl) ▸
       at 1 0 (Toff314 ∷ Toff314 ∷ []) (lw0 c4 [] (Toff314 ∷ Toff314 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Bx2-4013 ∷ []) (lem-sym12-at0210243143 c4) ▸
       at 3 1 (Bx2-4103 ∷ []) (lem-sym23-at0214203143 c4) ▸
       at 3 1 (Bx2-4130 ∷ []) (lem-sym34-at0214213043 c4) ▸ done

  b1 : Chain (CX40 ∷ Toff314 ∷ Toff314 ∷ Bx2-4130 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (CX40 ∷ Toff314 ∷ CCZ014 ∷ CS03 ∷ Toff314 ∷ Toff314 ∷ Bx2-4013 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b1 = at 2 3 (Bx2-4130 ∷ CCZ014 ∷ []) (lem-T312-beta-at02142140 c4) ▸
       at 2 1 (Bx2-4103 ∷ []) (lem-sym34-at02142140 c4) ▸
       at 2 1 (Bx2-4013 ∷ []) (lem-sym23-at0214213043 c4) ▸
       at 2 1 (Bx2-0413 ∷ []) (lem-sym12-at0214203143 c4) ▸
       at 2 2 (CCZ014 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0210243143 c4) ▸
       at 3 2 (CS03 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS14-at0210243143 c4) ▸
       at 4 0 (Toff314 ∷ Toff314 ∷ []) (lw0 c4 [] (Toff314 ∷ Toff314 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Bx2-4013 ∷ []) (lem-sym12-at0210243143 c4) ▸ done

  b2 : Chain (CX40 ∷ Toff314 ∷ CCZ014 ∷ CS03 ∷ Toff314 ∷ Toff314 ∷ Bx2-4013 ∷ Toff314 ∷ CS03⁻ ∷ []) (CX40 ∷ Toff314 ∷ CCZ014 ∷ CS03 ∷ Toff314 ∷ CCZ014 ∷ CS03⁻ ∷ Bx2-0413 ∷ [])
  b2 = at 6 1 (Bx2-4103 ∷ []) (lem-sym23-at0214203143 c4) ▸
       at 6 1 (Bx2-4130 ∷ []) (lem-sym34-at0214213043 c4) ▸
       at 5 3 (Bx2-4130 ∷ CCZ014 ∷ []) (lem-T312-beta-at02142140 c4) ▸
       at 5 1 (Bx2-4103 ∷ []) (lem-sym34-at02142140 c4) ▸
       at 5 1 (Bx2-4013 ∷ []) (lem-sym23-at0214213043 c4) ▸
       at 5 1 (Bx2-0413 ∷ []) (lem-sym12-at0214203143 c4) ▸
       at 5 2 (CCZ014 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0210243143 c4) ▸
       at 6 2 (CS03⁻ ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd14-at0210243143 c4) ▸ done

  b3 : Chain (CX40 ∷ Toff314 ∷ CCZ014 ∷ CS03 ∷ Toff314 ∷ CCZ014 ∷ CS03⁻ ∷ Bx2-0413 ∷ []) (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CS14 ∷ [])
  b3 = at 0 7 (Toff314 ∷ CCZ014 ∷ CCZ014 ∷ CS03 ∷ Toff314 ∷ CCZ014 ∷ CS03⁻ ∷ CX40 ∷ CCZ134 ∷ CS14 ∷ []) (pw2 c4 (CX40 ∷ Toff314 ∷ CCZ014 ∷ CS03 ∷ Toff314 ∷ CCZ014 ∷ CS03⁻ ∷ []) (Toff314 ∷ CCZ014 ∷ CCZ014 ∷ CS03 ∷ Toff314 ∷ CCZ014 ∷ CS03⁻ ∷ CX40 ∷ CCZ134 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 0 11 (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CS14 ∷ []) (sym (lem-F1-X-CS0-nf-of-rhs c4)) ▸ done


-- auto BOX(0;1234) | CCZ124: 1 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ124 : Complete 4 → ⟪ (Bx0-1234 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ124 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ CCZ124 ∷ []) (CCZ124 ∷ Bx0-1234 ∷ [])
  b0 = at 0 2 (CCZ124 ∷ Bx0-1234 ∷ []) (sym (lem-c124-beta c4)) ▸ done


-- auto BOX(0;1234) | CCZ124 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at2332 : Complete 4 → ⟪ (Bx0-1324 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at2332 c4 = run b0
  where
  b0 : Chain (Bx0-1324 ∷ CCZ134 ∷ []) (CCZ134 ∷ Bx0-1324 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ c4) ▸
       at 2 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 1 2 (CCZ124 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124 c4) ▸
       at 0 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 1 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ124 @243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at243243 : Complete 4 → ⟪ (Bx0-1423 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Bx0-1423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at243243 c4 = run b0
  where
  b0 : Chain (Bx0-1423 ∷ CCZ134 ∷ []) (CCZ134 ∷ Bx0-1423 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ c4) ▸
       at 2 2 (CCZ134 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ CCZ134 ∷ []) (CCZ134 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ134 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at2332 c4) ▸
       at 0 2 (CCZ134 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ CCZ134 ∷ []) (CCZ134 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ124 @0110243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at0110243243 : Complete 4 → ⟪ (Bx1-0423 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Bx1-0423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at0110243243 c4 = run b0
  where
  b0 : Chain (Bx1-0423 ∷ CCZ034 ∷ []) (CCZ034 ∷ Bx1-0423 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ c4) ▸
       at 2 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4) ▸
       at 1 2 (CCZ134 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at243243 c4) ▸
       at 0 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 1 2 (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ124 @0210243143: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at0210243143 : Complete 4 → ⟪ (Bx2-0413 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Bx2-0413 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at0210243143 c4 = run b0
  where
  b0 : Chain (Bx2-0413 ∷ CCZ034 ∷ []) (CCZ034 ∷ Bx2-0413 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ c4) ▸
       at 2 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 1 2 (CCZ034 ∷ Bx1-0423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at0110243243 c4) ▸
       at 0 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 1 2 (Bx2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0423⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CS21 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS21-at2332 : Complete 4 → ⟪ (Bx0-1324 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS21-at2332 c4 = run b0
  where
  b0 : Chain (Bx0-1324 ∷ CS13 ∷ []) (CS13 ∷ Bx0-1324 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ c4) ▸
       at 2 2 (CS12 ∷ Sw23 ∷ []) (lem-nat-2-CS13 c4) ▸
       at 1 2 (CS12 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS21 c4) ▸
       at 0 2 (CS13 ∷ Sw23 ∷ []) (lem-nat-2-CS12 c4) ▸
       at 1 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CS21 @243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS21-at243243 : Complete 4 → ⟪ (Bx0-1423 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ Bx0-1423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS21-at243243 c4 = run b0
  where
  b0 : Chain (Bx0-1423 ∷ CS14 ∷ []) (CS14 ∷ Bx0-1423 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ c4) ▸
       at 2 2 (CS13 ∷ Sw34 ∷ []) (lem-nat-3-CS14 c4) ▸
       at 1 2 (CS13 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS21-at2332 c4) ▸
       at 0 2 (CS14 ∷ Sw34 ∷ []) (lem-nat-3-CS13 c4) ▸
       at 1 2 (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CS21 @0110243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS21-at0110243243 : Complete 4 → ⟪ (Bx1-0423 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ Bx1-0423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS21-at0110243243 c4 = run b0
  where
  b0 : Chain (Bx1-0423 ∷ CS04 ∷ []) (CS04 ∷ Bx1-0423 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ c4) ▸
       at 2 2 (CS14 ∷ Sw01 ∷ []) (lem-nat-0-CS04 c4) ▸
       at 1 2 (CS14 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS21-at243243 c4) ▸
       at 0 2 (CS04 ∷ Sw01 ∷ []) (lem-nat-0-CS14 c4) ▸
       at 1 2 (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CS21 @0210243143: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS21-at0210243143 : Complete 4 → ⟪ (Bx2-0413 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ Bx2-0413 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS21-at0210243143 c4 = run b0
  where
  b0 : Chain (Bx2-0413 ∷ CS04 ∷ []) (CS04 ∷ Bx2-0413 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ c4) ▸
       at 2 2 (CS04 ∷ Sw12 ∷ []) (lem-nat-1-CS04 c4) ▸
       at 1 2 (CS04 ∷ Bx1-0423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS21-at0110243243 c4) ▸
       at 0 2 (CS04 ∷ Sw12 ∷ []) (lem-nat-1-CS04 c4) ▸
       at 1 2 (Bx2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0423⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- F1 X-CS1 [nf of rhs]: 32 steps
lem-F1-X-CS1-nf-of-rhs : Complete 4 → ⟪ (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CCZ014 ∷ CCZ014 ∷ CS03 ∷ Toff314 ∷ CX41 ∷ CZ04 ∷ CCZ014 ∷ CS03⁻ ∷ CCZ034 ∷ CS04 ∷ Bx2-0413 ∷ []) ⟫ʷ
lem-F1-X-CS1-nf-of-rhs c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS04 ∷ []) (CCZ014 ∷ Toff314 ∷ Toff314 ∷ Bx2-4103 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CX41 ∷ CS04 ∷ [])
  b0 = at 0 2 (CCZ014 ∷ []) (lem-SB2 c4) ▸
       at 2 5 (CX41 ∷ []) (lw0 c4 (CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ []) (CX41 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 1 (CS03 ∷ []) (refl) ▸
       at 5 1 (CS03⁻ ∷ []) (refl) ▸
       at 1 0 (Toff314 ∷ Toff314 ∷ []) (lw0 c4 [] (Toff314 ∷ Toff314 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Bx2-4013 ∷ []) (lem-sym12-at0210243143 c4) ▸
       at 3 1 (Bx2-4103 ∷ []) (lem-sym23-at0214203143 c4) ▸ done

  b1 : Chain (CCZ014 ∷ Toff314 ∷ Toff314 ∷ Bx2-4103 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CX41 ∷ CS04 ∷ []) (CCZ014 ∷ Toff314 ∷ CCZ014 ∷ CS03 ∷ Toff314 ∷ Toff314 ∷ Bx2-0413 ∷ Toff314 ∷ CS03⁻ ∷ CX41 ∷ CS04 ∷ [])
  b1 = at 3 1 (Bx2-4130 ∷ []) (lem-sym34-at0214213043 c4) ▸
       at 2 3 (Bx2-4130 ∷ CCZ014 ∷ []) (lem-T312-beta-at02142140 c4) ▸
       at 2 1 (Bx2-4103 ∷ []) (lem-sym34-at02142140 c4) ▸
       at 2 1 (Bx2-4013 ∷ []) (lem-sym23-at0214213043 c4) ▸
       at 2 1 (Bx2-0413 ∷ []) (lem-sym12-at0214203143 c4) ▸
       at 2 2 (CCZ014 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0210243143 c4) ▸
       at 3 2 (CS03 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS14-at0210243143 c4) ▸
       at 4 0 (Toff314 ∷ Toff314 ∷ []) (lw0 c4 [] (Toff314 ∷ Toff314 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (CCZ014 ∷ Toff314 ∷ CCZ014 ∷ CS03 ∷ Toff314 ∷ Toff314 ∷ Bx2-0413 ∷ Toff314 ∷ CS03⁻ ∷ CX41 ∷ CS04 ∷ []) (CCZ014 ∷ Toff314 ∷ CCZ014 ∷ CS03 ∷ Toff314 ∷ CCZ014 ∷ Bx2-0413 ∷ CS03⁻ ∷ CX41 ∷ CS04 ∷ [])
  b2 = at 6 1 (Bx2-4013 ∷ []) (lem-sym12-at0210243143 c4) ▸
       at 6 1 (Bx2-4103 ∷ []) (lem-sym23-at0214203143 c4) ▸
       at 6 1 (Bx2-4130 ∷ []) (lem-sym34-at0214213043 c4) ▸
       at 5 3 (Bx2-4130 ∷ CCZ014 ∷ []) (lem-T312-beta-at02142140 c4) ▸
       at 5 1 (Bx2-4103 ∷ []) (lem-sym34-at02142140 c4) ▸
       at 5 1 (Bx2-4013 ∷ []) (lem-sym23-at0214213043 c4) ▸
       at 5 1 (Bx2-0413 ∷ []) (lem-sym12-at0214203143 c4) ▸
       at 5 2 (CCZ014 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0210243143 c4) ▸ done

  b3 : Chain (CCZ014 ∷ Toff314 ∷ CCZ014 ∷ CS03 ∷ Toff314 ∷ CCZ014 ∷ Bx2-0413 ∷ CS03⁻ ∷ CX41 ∷ CS04 ∷ []) (Toff314 ∷ CCZ014 ∷ CCZ014 ∷ CS03 ∷ Toff314 ∷ CX41 ∷ CZ04 ∷ CCZ014 ∷ CS03⁻ ∷ CCZ034 ∷ CS04 ∷ Bx2-0413 ∷ [])
  b3 = at 6 2 (CS03⁻ ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd14-at0210243143 c4) ▸
       at 7 0 (CX41 ∷ CX41 ∷ []) (lw0 c4 [] (CX41 ∷ CX41 ∷ []) tt tt Eq.refl) ▸
       at 8 3 (Bx2-0413 ∷ CCZ034 ∷ []) (lem-CX23-beta-at0210243143 c4) ▸
       at 8 2 (CCZ034 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at0210243143 c4) ▸
       at 9 2 (CS04 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS21-at0210243143 c4) ▸
       at 6 2 (CX41 ∷ CS03⁻ ∷ []) (pw2 c4 (CS03⁻ ∷ CX41 ∷ []) (CX41 ∷ CS03⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CX41 ∷ CZ04 ∷ CCZ014 ∷ []) (pw2 c4 (CCZ014 ∷ CX41 ∷ []) (CX41 ∷ CZ04 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Toff314 ∷ CCZ014 ∷ []) (pw2 c4 (CCZ014 ∷ Toff314 ∷ []) (Toff314 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸ done


-- F1 X-CS1: 26 steps
lem-F1-X-CS1 : Complete 4 → ⟪ (CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS04 ∷ []) ⟫ʷ
lem-F1-X-CS1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ []) (CX41 ∷ Toff314 ∷ Toff314 ∷ Bx2-4130 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b0 = at 0 5 (CX41 ∷ []) (lw0 c4 (CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ []) (CX41 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 1 (CS03 ∷ []) (refl) ▸
       at 5 1 (CS03⁻ ∷ []) (refl) ▸
       at 1 0 (Toff314 ∷ Toff314 ∷ []) (lw0 c4 [] (Toff314 ∷ Toff314 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Bx2-4013 ∷ []) (lem-sym12-at0210243143 c4) ▸
       at 3 1 (Bx2-4103 ∷ []) (lem-sym23-at0214203143 c4) ▸
       at 3 1 (Bx2-4130 ∷ []) (lem-sym34-at0214213043 c4) ▸ done

  b1 : Chain (CX41 ∷ Toff314 ∷ Toff314 ∷ Bx2-4130 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (CX41 ∷ Toff314 ∷ CCZ014 ∷ CS03 ∷ Toff314 ∷ Toff314 ∷ Bx2-4013 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b1 = at 2 3 (Bx2-4130 ∷ CCZ014 ∷ []) (lem-T312-beta-at02142140 c4) ▸
       at 2 1 (Bx2-4103 ∷ []) (lem-sym34-at02142140 c4) ▸
       at 2 1 (Bx2-4013 ∷ []) (lem-sym23-at0214213043 c4) ▸
       at 2 1 (Bx2-0413 ∷ []) (lem-sym12-at0214203143 c4) ▸
       at 2 2 (CCZ014 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0210243143 c4) ▸
       at 3 2 (CS03 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS14-at0210243143 c4) ▸
       at 4 0 (Toff314 ∷ Toff314 ∷ []) (lw0 c4 [] (Toff314 ∷ Toff314 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Bx2-4013 ∷ []) (lem-sym12-at0210243143 c4) ▸ done

  b2 : Chain (CX41 ∷ Toff314 ∷ CCZ014 ∷ CS03 ∷ Toff314 ∷ Toff314 ∷ Bx2-4013 ∷ Toff314 ∷ CS03⁻ ∷ []) (CX41 ∷ Toff314 ∷ CCZ014 ∷ CS03 ∷ Toff314 ∷ CCZ014 ∷ CS03⁻ ∷ Bx2-0413 ∷ [])
  b2 = at 6 1 (Bx2-4103 ∷ []) (lem-sym23-at0214203143 c4) ▸
       at 6 1 (Bx2-4130 ∷ []) (lem-sym34-at0214213043 c4) ▸
       at 5 3 (Bx2-4130 ∷ CCZ014 ∷ []) (lem-T312-beta-at02142140 c4) ▸
       at 5 1 (Bx2-4103 ∷ []) (lem-sym34-at02142140 c4) ▸
       at 5 1 (Bx2-4013 ∷ []) (lem-sym23-at0214213043 c4) ▸
       at 5 1 (Bx2-0413 ∷ []) (lem-sym12-at0214203143 c4) ▸
       at 5 2 (CCZ014 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0210243143 c4) ▸
       at 6 2 (CS03⁻ ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd14-at0210243143 c4) ▸ done

  b3 : Chain (CX41 ∷ Toff314 ∷ CCZ014 ∷ CS03 ∷ Toff314 ∷ CCZ014 ∷ CS03⁻ ∷ Bx2-0413 ∷ []) (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS04 ∷ [])
  b3 = at 0 7 (Toff314 ∷ CCZ014 ∷ CCZ014 ∷ CS03 ∷ Toff314 ∷ CX41 ∷ CZ04 ∷ CCZ014 ∷ CS03⁻ ∷ CCZ034 ∷ CS04 ∷ []) (pw2 c4 (CX41 ∷ Toff314 ∷ CCZ014 ∷ CS03 ∷ Toff314 ∷ CCZ014 ∷ CS03⁻ ∷ []) (Toff314 ∷ CCZ014 ∷ CCZ014 ∷ CS03 ∷ Toff314 ∷ CX41 ∷ CZ04 ∷ CCZ014 ∷ CS03⁻ ∷ CCZ034 ∷ CS04 ∷ []) tt tt Eq.refl) ▸
       at 0 12 (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS04 ∷ []) (sym (lem-F1-X-CS1-nf-of-rhs c4)) ▸ done


-- auto BOX(0;1234) | CS13: 3 steps
lem-auto-BOX⟨0·1234⟩-∣-CS13 : Complete 4 → ⟪ (Bx0-1234 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS13 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ CS13 ∷ []) (CS13 ∷ Bx0-1234 ∷ [])
  b0 = at 0 1 (Bx0-1324 ∷ []) (lem-sym23 c4) ▸
       at 0 2 (CS13 ∷ Bx0-1324 ∷ []) (sym (lem-CS12-beta-at2332 c4)) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym23-at2332 c4) ▸ done


-- auto BOX(0;1234) | CCZ134: 3 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ134 : Complete 4 → ⟪ (Bx0-1234 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ134 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ CCZ134 ∷ []) (CCZ134 ∷ Bx0-1234 ∷ [])
  b0 = at 0 1 (Bx0-1324 ∷ []) (lem-sym23 c4) ▸
       at 0 2 (CCZ134 ∷ Bx0-1324 ∷ []) (sym (lem-c124-beta-at2332 c4)) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym23-at2332 c4) ▸ done


-- X1-beta @1221: 8 steps
lem-X1-beta-at1221 : Complete 4 → ⟪ (X2 ∷ Bx0-2134 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Bx0-2134 ∷ []) ⟫ʷ
lem-X1-beta-at1221 c4 = run b0
  where
  b0 : Chain (X2 ∷ Bx0-2134 ∷ X2 ∷ []) (CCZ134 ∷ Bx0-2134 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (X1 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ X2 ∷ []) (X1 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-1234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2134⟩ c4) ▸
       at 3 2 (X1 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ X2 ∷ []) (X1 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (CCZ234 ∷ Bx0-1234 ∷ []) (lem-X1-beta c4) ▸
       at 0 2 (CCZ134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ234 ∷ []) (CCZ134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-2134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1234⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- X1-beta @132132: 8 steps
lem-X1-beta-at132132 : Complete 4 → ⟪ (X3 ∷ Bx0-3124 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Bx0-3124 ∷ []) ⟫ʷ
lem-X1-beta-at132132 c4 = run b0
  where
  b0 : Chain (X3 ∷ Bx0-3124 ∷ X3 ∷ []) (CCZ124 ∷ Bx0-3124 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (X2 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ X3 ∷ []) (X2 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-2134 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3124⟩ c4) ▸
       at 3 2 (X2 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ X3 ∷ []) (X2 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (CCZ134 ∷ Bx0-2134 ∷ []) (lem-X1-beta-at1221 c4) ▸
       at 0 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 1 2 (Bx0-3124 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·2134⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- X1-beta @14213243: 8 steps
lem-X1-beta-at14213243 : Complete 4 → ⟪ (X4 ∷ Bx0-4123 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Bx0-4123 ∷ []) ⟫ʷ
lem-X1-beta-at14213243 c4 = run b0
  where
  b0 : Chain (X4 ∷ Bx0-4123 ∷ X4 ∷ []) (CCZ123 ∷ Bx0-4123 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (X3 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ X4 ∷ []) (X3 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-3124 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·4123⟩ c4) ▸
       at 3 2 (X3 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ X4 ∷ []) (X3 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (CCZ124 ∷ Bx0-3124 ∷ []) (lem-X1-beta-at132132 c4) ▸
       at 0 2 (CCZ123 ∷ Sw34 ∷ []) (lem-nat-3-CCZ124 c4) ▸
       at 1 2 (Bx0-4123 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·3124⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- X1-beta @0114203243: 8 steps
lem-X1-beta-at0114203243 : Complete 4 → ⟪ (X4 ∷ Bx1-4023 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ Bx1-4023 ∷ []) ⟫ʷ
lem-X1-beta-at0114203243 c4 = run b0
  where
  b0 : Chain (X4 ∷ Bx1-4023 ∷ X4 ∷ []) (CCZ023 ∷ Bx1-4023 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (X4 ∷ Sw01 ∷ []) (c₂ (Swap) (X ↑ ↑)) ▸
       at 2 2 (Bx0-4123 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·4023⟩ c4) ▸
       at 3 2 (X4 ∷ Sw01 ∷ []) (c₂ (Swap) (X ↑ ↑)) ▸
       at 1 3 (CCZ123 ∷ Bx0-4123 ∷ []) (lem-X1-beta-at14213243 c4) ▸
       at 0 2 (CCZ023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ123 ∷ []) (CCZ023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-4023 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·4123⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- X1-beta @0214203143: 8 steps
lem-X1-beta-at0214203143 : Complete 4 → ⟪ (X4 ∷ Bx2-4013 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ Bx2-4013 ∷ []) ⟫ʷ
lem-X1-beta-at0214203143 c4 = run b0
  where
  b0 : Chain (X4 ∷ Bx2-4013 ∷ X4 ∷ []) (CCZ013 ∷ Bx2-4013 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (X4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (X ↑)) ▸
       at 2 2 (Bx1-4023 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·4013⟩ c4) ▸
       at 3 2 (X4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (X ↑)) ▸
       at 1 3 (CCZ023 ∷ Bx1-4023 ∷ []) (lem-X1-beta-at0114203243 c4) ▸
       at 0 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 1 2 (Bx2-4013 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·4023⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CS13 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS13-at2332 : Complete 4 → ⟪ (Bx0-1324 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS13-at2332 c4 = run b0
  where
  b0 : Chain (Bx0-1324 ∷ CS12 ∷ []) (CS12 ∷ Bx0-1324 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ c4) ▸
       at 2 2 (CS13 ∷ Sw23 ∷ []) (lem-nat-2-CS12 c4) ▸
       at 1 2 (CS13 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS13 c4) ▸
       at 0 2 (CS12 ∷ Sw23 ∷ []) (lem-nat-2-CS13 c4) ▸
       at 1 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CS13 @243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS13-at243243 : Complete 4 → ⟪ (Bx0-1423 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ Bx0-1423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS13-at243243 c4 = run b0
  where
  b0 : Chain (Bx0-1423 ∷ CS12 ∷ []) (CS12 ∷ Bx0-1423 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ c4) ▸
       at 2 2 (CS12 ∷ Sw34 ∷ []) (sym (c₃ (CS ↑) (Swap))) ▸
       at 1 2 (CS12 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS13-at2332 c4) ▸
       at 0 2 (CS12 ∷ Sw34 ∷ []) (sym (c₃ (CS ↑) (Swap))) ▸
       at 1 2 (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CS13 @0110243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS13-at0110243243 : Complete 4 → ⟪ (Bx1-0423 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ Bx1-0423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS13-at0110243243 c4 = run b0
  where
  b0 : Chain (Bx1-0423 ∷ CS02 ∷ []) (CS02 ∷ Bx1-0423 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ c4) ▸
       at 2 2 (CS12 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS02 ∷ []) (CS12 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS12 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS13-at243243 c4) ▸
       at 0 2 (CS02 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CS13 @0210243143: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS13-at0210243143 : Complete 4 → ⟪ (Bx2-0413 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ Bx2-0413 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS13-at0210243143 c4 = run b0
  where
  b0 : Chain (Bx2-0413 ∷ CS01 ∷ []) (CS01 ∷ Bx2-0413 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ c4) ▸
       at 2 2 (CS02 ∷ Sw12 ∷ []) (lem-nat-1-CS01 c4) ▸
       at 1 2 (CS02 ∷ Bx1-0423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS13-at0110243243 c4) ▸
       at 0 2 (CS01 ∷ Sw12 ∷ []) (lem-nat-1-CS02 c4) ▸
       at 1 2 (Bx2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0423⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ134 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at2332 : Complete 4 → ⟪ (Bx0-1324 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at2332 c4 = run b0
  where
  b0 : Chain (Bx0-1324 ∷ CCZ124 ∷ []) (CCZ124 ∷ Bx0-1324 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ c4) ▸
       at 2 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 1 2 (CCZ134 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ134 c4) ▸
       at 0 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 1 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ134 @243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at243243 : Complete 4 → ⟪ (Bx0-1423 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Bx0-1423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at243243 c4 = run b0
  where
  b0 : Chain (Bx0-1423 ∷ CCZ123 ∷ []) (CCZ123 ∷ Bx0-1423 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ c4) ▸
       at 2 2 (CCZ124 ∷ Sw34 ∷ []) (lem-nat-3-CCZ123 c4) ▸
       at 1 2 (CCZ124 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at2332 c4) ▸
       at 0 2 (CCZ123 ∷ Sw34 ∷ []) (lem-nat-3-CCZ124 c4) ▸
       at 1 2 (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ134 @0110243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at0110243243 : Complete 4 → ⟪ (Bx1-0423 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ Bx1-0423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at0110243243 c4 = run b0
  where
  b0 : Chain (Bx1-0423 ∷ CCZ023 ∷ []) (CCZ023 ∷ Bx1-0423 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ c4) ▸
       at 2 2 (CCZ123 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ023 ∷ []) (CCZ123 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ123 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at243243 c4) ▸
       at 0 2 (CCZ023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ123 ∷ []) (CCZ023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ134 @0210243143: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at0210243143 : Complete 4 → ⟪ (Bx2-0413 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ Bx2-0413 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at0210243143 c4 = run b0
  where
  b0 : Chain (Bx2-0413 ∷ CCZ013 ∷ []) (CCZ013 ∷ Bx2-0413 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ c4) ▸
       at 2 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 1 2 (CCZ023 ∷ Bx1-0423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at0110243243 c4) ▸
       at 0 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 1 2 (Bx2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0423⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- F5 CS01: 38 steps
lem-F5-CS01 : Complete 4 → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ []) ⟫ʷ
lem-F5-CS01 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (run b4))))
  where
  b0 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (CCZ013 ∷ Bx2-0413 ∷ X4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b0 = at 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 1 (CS03 ∷ []) (refl) ▸
       at 5 1 (CS03⁻ ∷ []) (refl) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Bx2-4013 ∷ []) (lem-sym12-at0210243143 c4) ▸
       at 0 3 (CCZ013 ∷ Bx2-4013 ∷ []) (lem-X1-beta-at0214203143 c4) ▸
       at 1 1 (Bx2-0413 ∷ []) (lem-sym12-at0214203143 c4) ▸
       at 8 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ013 ∷ Bx2-0413 ∷ X4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (CCZ013 ∷ CS01 ∷ CCZ013 ∷ CS03 ∷ Toff314 ∷ Toff314 ∷ Bx2-4013 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b1 = at 10 1 (CS03 ∷ []) (refl) ▸
       at 12 1 (CS03⁻ ∷ []) (refl) ▸
       at 2 6 (CS01 ∷ CCZ013 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ []) (pw2 c4 (X4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ []) (CS01 ∷ CCZ013 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS01 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS13-at0210243143 c4) ▸
       at 2 2 (CCZ013 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at0210243143 c4) ▸
       at 3 2 (CS03 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS14-at0210243143 c4) ▸
       at 4 0 (Toff314 ∷ Toff314 ∷ []) (lw0 c4 [] (Toff314 ∷ Toff314 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Bx2-4013 ∷ []) (lem-sym12-at0210243143 c4) ▸ done

  b2 : Chain (CCZ013 ∷ CS01 ∷ CCZ013 ∷ CS03 ∷ Toff314 ∷ Toff314 ∷ Bx2-4013 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (CCZ013 ∷ CS01 ∷ CCZ013 ∷ CS03 ∷ Toff314 ∷ CCZ014 ∷ CS03⁻ ∷ Bx2-0413 ∷ Toff314 ∷ Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b2 = at 6 1 (Bx2-4103 ∷ []) (lem-sym23-at0214203143 c4) ▸
       at 6 1 (Bx2-4130 ∷ []) (lem-sym34-at0214213043 c4) ▸
       at 5 3 (Bx2-4130 ∷ CCZ014 ∷ []) (lem-T312-beta-at02142140 c4) ▸
       at 5 1 (Bx2-4103 ∷ []) (lem-sym34-at02142140 c4) ▸
       at 5 1 (Bx2-4013 ∷ []) (lem-sym23-at0214213043 c4) ▸
       at 5 1 (Bx2-0413 ∷ []) (lem-sym12-at0214203143 c4) ▸
       at 5 2 (CCZ014 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0210243143 c4) ▸
       at 6 2 (CS03⁻ ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd14-at0210243143 c4) ▸ done

  b3 : Chain (CCZ013 ∷ CS01 ∷ CCZ013 ∷ CS03 ∷ Toff314 ∷ CCZ014 ∷ CS03⁻ ∷ Bx2-0413 ∷ Toff314 ∷ Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (CCZ013 ∷ CS01 ∷ CCZ013 ∷ CS03 ∷ Toff314 ∷ CCZ014 ∷ CS03⁻ ∷ Toff314 ∷ Bx2-0413 ∷ CCZ014 ∷ Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b3 = at 7 0 (Toff314 ∷ Toff314 ∷ []) (lw0 c4 [] (Toff314 ∷ Toff314 ∷ []) tt tt Eq.refl) ▸
       at 9 1 (Bx2-4013 ∷ []) (lem-sym12-at0210243143 c4) ▸
       at 9 1 (Bx2-4103 ∷ []) (lem-sym23-at0214203143 c4) ▸
       at 9 1 (Bx2-4130 ∷ []) (lem-sym34-at0214213043 c4) ▸
       at 8 3 (Bx2-4130 ∷ CCZ014 ∷ []) (lem-T312-beta-at02142140 c4) ▸
       at 8 1 (Bx2-4103 ∷ []) (lem-sym34-at02142140 c4) ▸
       at 8 1 (Bx2-4013 ∷ []) (lem-sym23-at0214213043 c4) ▸
       at 8 1 (Bx2-0413 ∷ []) (lem-sym12-at0214203143 c4) ▸ done

  b4 : Chain (CCZ013 ∷ CS01 ∷ CCZ013 ∷ CS03 ∷ Toff314 ∷ CCZ014 ∷ CS03⁻ ∷ Toff314 ∷ Bx2-0413 ∷ CCZ014 ∷ Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (CS01 ∷ [])
  b4 = at 8 2 (CCZ014 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0210243143 c4) ▸
       at 1 5 (CCZ014 ∷ CS01 ∷ CCZ013 ∷ CS03 ∷ Toff314 ∷ []) (pw2 c4 (CS01 ∷ CCZ013 ∷ CS03 ∷ Toff314 ∷ CCZ014 ∷ []) (CCZ014 ∷ CS01 ∷ CCZ013 ∷ CS03 ∷ Toff314 ∷ []) tt tt Eq.refl) ▸
       at 2 7 (CCZ014 ∷ CS01 ∷ CCZ013 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ []) (pw2 c4 (CS01 ∷ CCZ013 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ CCZ014 ∷ []) (CCZ014 ∷ CS01 ∷ CCZ013 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ []) tt tt Eq.refl) ▸
       at 1 2 [] (pw2 c4 (CCZ014 ∷ CCZ014 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 [] (lem-beta-inv-at0210243143 c4) ▸
       at 0 11 (CS01 ∷ []) (pw2 c4 (CCZ013 ∷ CS01 ∷ CCZ013 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (CS01 ∷ []) tt tt Eq.refl) ▸ done


-- beta-T @2442: 8 steps
lem-beta-T-at2442 : Complete 4 → ⟪ (Bx0-1432 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) ⟫ʷ
lem-beta-T-at2442 c4 = run b0
  where
  b0 : Chain (Bx0-1432 ∷ []) (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1423 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1432⟩ c4) ▸
       at 1 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-beta-T-at243243 c4) ▸
       at 0 2 (Toff014 ∷ Sw23 ∷ []) (lem-nat-2-TOFF014 c4) ▸
       at 1 2 (CCZ023 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ023 ∷ []) (CCZ023 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff014 ∷ Sw23 ∷ []) (lem-nat-2-TOFF014 c4) ▸
       at 3 2 (CCZ023 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ023 ∷ []) (CCZ023 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;2;3) | BOX(0;1432): 14 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·1432⟩ : Complete 4 → ⟪ (Sb⁻0-1-2-3 ∷ Bx0-1432 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1432 ∷ Sb⁻0-1-2-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·1432⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb⁻0-1-2-3 ∷ Bx0-1432 ∷ []) (Toff014 ∷ CCZ023 ∷ CS12⁻ ∷ Toff014 ∷ CCZ023 ∷ [])
  b0 = at 1 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-beta-T-at2442 c4) ▸
       at 0 1 (CS12⁻ ∷ []) (refl) ▸
       at 0 2 (Toff014 ∷ CS12⁻ ∷ []) (pw3 c4 (CS12⁻ ∷ Toff014 ∷ []) (Toff014 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 1 1 (CS12⁻ ∷ []) (refl) ▸
       at 1 2 (CCZ023 ∷ CS12⁻ ∷ []) (lw4 c4 (CS12⁻ ∷ CCZ023 ∷ []) (CCZ023 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 2 1 (CS12⁻ ∷ []) (refl) ▸ done

  b1 : Chain (Toff014 ∷ CCZ023 ∷ CS12⁻ ∷ Toff014 ∷ CCZ023 ∷ []) (Bx0-1432 ∷ Sb⁻0-1-2-3 ∷ [])
  b1 = at 2 2 (Toff014 ∷ CS12⁻ ∷ []) (pw3 c4 (CS12⁻ ∷ Toff014 ∷ []) (Toff014 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 3 1 (CS12⁻ ∷ []) (refl) ▸
       at 3 2 (CCZ023 ∷ CS12⁻ ∷ []) (lw4 c4 (CS12⁻ ∷ CCZ023 ∷ []) (CCZ023 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 0 4 (Bx0-1432 ∷ []) (sym (lem-beta-T-at2442 c4)) ▸ done


-- auto SBOXd(0;1;2;3) | SBOX(0;1;43;2): 13 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩ : Complete 4 → ⟪ (Sb⁻0-1-2-3 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-43-2 ∷ Sb⁻0-1-2-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb⁻0-1-2-3 ∷ Sb0-1-43-2 ∷ []) (Bx0-1432 ∷ Toff234 ∷ Sb0-1-2-3 ∷ Toff234 ∷ CS12⁻ ∷ Sb⁻0-1-2-3 ∷ [])
  b0 = at 1 1 (Bx0-1432 ∷ Toff234 ∷ Sb0-1-2-3 ∷ Toff234 ∷ Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 0 2 (Bx0-1432 ∷ Sb⁻0-1-2-3 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·1432⟩ c4) ▸
       at 1 1 (CS12⁻ ∷ []) (refl) ▸
       at 3 1 (CS12 ∷ []) (refl) ▸
       at 1 4 (Toff234 ∷ CS12 ∷ Toff234 ∷ CS12⁻ ∷ []) (lw0 c4 (CS12⁻ ∷ Toff234 ∷ CS12 ∷ Toff234 ∷ []) (Toff234 ∷ CS12 ∷ Toff234 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb0-1-2-3 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 4 1 (CS12⁻ ∷ []) (refl) ▸ done

  b1 : Chain (Bx0-1432 ∷ Toff234 ∷ Sb0-1-2-3 ∷ Toff234 ∷ CS12⁻ ∷ Sb⁻0-1-2-3 ∷ []) (Sb0-1-43-2 ∷ Sb⁻0-1-2-3 ∷ [])
  b1 = at 5 1 (CS12⁻ ∷ []) (refl) ▸
       at 4 2 (CS12⁻ ∷ CS12⁻ ∷ []) (lw4 c4 (CS12⁻ ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 5 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 0 5 (Sb0-1-43-2 ∷ []) (refl) ▸ done


-- auto Kd0 | BOX(0;1234): 1 steps
lem-auto-Kd0-∣-BOX⟨0·1234⟩ : Complete 4 → ⟪ (K0⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ K0⁻ ∷ []) ⟫ʷ
lem-auto-Kd0-∣-BOX⟨0·1234⟩ c4 = run b0
  where
  b0 : Chain (K0⁻ ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ K0⁻ ∷ [])
  b0 = at 0 2 (Bx0-1234 ∷ K0⁻ ∷ []) (lem-K0-pass-ci c4) ▸ done


-- F0 @1221: 5 steps
lem-F0-at1221 : Complete 4 → ⟪ (Sb1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-42-1 ∷ []) ⟫ʷ
lem-F0-at1221 c4 = run b0
  where
  b0 : Chain (Sb1-0-42-3 ∷ []) (Sb3-0-42-1 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ c4) ▸
       at 1 1 (Sb3-0-41-2 ∷ []) (lem-F0 c4) ▸
       at 0 2 (Sb3-0-42-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·41·2⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- F0 @132132: 5 steps
lem-F0-at132132 : Complete 4 → ⟪ (Sb1-0-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-43-1 ∷ []) ⟫ʷ
lem-F0-at132132 c4 = run b0
  where
  b0 : Chain (Sb1-0-43-2 ∷ []) (Sb2-0-43-1 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·43·2⟩ c4) ▸
       at 1 1 (Sb3-0-42-1 ∷ []) (lem-F0-at1221 c4) ▸
       at 0 2 (Sb2-0-43-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·0·42·1⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- F0 @14213243: 5 steps
lem-F0-at14213243 : Complete 4 → ⟪ (Sb1-0-34-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-34-1 ∷ []) ⟫ʷ
lem-F0-at14213243 c4 = run b0
  where
  b0 : Chain (Sb1-0-34-2 ∷ []) (Sb2-0-34-1 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb1-0-43-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨1·0·34·2⟩ c4) ▸
       at 1 1 (Sb2-0-43-1 ∷ []) (lem-F0-at132132 c4) ▸
       at 0 2 (Sb2-0-34-1 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨2·0·43·1⟩ c4) ▸
       at 1 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- F0 @0114203243: 5 steps
lem-F0-at0114203243 : Complete 4 → ⟪ (Sb0-1-34-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-1-34-0 ∷ []) ⟫ʷ
lem-F0-at0114203243 c4 = run b0
  where
  b0 : Chain (Sb0-1-34-2 ∷ []) (Sb2-1-34-0 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb1-0-34-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·34·2⟩ c4) ▸
       at 1 1 (Sb2-0-34-1 ∷ []) (lem-F0-at14213243 c4) ▸
       at 0 2 (Sb2-1-34-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·0·34·1⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- F0 @0214203143: 5 steps
lem-F0-at0214203143 : Complete 4 → ⟪ (Sb0-2-34-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-34-0 ∷ []) ⟫ʷ
lem-F0-at0214203143 c4 = run b0
  where
  b0 : Chain (Sb0-2-34-1 ∷ []) (Sb1-2-34-0 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-34-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·34·1⟩ c4) ▸
       at 1 1 (Sb2-1-34-0 ∷ []) (lem-F0-at0114203243 c4) ▸
       at 0 2 (Sb1-2-34-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·1·34·0⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- F0 @0214213043: 5 steps
lem-F0-at0214213043 : Complete 4 → ⟪ (Sb1-2-34-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-34-1 ∷ []) ⟫ʷ
lem-F0-at0214213043 c4 = run b0
  where
  b0 : Chain (Sb1-2-34-0 ∷ []) (Sb0-2-34-1 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-2-34-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·2·34·0⟩ c4) ▸
       at 1 1 (Sb1-2-34-0 ∷ []) (lem-F0-at0214203143 c4) ▸
       at 0 2 (Sb0-2-34-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·2·34·0⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto Kd0 | BOX(0;1234) @3443: 7 steps
lem-auto-Kd0-∣-BOX⟨0·1234⟩-at3443 : Complete 4 → ⟪ (K0⁻ ∷ Bx0-1243 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1243 ∷ K0⁻ ∷ []) ⟫ʷ
lem-auto-Kd0-∣-BOX⟨0·1234⟩-at3443 c4 = run b0
  where
  b0 : Chain (K0⁻ ∷ Bx0-1243 ∷ []) (Bx0-1243 ∷ K0⁻ ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (K0⁻ ∷ Sw34 ∷ []) (sym (c₁ (K • iI) (Swap ↑ ↑))) ▸
       at 2 2 (Bx0-1234 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1243⟩ c4) ▸
       at 1 2 (Bx0-1234 ∷ K0⁻ ∷ []) (lem-auto-Kd0-∣-BOX⟨0·1234⟩ c4) ▸
       at 0 2 (Bx0-1243 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1234⟩ c4) ▸
       at 1 2 (K0⁻ ∷ Sw34 ∷ []) (sym (c₁ (K • iI) (Swap ↑ ↑))) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto Kd0 | BOX(0;1234) @233442: 7 steps
lem-auto-Kd0-∣-BOX⟨0·1234⟩-at233442 : Complete 4 → ⟪ (K0⁻ ∷ Bx0-1342 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1342 ∷ K0⁻ ∷ []) ⟫ʷ
lem-auto-Kd0-∣-BOX⟨0·1234⟩-at233442 c4 = run b0
  where
  b0 : Chain (K0⁻ ∷ Bx0-1342 ∷ []) (Bx0-1342 ∷ K0⁻ ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (K0⁻ ∷ Sw23 ∷ []) (sym (c₁ (K • iI) (Swap ↑))) ▸
       at 2 2 (Bx0-1243 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1342⟩ c4) ▸
       at 1 2 (Bx0-1243 ∷ K0⁻ ∷ []) (lem-auto-Kd0-∣-BOX⟨0·1234⟩-at3443 c4) ▸
       at 0 2 (Bx0-1342 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1243⟩ c4) ▸
       at 1 2 (K0⁻ ∷ Sw23 ∷ []) (sym (c₁ (K • iI) (Swap ↑))) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto Kd0 | BOX(0;1234) @12233441: 7 steps
lem-auto-Kd0-∣-BOX⟨0·1234⟩-at12233441 : Complete 4 → ⟪ (K0⁻ ∷ Bx0-2341 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2341 ∷ K0⁻ ∷ []) ⟫ʷ
lem-auto-Kd0-∣-BOX⟨0·1234⟩-at12233441 c4 = run b0
  where
  b0 : Chain (K0⁻ ∷ Bx0-2341 ∷ []) (Bx0-2341 ∷ K0⁻ ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (K0⁻ ∷ Sw12 ∷ []) (sym (c₁ (K • iI) (Swap))) ▸
       at 2 2 (Bx0-1342 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2341⟩ c4) ▸
       at 1 2 (Bx0-1342 ∷ K0⁻ ∷ []) (lem-auto-Kd0-∣-BOX⟨0·1234⟩-at233442 c4) ▸
       at 0 2 (Bx0-2341 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1342⟩ c4) ▸
       at 1 2 (K0⁻ ∷ Sw12 ∷ []) (sym (c₁ (K • iI) (Swap))) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto Kd0 | SBOX(1;2;34;0): 13 steps
lem-auto-Kd0-∣-SBOX⟨1·2·34·0⟩ : Complete 4 → ⟪ (K0⁻ ∷ Sb1-2-34-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-34-0 ∷ K0⁻ ∷ []) ⟫ʷ
lem-auto-Kd0-∣-SBOX⟨1·2·34·0⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (K0⁻ ∷ Sb1-2-34-0 ∷ []) (Bx0-2341 ∷ Toff134 ∷ Sb0-2-1-4 ∷ Toff134 ∷ K0⁻ ∷ Sb⁻0-2-1-4 ∷ [])
  b0 = at 1 1 (Sb0-2-34-1 ∷ []) (lem-F0-at0214213043 c4) ▸
       at 1 1 (Bx0-2341 ∷ Toff134 ∷ Sb0-2-1-4 ∷ Toff134 ∷ Sb⁻0-2-1-4 ∷ []) (refl) ▸
       at 0 2 (Bx0-2341 ∷ K0⁻ ∷ []) (lem-auto-Kd0-∣-BOX⟨0·1234⟩-at12233441 c4) ▸
       at 1 2 (Toff134 ∷ K0⁻ ∷ []) (pw2 c4 (K0⁻ ∷ Toff134 ∷ []) (Toff134 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 1 (CS12 ∷ []) (refl) ▸
       at 2 2 (CS12 ∷ K0⁻ ∷ []) (lw4 c4 (K0⁻ ∷ CS12 ∷ []) (CS12 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb0-2-1-4 ∷ []) (refl) ▸
       at 3 2 (Toff134 ∷ K0⁻ ∷ []) (pw2 c4 (K0⁻ ∷ Toff134 ∷ []) (Toff134 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Bx0-2341 ∷ Toff134 ∷ Sb0-2-1-4 ∷ Toff134 ∷ K0⁻ ∷ Sb⁻0-2-1-4 ∷ []) (Sb1-2-34-0 ∷ K0⁻ ∷ [])
  b1 = at 5 1 (CS12⁻ ∷ []) (refl) ▸
       at 4 2 (CS12⁻ ∷ K0⁻ ∷ []) (lw4 c4 (K0⁻ ∷ CS12⁻ ∷ []) (CS12⁻ ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb⁻0-2-1-4 ∷ []) (refl) ▸
       at 0 5 (Sb0-2-34-1 ∷ []) (refl) ▸
       at 0 1 (Sb1-2-34-0 ∷ []) (sym (lem-F0-at0214213043 c4)) ▸ done


-- sym12 @13213442: 5 steps
lem-sym12-at13213442 : Complete 4 → ⟪ (Bx0-3142 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1342 ∷ []) ⟫ʷ
lem-sym12-at13213442 c4 = run b0
  where
  b0 : Chain (Bx0-3142 ∷ []) (Bx0-1342 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-2143 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3142⟩ c4) ▸
       at 1 1 (Bx0-1243 ∷ []) (lem-sym12-at12213443 c4) ▸
       at 0 2 (Bx0-1342 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1243⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym12 @0113203442: 5 steps
lem-sym12-at0113203442 : Complete 4 → ⟪ (Bx1-3042 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0342 ∷ []) ⟫ʷ
lem-sym12-at0113203442 c4 = run b0
  where
  b0 : Chain (Bx1-3042 ∷ []) (Bx1-0342 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-3142 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·3042⟩ c4) ▸
       at 1 1 (Bx0-1342 ∷ []) (lem-sym12-at13213442 c4) ▸
       at 0 2 (Bx1-0342 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1342⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym12 @0213203441: 5 steps
lem-sym12-at0213203441 : Complete 4 → ⟪ (Bx2-3041 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0341 ∷ []) ⟫ʷ
lem-sym12-at0213203441 c4 = run b0
  where
  b0 : Chain (Bx2-3041 ∷ []) (Bx2-0341 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-3042 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·3041⟩ c4) ▸
       at 1 1 (Bx1-0342 ∷ []) (lem-sym12-at0113203442 c4) ▸
       at 0 2 (Bx2-0341 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0342⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym34 @0110233442: 5 steps
lem-sym34-at0110233442 : Complete 4 → ⟪ (Bx1-0342 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0324 ∷ []) ⟫ʷ
lem-sym34-at0110233442 c4 = run b0
  where
  b0 : Chain (Bx1-0342 ∷ []) (Bx1-0324 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1342 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0342⟩ c4) ▸
       at 1 1 (Bx0-1324 ∷ []) (lem-sym34-at233442 c4) ▸
       at 0 2 (Bx1-0324 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1324⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym34 @0210233441: 5 steps
lem-sym34-at0210233441 : Complete 4 → ⟪ (Bx2-0341 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0314 ∷ []) ⟫ʷ
lem-sym34-at0210233441 c4 = run b0
  where
  b0 : Chain (Bx2-0341 ∷ []) (Bx2-0314 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-0342 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0341⟩ c4) ▸
       at 1 1 (Bx1-0324 ∷ []) (lem-sym34-at0110233442 c4) ▸
       at 0 2 (Bx2-0314 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0324⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym23 @01102332: 5 steps
lem-sym23-at01102332 : Complete 4 → ⟪ (Bx1-0324 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0234 ∷ []) ⟫ʷ
lem-sym23-at01102332 c4 = run b0
  where
  b0 : Chain (Bx1-0324 ∷ []) (Bx1-0234 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1324 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0324⟩ c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym23-at2332 c4) ▸
       at 0 2 (Bx1-0234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1234⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done

