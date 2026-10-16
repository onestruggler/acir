{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D003 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0001 ; wl0002 ; wl0003 ; wl0006 ; wl0007 ; wl0008 ; wl0011 ; wl0015 ; wl0017 ; wl0021 ; wl0027 ; wl0028 ; wl0031 ; wl0033 ; wl0034 ; wl0035 ; wl0050 ; wl0051 ; wl0056 ; wl0057 ; wl0058 ; wl0062 ; wl0065 ; wl0067 ; wl0068 ; wl0076 ; wl0084 ; wl0091 ; wl0103 ; wl0111 ; wl0113 ; wl0138 ; wl0152 ; wl0154 ; wl0155 ; wl0212 ; wl0247 ; wl0248 ; wl0249 ; wl0250 ; wl0257 ; wl0278 ; wl0279 ; wl0280 ; wl0281 ; wl0282 ; wl0283 ; wl0284 ; wl0285 ; wl0286 ; wl0287 ; wl0288 ; wl0289 ; wl0290 ; wl0291 ; wl0292 ; wl0293 ; wl0294 ; wl0295 ; wl0296 ; wl0297 ; wl0298 ; wl0299 ; wl0300 ; wl0301 ; wl0302 ; wl0303 ; wl0304 ; wl0305 ; wl0306 ; wl0307 ; wl0308 ; wl0309 ; wl0310 ; wl0311 ; wl0312 ; wl0313 ; wl0314 ; wl0315 ; wl0316 ; wl0317 ; wl0318 ; wl0319 ; wl0320 ; wl0321 ; wl0322 ; wl0323 ; wl0324 ; wp0034 ; wp0055 ; wp0059 ; wp0077 ; wp0079 ; wp0080 ; wp0081 ; wp0082 ; wp0083 ; wp0084 ; wp0085 ; wp0086 ; wp0087 ; wp0088 ; wp0089 ; wp0090 ; wp0091 ; wp0092 ; wp0093 ; wp0094 ; wp0095)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-CS12-beta ; lem-F0 ; lem-K0-pass-c ; lem-K0-pass-ci ; lem-T312-beta ; lem-beta-T ; lem-beta-T-at243243 ; lem-beta-inv-at0210243143 ; lem-c124-beta ; lem-sym12 ; lem-sym12-at0214203143 ; lem-sym12-at1221 ; lem-sym23 ; lem-sym23-at0214203143 ; lem-sym23-at0214213043 ; lem-sym23-at1221 ; lem-sym34 ; lem-sym34-at1221 ; lem-sym34-at3443)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-CS12-beta-at2332 ; lem-CS12-beta-at243243 ; lem-CSd12-beta-at243243 ; lem-CX23-beta-at0210243143 ; lem-CX23-beta-at02243043 ; lem-SB2 ; lem-SBsym ; lem-T312-beta-at02142140 ; lem-X1-beta ; lem-auto-BOX⟨0·1234⟩-∣-CCZ034 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ231 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0210243143 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ324-at2332 ; lem-auto-BOX⟨0·1234⟩-∣-CS14 ; lem-auto-BOX⟨0·1234⟩-∣-CS14-at0210243143 ; lem-auto-BOX⟨0·1234⟩-∣-CS21 ; lem-auto-BOX⟨0·1234⟩-∣-CS23 ; lem-auto-BOX⟨0·1234⟩-∣-CSd14 ; lem-auto-BOX⟨0·1234⟩-∣-CSd14-at0210243143 ; lem-auto-BOX⟨0·1234⟩-∣-TOFF012 ; lem-c124-beta-at2332 ; lem-sym12-at0210243143 ; lem-sym12-at0214213043 ; lem-sym12-at02243043 ; lem-sym12-at12213443 ; lem-sym12-at233442 ; lem-sym23-at021021 ; lem-sym23-at12213443 ; lem-sym23-at122331 ; lem-sym23-at12243143 ; lem-sym23-at2332 ; lem-sym23-at243243 ; lem-sym23-at3443 ; lem-sym34-at0214213043 ; lem-sym34-at02142140 ; lem-sym34-at12213443 ; lem-sym34-at122331 ; lem-sym34-at12233441 ; lem-sym34-at2332 ; lem-sym34-at233442)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-nat-1-BOX⟨0·2134⟩ ; lem-nat-1-BOX⟨0·2413⟩ ; lem-nat-1-CCZ023 ; lem-nat-1-CCZ034 ; lem-nat-2-BOX⟨0·1234⟩ ; lem-nat-2-BOX⟨0·1324⟩ ; lem-nat-3-BOX⟨0·1243⟩ ; lem-nat-3-BOX⟨0·1423⟩)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-1-BOX⟨0·1423⟩ ; lem-nat-1-CCZ013 ; lem-nat-2-BOX⟨0·3124⟩ ; lem-nat-2-CCZ124 ; lem-nat-2-CCZ134 ; lem-nat-3-BOX⟨0·1324⟩)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-0-BOX⟨1·4023⟩ ; lem-nat-0-CCZ034 ; lem-nat-0-CCZ134 ; lem-nat-1-BOX⟨2·4013⟩ ; lem-nat-2-TOFF413 ; lem-nat-3-BOX⟨0·4123⟩)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-0-BOX⟨0·4123⟩ ; lem-nat-1-BOX⟨0·1234⟩ ; lem-nat-1-BOX⟨1·4023⟩ ; lem-nat-2-BOX⟨0·2134⟩ ; lem-nat-3-BOX⟨0·3124⟩)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-0-BOX⟨0·1234⟩ ; lem-nat-0-BOX⟨0·1423⟩ ; lem-nat-0-BOX⟨1·0234⟩ ; lem-nat-0-BOX⟨1·0423⟩ ; lem-nat-1-BOX⟨1·0234⟩ ; lem-nat-1-BOX⟨1·0423⟩ ; lem-nat-1-BOX⟨2·0134⟩ ; lem-nat-1-BOX⟨2·0413⟩ ; lem-nat-2-BOX⟨2·0134⟩ ; lem-nat-2-BOX⟨3·0124⟩ ; lem-nat-3-BOX⟨0·1234⟩ ; lem-nat-3-CCZ123 ; lem-nat-3-CCZ124)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-0-BOX⟨0·1324⟩ ; lem-nat-1-BOX⟨0·1342⟩ ; lem-nat-1-BOX⟨0·2341⟩ ; lem-nat-1-BOX⟨1·0324⟩ ; lem-nat-1-CS01 ; lem-nat-1-CS02 ; lem-nat-2-BOX⟨0·1243⟩ ; lem-nat-2-BOX⟨0·1342⟩ ; lem-nat-2-BOX⟨0·3142⟩ ; lem-nat-2-CS12 ; lem-nat-2-CS13 ; lem-nat-3-CS13 ; lem-nat-3-CS14)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-0-BOX⟨0·1342⟩ ; lem-nat-0-CS04 ; lem-nat-0-CS14 ; lem-nat-0-SBOX⟨0·1·34·2⟩ ; lem-nat-0-SBOX⟨2·0·34·1⟩ ; lem-nat-1-CS04 ; lem-nat-1-SBOX⟨0·2·34·1⟩ ; lem-nat-1-SBOX⟨1·0·42·3⟩ ; lem-nat-1-SBOX⟨3·0·41·2⟩ ; lem-nat-2-BOX⟨0·1432⟩ ; lem-nat-2-SBOX⟨0·1·23·4⟩ ; lem-nat-2-SBOX⟨0·1·32·4⟩ ; lem-nat-2-SBOX⟨1·0·43·2⟩ ; lem-nat-2-SBOX⟨3·0·42·1⟩ ; lem-nat-2-TOFF014 ; lem-nat-3-CS23 ; lem-nat-3-CS24 ; lem-nat-3-SBOX⟨1·0·34·2⟩ ; lem-nat-3-SBOX⟨2·0·43·1⟩)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-nat-0-BOX⟨0·3142⟩ ; lem-nat-0-BOX⟨1·0324⟩ ; lem-nat-0-BOX⟨1·0342⟩ ; lem-nat-0-BOX⟨1·3042⟩ ; lem-nat-0-BOX⟨4·0231⟩ ; lem-nat-0-SBOX⟨0·1·23·4⟩ ; lem-nat-0-SBOX⟨1·2·34·0⟩ ; lem-nat-0-SBOX⟨4·0·23·1⟩ ; lem-nat-1-BOX⟨1·0342⟩ ; lem-nat-1-BOX⟨1·3042⟩ ; lem-nat-1-BOX⟨2·0314⟩ ; lem-nat-1-BOX⟨2·0341⟩ ; lem-nat-1-BOX⟨2·3041⟩ ; lem-nat-1-SBOX⟨1·0·32·4⟩ ; lem-nat-1-SBOX⟨2·1·34·0⟩ ; lem-nat-1-SBOX⟨4·0·31·2⟩ ; lem-nat-2-SBOX⟨1·0·23·4⟩ ; lem-nat-2-SBOX⟨4·0·32·1⟩ ; lem-nat-3-BOX⟨3·0124⟩ ; lem-nat-3-BOX⟨4·0123⟩ ; lem-nat-3-SBOX⟨2·0·31·4⟩ ; lem-nat-3-SBOX⟨3·0·41·2⟩ ; lem-nat-3-TOFF412)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-0-BOX⟨4·1230⟩ ; lem-nat-0-SBOX⟨1·0·32·4⟩ ; lem-nat-1-BOX⟨4·0132⟩ ; lem-nat-1-BOX⟨4·0231⟩ ; lem-nat-1-SBOX⟨2·0·13·4⟩ ; lem-nat-2-BOX⟨4·0123⟩ ; lem-nat-2-BOX⟨4·0132⟩ ; lem-nat-3-SBOX⟨2·0·14·3⟩)
-- auto BOX(0;1234) | CCZ324 @243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ324-at243243 : Ws → ⟪ (Bx0-1423 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Bx0-1423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ324-at243243 c4 = run b0
  where
  b0 : Chain (Bx0-1423 ∷ CCZ234 ∷ []) (CCZ234 ∷ Bx0-1423 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ (lit c4)) ▸
       at 2 2 (CCZ234 ∷ Sw34 ∷ []) (sym (wl0155 (lit c4))) ▸
       at 1 2 (CCZ234 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ324-at2332 c4) ▸
       at 0 2 (CCZ234 ∷ Sw34 ∷ []) (sym (wl0155 (lit c4))) ▸
       at 1 2 (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto BOX(0;1234) | CCZ324 @0110243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ324-at0110243243 : Ws → ⟪ (Bx1-0423 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Bx1-0423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ324-at0110243243 c4 = run b0
  where
  b0 : Chain (Bx1-0423 ∷ CCZ234 ∷ []) (CCZ234 ∷ Bx1-0423 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4)) ▸
       at 2 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 1 2 (CCZ234 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ324-at243243 c4) ▸
       at 0 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 1 2 (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto BOX(0;1234) | CCZ324 @0210243143: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ324-at0210243143 : Ws → ⟪ (Bx2-0413 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Bx2-0413 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ324-at0210243143 c4 = run b0
  where
  b0 : Chain (Bx2-0413 ∷ CCZ134 ∷ []) (CCZ134 ∷ Bx2-0413 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4)) ▸
       at 2 2 (CCZ234 ∷ Sw12 ∷ []) (sym (wl0084 (lit c4))) ▸
       at 1 2 (CCZ234 ∷ Bx1-0423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ324-at0110243243 c4) ▸
       at 0 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0034 (lit c4))) ▸
       at 1 2 (Bx2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0423⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto BOX(0;1234) | CS23 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS23-at2332 : Ws → ⟪ (Bx0-1324 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS23-at2332 c4 = run b0
  where
  b0 : Chain (Bx0-1324 ∷ CS23 ∷ []) (CS23 ∷ Bx0-1324 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ (lit c4)) ▸
       at 2 2 (CS23 ∷ Sw23 ∷ []) (sym (wl0152 (lit c4))) ▸
       at 1 2 (CS23 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS23 c4) ▸
       at 0 2 (CS23 ∷ Sw23 ∷ []) (sym (wl0152 (lit c4))) ▸
       at 1 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto BOX(0;1234) | CS23 @243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS23-at243243 : Ws → ⟪ (Bx0-1423 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ Bx0-1423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS23-at243243 c4 = run b0
  where
  b0 : Chain (Bx0-1423 ∷ CS24 ∷ []) (CS24 ∷ Bx0-1423 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ (lit c4)) ▸
       at 2 2 (CS23 ∷ Sw34 ∷ []) (lem-nat-3-CS24 (lit c4)) ▸
       at 1 2 (CS23 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS23-at2332 c4) ▸
       at 0 2 (CS24 ∷ Sw34 ∷ []) (lem-nat-3-CS23 (lit c4)) ▸
       at 1 2 (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto BOX(0;1234) | CS23 @0110243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS23-at0110243243 : Ws → ⟪ (Bx1-0423 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ Bx1-0423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS23-at0110243243 c4 = run b0
  where
  b0 : Chain (Bx1-0423 ∷ CS24 ∷ []) (CS24 ∷ Bx1-0423 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4)) ▸
       at 2 2 (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑)) ▸
       at 1 2 (CS24 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS23-at243243 c4) ▸
       at 0 2 (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑)) ▸
       at 1 2 (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto BOX(0;1234) | CS23 @0210243143: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS23-at0210243143 : Ws → ⟪ (Bx2-0413 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ Bx2-0413 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS23-at0210243143 c4 = run b0
  where
  b0 : Chain (Bx2-0413 ∷ CS14 ∷ []) (CS14 ∷ Bx2-0413 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4)) ▸
       at 2 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0008 (lit c4))) ▸
       at 1 2 (CS24 ∷ Bx1-0423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS23-at0110243243 c4) ▸
       at 0 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0017 (lit c4))) ▸
       at 1 2 (Bx2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0423⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- F1 X-CS0 [nf of rhs]: 36 steps
lem-F1-X-CS0-nf-of-rhs : Ws → ⟪ (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CCZ014 ∷ CCZ014 ∷ CS03 ∷ Toff314 ∷ CCZ014 ∷ CS03⁻ ∷ CX40 ∷ CCZ134 ∷ CS14 ∷ Bx2-0413 ∷ []) ⟫ʷ
lem-F1-X-CS0-nf-of-rhs c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (run b4))))
  where
  b0 : Chain (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CS14 ∷ []) (CCZ014 ∷ Toff314 ∷ Toff314 ∷ Bx2-4103 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CX40 ∷ CS14 ∷ [])
  b0 = at 0 2 (CCZ014 ∷ []) (lem-SB2 c4) ▸
       at 2 5 (CX40 ∷ []) (wp0079 c4) ▸
       at 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 1 (CS03 ∷ []) (refl) ▸
       at 5 1 (CS03⁻ ∷ []) (refl) ▸
       at 1 0 (Toff314 ∷ Toff314 ∷ []) (sym (wl0248 (lit c4))) ▸
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
       at 4 0 (Toff314 ∷ Toff314 ∷ []) (sym (wl0248 (lit c4))) ▸ done

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
       at 7 0 (CX40 ∷ CX40 ∷ []) (sym (wp0080 c4)) ▸
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
       at 0 2 (Toff314 ∷ CCZ014 ∷ []) (wp0077 c4) ▸ done


-- F1 X-CS0: 26 steps
lem-F1-X-CS0 : Ws → ⟪ (CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CS14 ∷ []) ⟫ʷ
lem-F1-X-CS0 c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb2-0-41-3 ∷ []) (CX40 ∷ Toff314 ∷ Toff314 ∷ Bx2-4130 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b0 = at 0 5 (CX40 ∷ []) (wp0079 c4) ▸
       at 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 1 (CS03 ∷ []) (refl) ▸
       at 5 1 (CS03⁻ ∷ []) (refl) ▸
       at 1 0 (Toff314 ∷ Toff314 ∷ []) (sym (wl0248 (lit c4))) ▸
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
       at 4 0 (Toff314 ∷ Toff314 ∷ []) (sym (wl0248 (lit c4))) ▸
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
  b3 = at 0 7 (Toff314 ∷ CCZ014 ∷ CCZ014 ∷ CS03 ∷ Toff314 ∷ CCZ014 ∷ CS03⁻ ∷ CX40 ∷ CCZ134 ∷ CS14 ∷ []) (wp0081 c4) ▸
       at 0 11 (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CS14 ∷ []) (sym (lem-F1-X-CS0-nf-of-rhs c4)) ▸ done


-- auto BOX(0;1234) | CCZ124: 1 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ124 : Ws → ⟪ (Bx0-1234 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ124 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ CCZ124 ∷ []) (CCZ124 ∷ Bx0-1234 ∷ [])
  b0 = at 0 2 (CCZ124 ∷ Bx0-1234 ∷ []) (sym (lem-c124-beta c4)) ▸ done


-- auto BOX(0;1234) | CCZ124 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at2332 : Ws → ⟪ (Bx0-1324 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at2332 c4 = run b0
  where
  b0 : Chain (Bx0-1324 ∷ CCZ134 ∷ []) (CCZ134 ∷ Bx0-1324 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ (lit c4)) ▸
       at 2 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 (lit c4)) ▸
       at 1 2 (CCZ124 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124 c4) ▸
       at 0 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 (lit c4)) ▸
       at 1 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto BOX(0;1234) | CCZ124 @243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at243243 : Ws → ⟪ (Bx0-1423 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Bx0-1423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at243243 c4 = run b0
  where
  b0 : Chain (Bx0-1423 ∷ CCZ134 ∷ []) (CCZ134 ∷ Bx0-1423 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ (lit c4)) ▸
       at 2 2 (CCZ134 ∷ Sw34 ∷ []) (sym (wl0154 (lit c4))) ▸
       at 1 2 (CCZ134 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at2332 c4) ▸
       at 0 2 (CCZ134 ∷ Sw34 ∷ []) (sym (wl0154 (lit c4))) ▸
       at 1 2 (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto BOX(0;1234) | CCZ124 @0110243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at0110243243 : Ws → ⟪ (Bx1-0423 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Bx1-0423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at0110243243 c4 = run b0
  where
  b0 : Chain (Bx1-0423 ∷ CCZ034 ∷ []) (CCZ034 ∷ Bx1-0423 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4)) ▸
       at 2 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 (lit c4)) ▸
       at 1 2 (CCZ134 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at243243 c4) ▸
       at 0 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 (lit c4)) ▸
       at 1 2 (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto BOX(0;1234) | CCZ124 @0210243143: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at0210243143 : Ws → ⟪ (Bx2-0413 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Bx2-0413 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at0210243143 c4 = run b0
  where
  b0 : Chain (Bx2-0413 ∷ CCZ034 ∷ []) (CCZ034 ∷ Bx2-0413 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4)) ▸
       at 2 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 (lit c4)) ▸
       at 1 2 (CCZ034 ∷ Bx1-0423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at0110243243 c4) ▸
       at 0 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 (lit c4)) ▸
       at 1 2 (Bx2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0423⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto BOX(0;1234) | CS21 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS21-at2332 : Ws → ⟪ (Bx0-1324 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS21-at2332 c4 = run b0
  where
  b0 : Chain (Bx0-1324 ∷ CS13 ∷ []) (CS13 ∷ Bx0-1324 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ (lit c4)) ▸
       at 2 2 (CS12 ∷ Sw23 ∷ []) (lem-nat-2-CS13 (lit c4)) ▸
       at 1 2 (CS12 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS21 c4) ▸
       at 0 2 (CS13 ∷ Sw23 ∷ []) (lem-nat-2-CS12 (lit c4)) ▸
       at 1 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto BOX(0;1234) | CS21 @243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS21-at243243 : Ws → ⟪ (Bx0-1423 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ Bx0-1423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS21-at243243 c4 = run b0
  where
  b0 : Chain (Bx0-1423 ∷ CS14 ∷ []) (CS14 ∷ Bx0-1423 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ (lit c4)) ▸
       at 2 2 (CS13 ∷ Sw34 ∷ []) (lem-nat-3-CS14 (lit c4)) ▸
       at 1 2 (CS13 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS21-at2332 c4) ▸
       at 0 2 (CS14 ∷ Sw34 ∷ []) (lem-nat-3-CS13 (lit c4)) ▸
       at 1 2 (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto BOX(0;1234) | CS21 @0110243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS21-at0110243243 : Ws → ⟪ (Bx1-0423 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ Bx1-0423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS21-at0110243243 c4 = run b0
  where
  b0 : Chain (Bx1-0423 ∷ CS04 ∷ []) (CS04 ∷ Bx1-0423 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4)) ▸
       at 2 2 (CS14 ∷ Sw01 ∷ []) (lem-nat-0-CS04 (lit c4)) ▸
       at 1 2 (CS14 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS21-at243243 c4) ▸
       at 0 2 (CS04 ∷ Sw01 ∷ []) (lem-nat-0-CS14 (lit c4)) ▸
       at 1 2 (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto BOX(0;1234) | CS21 @0210243143: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS21-at0210243143 : Ws → ⟪ (Bx2-0413 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ Bx2-0413 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS21-at0210243143 c4 = run b0
  where
  b0 : Chain (Bx2-0413 ∷ CS04 ∷ []) (CS04 ∷ Bx2-0413 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4)) ▸
       at 2 2 (CS04 ∷ Sw12 ∷ []) (lem-nat-1-CS04 (lit c4)) ▸
       at 1 2 (CS04 ∷ Bx1-0423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS21-at0110243243 c4) ▸
       at 0 2 (CS04 ∷ Sw12 ∷ []) (lem-nat-1-CS04 (lit c4)) ▸
       at 1 2 (Bx2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0423⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- F1 X-CS1 [nf of rhs]: 32 steps
lem-F1-X-CS1-nf-of-rhs : Ws → ⟪ (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CCZ014 ∷ CCZ014 ∷ CS03 ∷ Toff314 ∷ CX41 ∷ CZ04 ∷ CCZ014 ∷ CS03⁻ ∷ CCZ034 ∷ CS04 ∷ Bx2-0413 ∷ []) ⟫ʷ
lem-F1-X-CS1-nf-of-rhs c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS04 ∷ []) (CCZ014 ∷ Toff314 ∷ Toff314 ∷ Bx2-4103 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CX41 ∷ CS04 ∷ [])
  b0 = at 0 2 (CCZ014 ∷ []) (lem-SB2 c4) ▸
       at 2 5 (CX41 ∷ []) (wl0278 (lit c4)) ▸
       at 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 1 (CS03 ∷ []) (refl) ▸
       at 5 1 (CS03⁻ ∷ []) (refl) ▸
       at 1 0 (Toff314 ∷ Toff314 ∷ []) (sym (wl0248 (lit c4))) ▸
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
       at 4 0 (Toff314 ∷ Toff314 ∷ []) (sym (wl0248 (lit c4))) ▸ done

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
       at 7 0 (CX41 ∷ CX41 ∷ []) (sym (wl0279 (lit c4))) ▸
       at 8 3 (Bx2-0413 ∷ CCZ034 ∷ []) (lem-CX23-beta-at0210243143 c4) ▸
       at 8 2 (CCZ034 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at0210243143 c4) ▸
       at 9 2 (CS04 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS21-at0210243143 c4) ▸
       at 6 2 (CX41 ∷ CS03⁻ ∷ []) (wp0082 c4) ▸
       at 5 2 (CX41 ∷ CZ04 ∷ CCZ014 ∷ []) (wp0083 c4) ▸
       at 0 2 (Toff314 ∷ CCZ014 ∷ []) (wp0077 c4) ▸ done


-- F1 X-CS1: 26 steps
lem-F1-X-CS1 : Ws → ⟪ (CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS04 ∷ []) ⟫ʷ
lem-F1-X-CS1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ []) (CX41 ∷ Toff314 ∷ Toff314 ∷ Bx2-4130 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b0 = at 0 5 (CX41 ∷ []) (wl0278 (lit c4)) ▸
       at 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 1 (CS03 ∷ []) (refl) ▸
       at 5 1 (CS03⁻ ∷ []) (refl) ▸
       at 1 0 (Toff314 ∷ Toff314 ∷ []) (sym (wl0248 (lit c4))) ▸
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
       at 4 0 (Toff314 ∷ Toff314 ∷ []) (sym (wl0248 (lit c4))) ▸
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
  b3 = at 0 7 (Toff314 ∷ CCZ014 ∷ CCZ014 ∷ CS03 ∷ Toff314 ∷ CX41 ∷ CZ04 ∷ CCZ014 ∷ CS03⁻ ∷ CCZ034 ∷ CS04 ∷ []) (wp0084 c4) ▸
       at 0 12 (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS04 ∷ []) (sym (lem-F1-X-CS1-nf-of-rhs c4)) ▸ done


-- auto BOX(0;1234) | CS13: 3 steps
lem-auto-BOX⟨0·1234⟩-∣-CS13 : Ws → ⟪ (Bx0-1234 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS13 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ CS13 ∷ []) (CS13 ∷ Bx0-1234 ∷ [])
  b0 = at 0 1 (Bx0-1324 ∷ []) (lem-sym23 c4) ▸
       at 0 2 (CS13 ∷ Bx0-1324 ∷ []) (sym (lem-CS12-beta-at2332 c4)) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym23-at2332 c4) ▸ done


-- auto BOX(0;1234) | CCZ134: 3 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ134 : Ws → ⟪ (Bx0-1234 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ134 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ CCZ134 ∷ []) (CCZ134 ∷ Bx0-1234 ∷ [])
  b0 = at 0 1 (Bx0-1324 ∷ []) (lem-sym23 c4) ▸
       at 0 2 (CCZ134 ∷ Bx0-1324 ∷ []) (sym (lem-c124-beta-at2332 c4)) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym23-at2332 c4) ▸ done


-- X1-beta @1221: 8 steps
lem-X1-beta-at1221 : Ws → ⟪ (X2 ∷ Bx0-2134 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Bx0-2134 ∷ []) ⟫ʷ
lem-X1-beta-at1221 c4 = run b0
  where
  b0 : Chain (X2 ∷ Bx0-2134 ∷ X2 ∷ []) (CCZ134 ∷ Bx0-2134 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (X1 ∷ Sw12 ∷ []) (wl0280 (lit c4)) ▸
       at 2 2 (Bx0-1234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2134⟩ (lit c4)) ▸
       at 3 2 (X1 ∷ Sw12 ∷ []) (wl0280 (lit c4)) ▸
       at 1 3 (CCZ234 ∷ Bx0-1234 ∷ []) (lem-X1-beta c4) ▸
       at 0 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0034 (lit c4))) ▸
       at 1 2 (Bx0-2134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1234⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- X1-beta @132132: 8 steps
lem-X1-beta-at132132 : Ws → ⟪ (X3 ∷ Bx0-3124 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Bx0-3124 ∷ []) ⟫ʷ
lem-X1-beta-at132132 c4 = run b0
  where
  b0 : Chain (X3 ∷ Bx0-3124 ∷ X3 ∷ []) (CCZ124 ∷ Bx0-3124 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (X2 ∷ Sw23 ∷ []) (wl0281 (lit c4)) ▸
       at 2 2 (Bx0-2134 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3124⟩ (lit c4)) ▸
       at 3 2 (X2 ∷ Sw23 ∷ []) (wl0281 (lit c4)) ▸
       at 1 3 (CCZ134 ∷ Bx0-2134 ∷ []) (lem-X1-beta-at1221 c4) ▸
       at 0 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 (lit c4)) ▸
       at 1 2 (Bx0-3124 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·2134⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- X1-beta @14213243: 8 steps
lem-X1-beta-at14213243 : Ws → ⟪ (X4 ∷ Bx0-4123 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Bx0-4123 ∷ []) ⟫ʷ
lem-X1-beta-at14213243 c4 = run b0
  where
  b0 : Chain (X4 ∷ Bx0-4123 ∷ X4 ∷ []) (CCZ123 ∷ Bx0-4123 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (X3 ∷ Sw34 ∷ []) (wl0282 (lit c4)) ▸
       at 2 2 (Bx0-3124 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·4123⟩ (lit c4)) ▸
       at 3 2 (X3 ∷ Sw34 ∷ []) (wl0282 (lit c4)) ▸
       at 1 3 (CCZ124 ∷ Bx0-3124 ∷ []) (lem-X1-beta-at132132 c4) ▸
       at 0 2 (CCZ123 ∷ Sw34 ∷ []) (lem-nat-3-CCZ124 (lit c4)) ▸
       at 1 2 (Bx0-4123 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·3124⟩ (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- X1-beta @0114203243: 8 steps
lem-X1-beta-at0114203243 : Ws → ⟪ (X4 ∷ Bx1-4023 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ Bx1-4023 ∷ []) ⟫ʷ
lem-X1-beta-at0114203243 c4 = run b0
  where
  b0 : Chain (X4 ∷ Bx1-4023 ∷ X4 ∷ []) (CCZ023 ∷ Bx1-4023 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (X4 ∷ Sw01 ∷ []) (c₂ (Swap) (X ↑ ↑)) ▸
       at 2 2 (Bx0-4123 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·4023⟩ (lit c4)) ▸
       at 3 2 (X4 ∷ Sw01 ∷ []) (c₂ (Swap) (X ↑ ↑)) ▸
       at 1 3 (CCZ123 ∷ Bx0-4123 ∷ []) (lem-X1-beta-at14213243 c4) ▸
       at 0 2 (CCZ023 ∷ Sw01 ∷ []) (sym (wl0003 (lit c4))) ▸
       at 1 2 (Bx1-4023 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·4123⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- X1-beta @0214203143: 8 steps
lem-X1-beta-at0214203143 : Ws → ⟪ (X4 ∷ Bx2-4013 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ Bx2-4013 ∷ []) ⟫ʷ
lem-X1-beta-at0214203143 c4 = run b0
  where
  b0 : Chain (X4 ∷ Bx2-4013 ∷ X4 ∷ []) (CCZ013 ∷ Bx2-4013 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (X4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (X ↑)) ▸
       at 2 2 (Bx1-4023 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·4013⟩ (lit c4)) ▸
       at 3 2 (X4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (X ↑)) ▸
       at 1 3 (CCZ023 ∷ Bx1-4023 ∷ []) (lem-X1-beta-at0114203243 c4) ▸
       at 0 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 (lit c4)) ▸
       at 1 2 (Bx2-4013 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·4023⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto BOX(0;1234) | CS13 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS13-at2332 : Ws → ⟪ (Bx0-1324 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS13-at2332 c4 = run b0
  where
  b0 : Chain (Bx0-1324 ∷ CS12 ∷ []) (CS12 ∷ Bx0-1324 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ (lit c4)) ▸
       at 2 2 (CS13 ∷ Sw23 ∷ []) (lem-nat-2-CS12 (lit c4)) ▸
       at 1 2 (CS13 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS13 c4) ▸
       at 0 2 (CS12 ∷ Sw23 ∷ []) (lem-nat-2-CS13 (lit c4)) ▸
       at 1 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto BOX(0;1234) | CS13 @243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS13-at243243 : Ws → ⟪ (Bx0-1423 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ Bx0-1423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS13-at243243 c4 = run b0
  where
  b0 : Chain (Bx0-1423 ∷ CS12 ∷ []) (CS12 ∷ Bx0-1423 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ (lit c4)) ▸
       at 2 2 (CS12 ∷ Sw34 ∷ []) (sym (c₃ (CS ↑) (Swap))) ▸
       at 1 2 (CS12 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS13-at2332 c4) ▸
       at 0 2 (CS12 ∷ Sw34 ∷ []) (sym (c₃ (CS ↑) (Swap))) ▸
       at 1 2 (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto BOX(0;1234) | CS13 @0110243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS13-at0110243243 : Ws → ⟪ (Bx1-0423 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ Bx1-0423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS13-at0110243243 c4 = run b0
  where
  b0 : Chain (Bx1-0423 ∷ CS02 ∷ []) (CS02 ∷ Bx1-0423 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4)) ▸
       at 2 2 (CS12 ∷ Sw01 ∷ []) (sym (wl0138 (lit c4))) ▸
       at 1 2 (CS12 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS13-at243243 c4) ▸
       at 0 2 (CS02 ∷ Sw01 ∷ []) (sym (wl0035 (lit c4))) ▸
       at 1 2 (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto BOX(0;1234) | CS13 @0210243143: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS13-at0210243143 : Ws → ⟪ (Bx2-0413 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ Bx2-0413 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS13-at0210243143 c4 = run b0
  where
  b0 : Chain (Bx2-0413 ∷ CS01 ∷ []) (CS01 ∷ Bx2-0413 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4)) ▸
       at 2 2 (CS02 ∷ Sw12 ∷ []) (lem-nat-1-CS01 (lit c4)) ▸
       at 1 2 (CS02 ∷ Bx1-0423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS13-at0110243243 c4) ▸
       at 0 2 (CS01 ∷ Sw12 ∷ []) (lem-nat-1-CS02 (lit c4)) ▸
       at 1 2 (Bx2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0423⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto BOX(0;1234) | CCZ134 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at2332 : Ws → ⟪ (Bx0-1324 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at2332 c4 = run b0
  where
  b0 : Chain (Bx0-1324 ∷ CCZ124 ∷ []) (CCZ124 ∷ Bx0-1324 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ (lit c4)) ▸
       at 2 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 (lit c4)) ▸
       at 1 2 (CCZ134 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ134 c4) ▸
       at 0 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 (lit c4)) ▸
       at 1 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto BOX(0;1234) | CCZ134 @243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at243243 : Ws → ⟪ (Bx0-1423 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Bx0-1423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at243243 c4 = run b0
  where
  b0 : Chain (Bx0-1423 ∷ CCZ123 ∷ []) (CCZ123 ∷ Bx0-1423 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ (lit c4)) ▸
       at 2 2 (CCZ124 ∷ Sw34 ∷ []) (lem-nat-3-CCZ123 (lit c4)) ▸
       at 1 2 (CCZ124 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at2332 c4) ▸
       at 0 2 (CCZ123 ∷ Sw34 ∷ []) (lem-nat-3-CCZ124 (lit c4)) ▸
       at 1 2 (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto BOX(0;1234) | CCZ134 @0110243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at0110243243 : Ws → ⟪ (Bx1-0423 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ Bx1-0423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at0110243243 c4 = run b0
  where
  b0 : Chain (Bx1-0423 ∷ CCZ023 ∷ []) (CCZ023 ∷ Bx1-0423 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4)) ▸
       at 2 2 (CCZ123 ∷ Sw01 ∷ []) (sym (wl0103 (lit c4))) ▸
       at 1 2 (CCZ123 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at243243 c4) ▸
       at 0 2 (CCZ023 ∷ Sw01 ∷ []) (sym (wl0003 (lit c4))) ▸
       at 1 2 (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto BOX(0;1234) | CCZ134 @0210243143: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at0210243143 : Ws → ⟪ (Bx2-0413 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ Bx2-0413 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at0210243143 c4 = run b0
  where
  b0 : Chain (Bx2-0413 ∷ CCZ013 ∷ []) (CCZ013 ∷ Bx2-0413 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4)) ▸
       at 2 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 (lit c4)) ▸
       at 1 2 (CCZ023 ∷ Bx1-0423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at0110243243 c4) ▸
       at 0 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 (lit c4)) ▸
       at 1 2 (Bx2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0423⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- F5 CS01: 38 steps
lem-F5-CS01 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ []) ⟫ʷ
lem-F5-CS01 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (run b4))))
  where
  b0 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (CCZ013 ∷ Bx2-0413 ∷ X4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b0 = at 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 1 (CS03 ∷ []) (refl) ▸
       at 5 1 (CS03⁻ ∷ []) (refl) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 1 1 (Bx2-4013 ∷ []) (lem-sym12-at0210243143 c4) ▸
       at 0 3 (CCZ013 ∷ Bx2-4013 ∷ []) (lem-X1-beta-at0214203143 c4) ▸
       at 1 1 (Bx2-0413 ∷ []) (lem-sym12-at0214203143 c4) ▸
       at 8 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ013 ∷ Bx2-0413 ∷ X4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (CCZ013 ∷ CS01 ∷ CCZ013 ∷ CS03 ∷ Toff314 ∷ Toff314 ∷ Bx2-4013 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b1 = at 10 1 (CS03 ∷ []) (refl) ▸
       at 12 1 (CS03⁻ ∷ []) (refl) ▸
       at 2 6 (CS01 ∷ CCZ013 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ []) (sym (wp0085 c4)) ▸
       at 1 2 (CS01 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS13-at0210243143 c4) ▸
       at 2 2 (CCZ013 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at0210243143 c4) ▸
       at 3 2 (CS03 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS14-at0210243143 c4) ▸
       at 4 0 (Toff314 ∷ Toff314 ∷ []) (sym (wl0248 (lit c4))) ▸
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
  b3 = at 7 0 (Toff314 ∷ Toff314 ∷ []) (sym (wl0248 (lit c4))) ▸
       at 9 1 (Bx2-4013 ∷ []) (lem-sym12-at0210243143 c4) ▸
       at 9 1 (Bx2-4103 ∷ []) (lem-sym23-at0214203143 c4) ▸
       at 9 1 (Bx2-4130 ∷ []) (lem-sym34-at0214213043 c4) ▸
       at 8 3 (Bx2-4130 ∷ CCZ014 ∷ []) (lem-T312-beta-at02142140 c4) ▸
       at 8 1 (Bx2-4103 ∷ []) (lem-sym34-at02142140 c4) ▸
       at 8 1 (Bx2-4013 ∷ []) (lem-sym23-at0214213043 c4) ▸
       at 8 1 (Bx2-0413 ∷ []) (lem-sym12-at0214203143 c4) ▸ done

  b4 : Chain (CCZ013 ∷ CS01 ∷ CCZ013 ∷ CS03 ∷ Toff314 ∷ CCZ014 ∷ CS03⁻ ∷ Toff314 ∷ Bx2-0413 ∷ CCZ014 ∷ Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (CS01 ∷ [])
  b4 = at 8 2 (CCZ014 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0210243143 c4) ▸
       at 1 5 (CCZ014 ∷ CS01 ∷ CCZ013 ∷ CS03 ∷ Toff314 ∷ []) (sym (wp0086 c4)) ▸
       at 2 7 (CCZ014 ∷ CS01 ∷ CCZ013 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ []) (sym (wp0087 c4)) ▸
       at 1 2 [] (wp0055 c4) ▸
       at 7 2 [] (lem-beta-inv-at0210243143 c4) ▸
       at 0 11 (CS01 ∷ []) (wp0088 c4) ▸ done


-- beta-T @2442: 8 steps
lem-beta-T-at2442 : Ws → ⟪ (Bx0-1432 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) ⟫ʷ
lem-beta-T-at2442 c4 = run b0
  where
  b0 : Chain (Bx0-1432 ∷ []) (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx0-1423 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1432⟩ (lit c4)) ▸
       at 1 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-beta-T-at243243 c4) ▸
       at 0 2 (Toff014 ∷ Sw23 ∷ []) (lem-nat-2-TOFF014 (lit c4)) ▸
       at 1 2 (CCZ023 ∷ Sw23 ∷ []) (sym (wl0065 (lit c4))) ▸
       at 2 2 (Toff014 ∷ Sw23 ∷ []) (lem-nat-2-TOFF014 (lit c4)) ▸
       at 3 2 (CCZ023 ∷ Sw23 ∷ []) (sym (wl0065 (lit c4))) ▸
       at 4 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOXd(0;1;2;3) | BOX(0;1432): 14 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·1432⟩ : Ws → ⟪ (Sb⁻0-1-2-3 ∷ Bx0-1432 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1432 ∷ Sb⁻0-1-2-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·1432⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb⁻0-1-2-3 ∷ Bx0-1432 ∷ []) (Toff014 ∷ CCZ023 ∷ CS12⁻ ∷ Toff014 ∷ CCZ023 ∷ [])
  b0 = at 1 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-beta-T-at2442 c4) ▸
       at 0 1 (CS12⁻ ∷ []) (refl) ▸
       at 0 2 (Toff014 ∷ CS12⁻ ∷ []) (wp0089 c4) ▸
       at 1 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 1 1 (CS12⁻ ∷ []) (refl) ▸
       at 1 2 (CCZ023 ∷ CS12⁻ ∷ []) (sym (wl0284 (lit c4))) ▸
       at 2 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 2 1 (CS12⁻ ∷ []) (refl) ▸ done

  b1 : Chain (Toff014 ∷ CCZ023 ∷ CS12⁻ ∷ Toff014 ∷ CCZ023 ∷ []) (Bx0-1432 ∷ Sb⁻0-1-2-3 ∷ [])
  b1 = at 2 2 (Toff014 ∷ CS12⁻ ∷ []) (wp0089 c4) ▸
       at 3 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 3 1 (CS12⁻ ∷ []) (refl) ▸
       at 3 2 (CCZ023 ∷ CS12⁻ ∷ []) (sym (wl0284 (lit c4))) ▸
       at 4 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 0 4 (Bx0-1432 ∷ []) (sym (lem-beta-T-at2442 c4)) ▸ done


-- auto SBOXd(0;1;2;3) | SBOX(0;1;43;2): 13 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩ : Ws → ⟪ (Sb⁻0-1-2-3 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-43-2 ∷ Sb⁻0-1-2-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb⁻0-1-2-3 ∷ Sb0-1-43-2 ∷ []) (Bx0-1432 ∷ Toff234 ∷ Sb0-1-2-3 ∷ Toff234 ∷ CS12⁻ ∷ Sb⁻0-1-2-3 ∷ [])
  b0 = at 1 1 (Bx0-1432 ∷ Toff234 ∷ Sb0-1-2-3 ∷ Toff234 ∷ Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 0 2 (Bx0-1432 ∷ Sb⁻0-1-2-3 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨0·1432⟩ c4) ▸
       at 1 1 (CS12⁻ ∷ []) (refl) ▸
       at 3 1 (CS12 ∷ []) (refl) ▸
       at 1 4 (Toff234 ∷ CS12 ∷ Toff234 ∷ CS12⁻ ∷ []) (wl0285 (lit c4)) ▸
       at 2 1 (Sb0-1-2-3 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 4 1 (CS12⁻ ∷ []) (refl) ▸ done

  b1 : Chain (Bx0-1432 ∷ Toff234 ∷ Sb0-1-2-3 ∷ Toff234 ∷ CS12⁻ ∷ Sb⁻0-1-2-3 ∷ []) (Sb0-1-43-2 ∷ Sb⁻0-1-2-3 ∷ [])
  b1 = at 5 1 (CS12⁻ ∷ []) (refl) ▸
       at 4 2 (CS12⁻ ∷ CS12⁻ ∷ []) (wl0286 (lit c4)) ▸
       at 4 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 5 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 0 5 (Sb0-1-43-2 ∷ []) (refl) ▸ done


-- auto Kd0 | BOX(0;1234): 1 steps
lem-auto-Kd0-∣-BOX⟨0·1234⟩ : Ws → ⟪ (K0⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ K0⁻ ∷ []) ⟫ʷ
lem-auto-Kd0-∣-BOX⟨0·1234⟩ c4 = run b0
  where
  b0 : Chain (K0⁻ ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ K0⁻ ∷ [])
  b0 = at 0 2 (Bx0-1234 ∷ K0⁻ ∷ []) (lem-K0-pass-ci c4) ▸ done


-- F0 @1221: 5 steps
lem-F0-at1221 : Ws → ⟪ (Sb1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-42-1 ∷ []) ⟫ʷ
lem-F0-at1221 c4 = run b0
  where
  b0 : Chain (Sb1-0-42-3 ∷ []) (Sb3-0-42-1 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 1 1 (Sb3-0-41-2 ∷ []) (lem-F0 c4) ▸
       at 0 2 (Sb3-0-42-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·41·2⟩ (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- F0 @132132: 5 steps
lem-F0-at132132 : Ws → ⟪ (Sb1-0-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-43-1 ∷ []) ⟫ʷ
lem-F0-at132132 c4 = run b0
  where
  b0 : Chain (Sb1-0-43-2 ∷ []) (Sb2-0-43-1 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·43·2⟩ (lit c4)) ▸
       at 1 1 (Sb3-0-42-1 ∷ []) (lem-F0-at1221 c4) ▸
       at 0 2 (Sb2-0-43-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·0·42·1⟩ (lit c4)) ▸
       at 1 2 [] (wl0006 (lit c4)) ▸ done


-- F0 @14213243: 5 steps
lem-F0-at14213243 : Ws → ⟪ (Sb1-0-34-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-34-1 ∷ []) ⟫ʷ
lem-F0-at14213243 c4 = run b0
  where
  b0 : Chain (Sb1-0-34-2 ∷ []) (Sb2-0-34-1 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Sb1-0-43-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨1·0·34·2⟩ (lit c4)) ▸
       at 1 1 (Sb2-0-43-1 ∷ []) (lem-F0-at132132 c4) ▸
       at 0 2 (Sb2-0-34-1 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨2·0·43·1⟩ (lit c4)) ▸
       at 1 2 [] (wl0007 (lit c4)) ▸ done


-- F0 @0114203243: 5 steps
lem-F0-at0114203243 : Ws → ⟪ (Sb0-1-34-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-1-34-0 ∷ []) ⟫ʷ
lem-F0-at0114203243 c4 = run b0
  where
  b0 : Chain (Sb0-1-34-2 ∷ []) (Sb2-1-34-0 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Sb1-0-34-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·34·2⟩ (lit c4)) ▸
       at 1 1 (Sb2-0-34-1 ∷ []) (lem-F0-at14213243 c4) ▸
       at 0 2 (Sb2-1-34-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·0·34·1⟩ (lit c4)) ▸
       at 1 2 [] (wl0002 (lit c4)) ▸ done


-- F0 @0214203143: 5 steps
lem-F0-at0214203143 : Ws → ⟪ (Sb0-2-34-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-34-0 ∷ []) ⟫ʷ
lem-F0-at0214203143 c4 = run b0
  where
  b0 : Chain (Sb0-2-34-1 ∷ []) (Sb1-2-34-0 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Sb0-1-34-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·34·1⟩ (lit c4)) ▸
       at 1 1 (Sb2-1-34-0 ∷ []) (lem-F0-at0114203243 c4) ▸
       at 0 2 (Sb1-2-34-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·1·34·0⟩ (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- F0 @0214213043: 5 steps
lem-F0-at0214213043 : Ws → ⟪ (Sb1-2-34-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-34-1 ∷ []) ⟫ʷ
lem-F0-at0214213043 c4 = run b0
  where
  b0 : Chain (Sb1-2-34-0 ∷ []) (Sb0-2-34-1 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Sb0-2-34-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·2·34·0⟩ (lit c4)) ▸
       at 1 1 (Sb1-2-34-0 ∷ []) (lem-F0-at0214203143 c4) ▸
       at 0 2 (Sb0-2-34-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·2·34·0⟩ (lit c4)) ▸
       at 1 2 [] (wl0002 (lit c4)) ▸ done


-- auto Kd0 | BOX(0;1234) @3443: 7 steps
lem-auto-Kd0-∣-BOX⟨0·1234⟩-at3443 : Ws → ⟪ (K0⁻ ∷ Bx0-1243 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1243 ∷ K0⁻ ∷ []) ⟫ʷ
lem-auto-Kd0-∣-BOX⟨0·1234⟩-at3443 c4 = run b0
  where
  b0 : Chain (K0⁻ ∷ Bx0-1243 ∷ []) (Bx0-1243 ∷ K0⁻ ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (K0⁻ ∷ Sw34 ∷ []) (sym (c₁ (K • iI) (Swap ↑ ↑))) ▸
       at 2 2 (Bx0-1234 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1243⟩ (lit c4)) ▸
       at 1 2 (Bx0-1234 ∷ K0⁻ ∷ []) (lem-auto-Kd0-∣-BOX⟨0·1234⟩ c4) ▸
       at 0 2 (Bx0-1243 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1234⟩ (lit c4)) ▸
       at 1 2 (K0⁻ ∷ Sw34 ∷ []) (sym (c₁ (K • iI) (Swap ↑ ↑))) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto Kd0 | BOX(0;1234) @233442: 7 steps
lem-auto-Kd0-∣-BOX⟨0·1234⟩-at233442 : Ws → ⟪ (K0⁻ ∷ Bx0-1342 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1342 ∷ K0⁻ ∷ []) ⟫ʷ
lem-auto-Kd0-∣-BOX⟨0·1234⟩-at233442 c4 = run b0
  where
  b0 : Chain (K0⁻ ∷ Bx0-1342 ∷ []) (Bx0-1342 ∷ K0⁻ ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (K0⁻ ∷ Sw23 ∷ []) (sym (c₁ (K • iI) (Swap ↑))) ▸
       at 2 2 (Bx0-1243 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1342⟩ (lit c4)) ▸
       at 1 2 (Bx0-1243 ∷ K0⁻ ∷ []) (lem-auto-Kd0-∣-BOX⟨0·1234⟩-at3443 c4) ▸
       at 0 2 (Bx0-1342 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1243⟩ (lit c4)) ▸
       at 1 2 (K0⁻ ∷ Sw23 ∷ []) (sym (c₁ (K • iI) (Swap ↑))) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto Kd0 | BOX(0;1234) @12233441: 7 steps
lem-auto-Kd0-∣-BOX⟨0·1234⟩-at12233441 : Ws → ⟪ (K0⁻ ∷ Bx0-2341 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2341 ∷ K0⁻ ∷ []) ⟫ʷ
lem-auto-Kd0-∣-BOX⟨0·1234⟩-at12233441 c4 = run b0
  where
  b0 : Chain (K0⁻ ∷ Bx0-2341 ∷ []) (Bx0-2341 ∷ K0⁻ ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (K0⁻ ∷ Sw12 ∷ []) (sym (c₁ (K • iI) (Swap))) ▸
       at 2 2 (Bx0-1342 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2341⟩ (lit c4)) ▸
       at 1 2 (Bx0-1342 ∷ K0⁻ ∷ []) (lem-auto-Kd0-∣-BOX⟨0·1234⟩-at233442 c4) ▸
       at 0 2 (Bx0-2341 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1342⟩ (lit c4)) ▸
       at 1 2 (K0⁻ ∷ Sw12 ∷ []) (sym (c₁ (K • iI) (Swap))) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto Kd0 | SBOX(1;2;34;0): 13 steps
lem-auto-Kd0-∣-SBOX⟨1·2·34·0⟩ : Ws → ⟪ (K0⁻ ∷ Sb1-2-34-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-34-0 ∷ K0⁻ ∷ []) ⟫ʷ
lem-auto-Kd0-∣-SBOX⟨1·2·34·0⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (K0⁻ ∷ Sb1-2-34-0 ∷ []) (Bx0-2341 ∷ Toff134 ∷ Sb0-2-1-4 ∷ Toff134 ∷ K0⁻ ∷ Sb⁻0-2-1-4 ∷ [])
  b0 = at 1 1 (Sb0-2-34-1 ∷ []) (lem-F0-at0214213043 c4) ▸
       at 1 1 (Bx0-2341 ∷ Toff134 ∷ Sb0-2-1-4 ∷ Toff134 ∷ Sb⁻0-2-1-4 ∷ []) (refl) ▸
       at 0 2 (Bx0-2341 ∷ K0⁻ ∷ []) (lem-auto-Kd0-∣-BOX⟨0·1234⟩-at12233441 c4) ▸
       at 1 2 (Toff134 ∷ K0⁻ ∷ []) (wp0090 c4) ▸
       at 3 1 (CS12 ∷ []) (refl) ▸
       at 2 2 (CS12 ∷ K0⁻ ∷ []) (sym (wl0287 (lit c4))) ▸
       at 2 1 (Sb0-2-1-4 ∷ []) (refl) ▸
       at 3 2 (Toff134 ∷ K0⁻ ∷ []) (wp0090 c4) ▸ done

  b1 : Chain (Bx0-2341 ∷ Toff134 ∷ Sb0-2-1-4 ∷ Toff134 ∷ K0⁻ ∷ Sb⁻0-2-1-4 ∷ []) (Sb1-2-34-0 ∷ K0⁻ ∷ [])
  b1 = at 5 1 (CS12⁻ ∷ []) (refl) ▸
       at 4 2 (CS12⁻ ∷ K0⁻ ∷ []) (sym (wl0288 (lit c4))) ▸
       at 4 1 (Sb⁻0-2-1-4 ∷ []) (refl) ▸
       at 0 5 (Sb0-2-34-1 ∷ []) (refl) ▸
       at 0 1 (Sb1-2-34-0 ∷ []) (sym (lem-F0-at0214213043 c4)) ▸ done


-- sym12 @13213442: 5 steps
lem-sym12-at13213442 : Ws → ⟪ (Bx0-3142 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1342 ∷ []) ⟫ʷ
lem-sym12-at13213442 c4 = run b0
  where
  b0 : Chain (Bx0-3142 ∷ []) (Bx0-1342 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx0-2143 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3142⟩ (lit c4)) ▸
       at 1 1 (Bx0-1243 ∷ []) (lem-sym12-at12213443 c4) ▸
       at 0 2 (Bx0-1342 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1243⟩ (lit c4)) ▸
       at 1 2 [] (wl0006 (lit c4)) ▸ done


-- sym12 @0113203442: 5 steps
lem-sym12-at0113203442 : Ws → ⟪ (Bx1-3042 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0342 ∷ []) ⟫ʷ
lem-sym12-at0113203442 c4 = run b0
  where
  b0 : Chain (Bx1-3042 ∷ []) (Bx1-0342 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx0-3142 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·3042⟩ (lit c4)) ▸
       at 1 1 (Bx0-1342 ∷ []) (lem-sym12-at13213442 c4) ▸
       at 0 2 (Bx1-0342 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1342⟩ (lit c4)) ▸
       at 1 2 [] (wl0002 (lit c4)) ▸ done


-- sym12 @0213203441: 5 steps
lem-sym12-at0213203441 : Ws → ⟪ (Bx2-3041 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0341 ∷ []) ⟫ʷ
lem-sym12-at0213203441 c4 = run b0
  where
  b0 : Chain (Bx2-3041 ∷ []) (Bx2-0341 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx1-3042 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·3041⟩ (lit c4)) ▸
       at 1 1 (Bx1-0342 ∷ []) (lem-sym12-at0113203442 c4) ▸
       at 0 2 (Bx2-0341 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0342⟩ (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- sym34 @0110233442: 5 steps
lem-sym34-at0110233442 : Ws → ⟪ (Bx1-0342 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0324 ∷ []) ⟫ʷ
lem-sym34-at0110233442 c4 = run b0
  where
  b0 : Chain (Bx1-0342 ∷ []) (Bx1-0324 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx0-1342 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0342⟩ (lit c4)) ▸
       at 1 1 (Bx0-1324 ∷ []) (lem-sym34-at233442 c4) ▸
       at 0 2 (Bx1-0324 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1324⟩ (lit c4)) ▸
       at 1 2 [] (wl0002 (lit c4)) ▸ done


-- sym34 @0210233441: 5 steps
lem-sym34-at0210233441 : Ws → ⟪ (Bx2-0341 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0314 ∷ []) ⟫ʷ
lem-sym34-at0210233441 c4 = run b0
  where
  b0 : Chain (Bx2-0341 ∷ []) (Bx2-0314 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx1-0342 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0341⟩ (lit c4)) ▸
       at 1 1 (Bx1-0324 ∷ []) (lem-sym34-at0110233442 c4) ▸
       at 0 2 (Bx2-0314 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0324⟩ (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- sym23 @01102332: 5 steps
lem-sym23-at01102332 : Ws → ⟪ (Bx1-0324 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0234 ∷ []) ⟫ʷ
lem-sym23-at01102332 c4 = run b0
  where
  b0 : Chain (Bx1-0324 ∷ []) (Bx1-0234 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx0-1324 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0324⟩ (lit c4)) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym23-at2332 c4) ▸
       at 0 2 (Bx1-0234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1234⟩ (lit c4)) ▸
       at 1 2 [] (wl0002 (lit c4)) ▸ done


-- sym23 @02102331: 5 steps
lem-sym23-at02102331 : Ws → ⟪ (Bx2-0314 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ []) ⟫ʷ
lem-sym23-at02102331 c4 = run b0
  where
  b0 : Chain (Bx2-0314 ∷ []) (Bx2-0134 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx1-0324 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0314⟩ (lit c4)) ▸
       at 1 1 (Bx1-0234 ∷ []) (lem-sym23-at01102332 c4) ▸
       at 0 2 (Bx2-0134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0234⟩ (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- CS12-beta @0110: 7 steps
lem-CS12-beta-at0110 : Ws → ⟪ (CS02 ∷ Bx1-0234 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0234 ∷ CS02 ∷ []) ⟫ʷ
lem-CS12-beta-at0110 c4 = run b0
  where
  b0 : Chain (CS02 ∷ Bx1-0234 ∷ []) (Bx1-0234 ∷ CS02 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (CS12 ∷ Sw01 ∷ []) (sym (wl0138 (lit c4))) ▸
       at 2 2 (Bx0-1234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0234⟩ (lit c4)) ▸
       at 1 2 (Bx0-1234 ∷ CS12 ∷ []) (lem-CS12-beta c4) ▸
       at 0 2 (Bx1-0234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1234⟩ (lit c4)) ▸
       at 1 2 (CS02 ∷ Sw01 ∷ []) (sym (wl0035 (lit c4))) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- CS12-beta @021021: 7 steps
lem-CS12-beta-at021021 : Ws → ⟪ (CS01 ∷ Bx2-0134 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ CS01 ∷ []) ⟫ʷ
lem-CS12-beta-at021021 c4 = run b0
  where
  b0 : Chain (CS01 ∷ Bx2-0134 ∷ []) (Bx2-0134 ∷ CS01 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CS02 ∷ Sw12 ∷ []) (lem-nat-1-CS01 (lit c4)) ▸
       at 2 2 (Bx1-0234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0134⟩ (lit c4)) ▸
       at 1 2 (Bx1-0234 ∷ CS02 ∷ []) (lem-CS12-beta-at0110 c4) ▸
       at 0 2 (Bx2-0134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0234⟩ (lit c4)) ▸
       at 1 2 (CS01 ∷ Sw12 ∷ []) (lem-nat-1-CS02 (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- sym34 @01102332: 5 steps
lem-sym34-at01102332 : Ws → ⟪ (Bx1-0324 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0342 ∷ []) ⟫ʷ
lem-sym34-at01102332 c4 = run b0
  where
  b0 : Chain (Bx1-0324 ∷ []) (Bx1-0342 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx0-1324 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0324⟩ (lit c4)) ▸
       at 1 1 (Bx0-1342 ∷ []) (lem-sym34-at2332 c4) ▸
       at 0 2 (Bx1-0342 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1342⟩ (lit c4)) ▸
       at 1 2 [] (wl0002 (lit c4)) ▸ done


-- sym34 @02102331: 5 steps
lem-sym34-at02102331 : Ws → ⟪ (Bx2-0314 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0341 ∷ []) ⟫ʷ
lem-sym34-at02102331 c4 = run b0
  where
  b0 : Chain (Bx2-0314 ∷ []) (Bx2-0341 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx1-0324 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0314⟩ (lit c4)) ▸
       at 1 1 (Bx1-0342 ∷ []) (lem-sym34-at01102332 c4) ▸
       at 0 2 (Bx2-0341 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0342⟩ (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- sym12 @0110233442: 5 steps
lem-sym12-at0110233442 : Ws → ⟪ (Bx1-0342 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3042 ∷ []) ⟫ʷ
lem-sym12-at0110233442 c4 = run b0
  where
  b0 : Chain (Bx1-0342 ∷ []) (Bx1-3042 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx0-1342 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0342⟩ (lit c4)) ▸
       at 1 1 (Bx0-3142 ∷ []) (lem-sym12-at233442 c4) ▸
       at 0 2 (Bx1-3042 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·3142⟩ (lit c4)) ▸
       at 1 2 [] (wl0002 (lit c4)) ▸ done


-- sym12 @0210233441: 5 steps
lem-sym12-at0210233441 : Ws → ⟪ (Bx2-0341 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3041 ∷ []) ⟫ʷ
lem-sym12-at0210233441 c4 = run b0
  where
  b0 : Chain (Bx2-0341 ∷ []) (Bx2-3041 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx1-0342 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0341⟩ (lit c4)) ▸
       at 1 1 (Bx1-3042 ∷ []) (lem-sym12-at0110233442 c4) ▸
       at 0 2 (Bx2-3041 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·3042⟩ (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- auto CS01 | BOX(2;3041): 7 steps
lem-auto-CS01-∣-BOX⟨2·3041⟩ : Ws → ⟪ (CS01 ∷ Bx2-3041 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3041 ∷ CS01 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨2·3041⟩ c4 = run b0
  where
  b0 : Chain (CS01 ∷ Bx2-3041 ∷ []) (Bx2-3041 ∷ CS01 ∷ [])
  b0 = at 1 1 (Bx2-0341 ∷ []) (lem-sym12-at0213203441 c4) ▸
       at 1 1 (Bx2-0314 ∷ []) (lem-sym34-at0210233441 c4) ▸
       at 1 1 (Bx2-0134 ∷ []) (lem-sym23-at02102331 c4) ▸
       at 0 2 (Bx2-0134 ∷ CS01 ∷ []) (lem-CS12-beta-at021021 c4) ▸
       at 0 1 (Bx2-0314 ∷ []) (lem-sym23-at021021 c4) ▸
       at 0 1 (Bx2-0341 ∷ []) (lem-sym34-at02102331 c4) ▸
       at 0 1 (Bx2-3041 ∷ []) (lem-sym12-at0210233441 c4) ▸ done


-- auto CS01 | SBOX(2;3;04;1): 9 steps
lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩ : Ws → ⟪ (CS01 ∷ Sb2-3-04-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-3-04-1 ∷ CS01 ∷ []) ⟫ʷ
lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CS01 ∷ Sb2-3-04-1 ∷ []) (Bx2-3041 ∷ Toff104 ∷ Sb2-3-1-4 ∷ Toff104 ∷ Sb⁻2-3-1-4 ∷ CS01 ∷ [])
  b0 = at 1 1 (Bx2-3041 ∷ Toff104 ∷ Sb2-3-1-4 ∷ Toff104 ∷ Sb⁻2-3-1-4 ∷ []) (refl) ▸
       at 0 2 (Bx2-3041 ∷ CS01 ∷ []) (lem-auto-CS01-∣-BOX⟨2·3041⟩ c4) ▸
       at 3 1 (CS13 ∷ []) (refl) ▸
       at 1 4 (Toff104 ∷ CS13 ∷ Toff104 ∷ CS01 ∷ []) (wp0091 c4) ▸
       at 2 1 (Sb2-3-1-4 ∷ []) (refl) ▸
       at 5 1 (CS13⁻ ∷ []) (refl) ▸
       at 4 2 (CS13⁻ ∷ CS01 ∷ []) (wl0289 (lit c4)) ▸
       at 4 1 (Sb⁻2-3-1-4 ∷ []) (refl) ▸ done

  b1 : Chain (Bx2-3041 ∷ Toff104 ∷ Sb2-3-1-4 ∷ Toff104 ∷ Sb⁻2-3-1-4 ∷ CS01 ∷ []) (Sb2-3-04-1 ∷ CS01 ∷ [])
  b1 = at 0 5 (Sb2-3-04-1 ∷ []) (refl) ▸ done


-- auto K0 | BOX(0;1234): 1 steps
lem-auto-K0-∣-BOX⟨0·1234⟩ : Ws → ⟪ (K0 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ K0 ∷ []) ⟫ʷ
lem-auto-K0-∣-BOX⟨0·1234⟩ c4 = run b0
  where
  b0 : Chain (K0 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ K0 ∷ [])
  b0 = at 0 2 (Bx0-1234 ∷ K0 ∷ []) (lem-K0-pass-c c4) ▸ done


-- auto K0 | BOX(0;1234) @3443: 7 steps
lem-auto-K0-∣-BOX⟨0·1234⟩-at3443 : Ws → ⟪ (K0 ∷ Bx0-1243 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1243 ∷ K0 ∷ []) ⟫ʷ
lem-auto-K0-∣-BOX⟨0·1234⟩-at3443 c4 = run b0
  where
  b0 : Chain (K0 ∷ Bx0-1243 ∷ []) (Bx0-1243 ∷ K0 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 2 2 (Bx0-1234 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1243⟩ (lit c4)) ▸
       at 1 2 (Bx0-1234 ∷ K0 ∷ []) (lem-auto-K0-∣-BOX⟨0·1234⟩ c4) ▸
       at 0 2 (Bx0-1243 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1234⟩ (lit c4)) ▸
       at 1 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto K0 | BOX(0;1234) @233442: 7 steps
lem-auto-K0-∣-BOX⟨0·1234⟩-at233442 : Ws → ⟪ (K0 ∷ Bx0-1342 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1342 ∷ K0 ∷ []) ⟫ʷ
lem-auto-K0-∣-BOX⟨0·1234⟩-at233442 c4 = run b0
  where
  b0 : Chain (K0 ∷ Bx0-1342 ∷ []) (Bx0-1342 ∷ K0 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 2 2 (Bx0-1243 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1342⟩ (lit c4)) ▸
       at 1 2 (Bx0-1243 ∷ K0 ∷ []) (lem-auto-K0-∣-BOX⟨0·1234⟩-at3443 c4) ▸
       at 0 2 (Bx0-1342 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1243⟩ (lit c4)) ▸
       at 1 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto K0 | BOX(0;1234) @12233441: 7 steps
lem-auto-K0-∣-BOX⟨0·1234⟩-at12233441 : Ws → ⟪ (K0 ∷ Bx0-2341 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2341 ∷ K0 ∷ []) ⟫ʷ
lem-auto-K0-∣-BOX⟨0·1234⟩-at12233441 c4 = run b0
  where
  b0 : Chain (K0 ∷ Bx0-2341 ∷ []) (Bx0-2341 ∷ K0 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 2 2 (Bx0-1342 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2341⟩ (lit c4)) ▸
       at 1 2 (Bx0-1342 ∷ K0 ∷ []) (lem-auto-K0-∣-BOX⟨0·1234⟩-at233442 c4) ▸
       at 0 2 (Bx0-2341 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1342⟩ (lit c4)) ▸
       at 1 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto K0 | SBOX(1;2;34;0): 13 steps
lem-auto-K0-∣-SBOX⟨1·2·34·0⟩ : Ws → ⟪ (K0 ∷ Sb1-2-34-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-34-0 ∷ K0 ∷ []) ⟫ʷ
lem-auto-K0-∣-SBOX⟨1·2·34·0⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (K0 ∷ Sb1-2-34-0 ∷ []) (Bx0-2341 ∷ Toff134 ∷ Sb0-2-1-4 ∷ Toff134 ∷ K0 ∷ Sb⁻0-2-1-4 ∷ [])
  b0 = at 1 1 (Sb0-2-34-1 ∷ []) (lem-F0-at0214213043 c4) ▸
       at 1 1 (Bx0-2341 ∷ Toff134 ∷ Sb0-2-1-4 ∷ Toff134 ∷ Sb⁻0-2-1-4 ∷ []) (refl) ▸
       at 0 2 (Bx0-2341 ∷ K0 ∷ []) (lem-auto-K0-∣-BOX⟨0·1234⟩-at12233441 c4) ▸
       at 1 2 (Toff134 ∷ K0 ∷ []) (wp0092 c4) ▸
       at 3 1 (CS12 ∷ []) (refl) ▸
       at 2 2 (CS12 ∷ K0 ∷ []) (sym (wl0290 (lit c4))) ▸
       at 2 1 (Sb0-2-1-4 ∷ []) (refl) ▸
       at 3 2 (Toff134 ∷ K0 ∷ []) (wp0092 c4) ▸ done

  b1 : Chain (Bx0-2341 ∷ Toff134 ∷ Sb0-2-1-4 ∷ Toff134 ∷ K0 ∷ Sb⁻0-2-1-4 ∷ []) (Sb1-2-34-0 ∷ K0 ∷ [])
  b1 = at 5 1 (CS12⁻ ∷ []) (refl) ▸
       at 4 2 (CS12⁻ ∷ K0 ∷ []) (sym (wl0291 (lit c4))) ▸
       at 4 1 (Sb⁻0-2-1-4 ∷ []) (refl) ▸
       at 0 5 (Sb0-2-34-1 ∷ []) (refl) ▸
       at 0 1 (Sb1-2-34-0 ∷ []) (sym (lem-F0-at0214213043 c4)) ▸ done


-- auto SBOX(0;1;2;3) | BOX(0;1432): 14 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·1432⟩ : Ws → ⟪ (Sb0-1-2-3 ∷ Bx0-1432 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1432 ∷ Sb0-1-2-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·1432⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-1-2-3 ∷ Bx0-1432 ∷ []) (Toff014 ∷ CCZ023 ∷ CS12 ∷ Toff014 ∷ CCZ023 ∷ [])
  b0 = at 1 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-beta-T-at2442 c4) ▸
       at 0 1 (CS12 ∷ []) (refl) ▸
       at 0 2 (Toff014 ∷ CS12 ∷ []) (wp0093 c4) ▸
       at 1 1 (Sb0-1-2-3 ∷ []) (refl) ▸
       at 1 1 (CS12 ∷ []) (refl) ▸
       at 1 2 (CCZ023 ∷ CS12 ∷ []) (sym (wl0292 (lit c4))) ▸
       at 2 1 (Sb0-1-2-3 ∷ []) (refl) ▸
       at 2 1 (CS12 ∷ []) (refl) ▸ done

  b1 : Chain (Toff014 ∷ CCZ023 ∷ CS12 ∷ Toff014 ∷ CCZ023 ∷ []) (Bx0-1432 ∷ Sb0-1-2-3 ∷ [])
  b1 = at 2 2 (Toff014 ∷ CS12 ∷ []) (wp0093 c4) ▸
       at 3 1 (Sb0-1-2-3 ∷ []) (refl) ▸
       at 3 1 (CS12 ∷ []) (refl) ▸
       at 3 2 (CCZ023 ∷ CS12 ∷ []) (sym (wl0292 (lit c4))) ▸
       at 4 1 (Sb0-1-2-3 ∷ []) (refl) ▸
       at 0 4 (Bx0-1432 ∷ []) (sym (lem-beta-T-at2442 c4)) ▸ done


-- auto SBOX(0;1;2;3) | SBOX(0;1;43;2): 13 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩ : Ws → ⟪ (Sb0-1-2-3 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-43-2 ∷ Sb0-1-2-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-1-2-3 ∷ Sb0-1-43-2 ∷ []) (Bx0-1432 ∷ Toff234 ∷ Sb0-1-2-3 ∷ Toff234 ∷ CS12 ∷ Sb⁻0-1-2-3 ∷ [])
  b0 = at 1 1 (Bx0-1432 ∷ Toff234 ∷ Sb0-1-2-3 ∷ Toff234 ∷ Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 0 2 (Bx0-1432 ∷ Sb0-1-2-3 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨0·1432⟩ c4) ▸
       at 1 1 (CS12 ∷ []) (refl) ▸
       at 3 1 (CS12 ∷ []) (refl) ▸
       at 1 4 (Toff234 ∷ CS12 ∷ Toff234 ∷ CS12 ∷ []) (wl0293 (lit c4)) ▸
       at 2 1 (Sb0-1-2-3 ∷ []) (refl) ▸
       at 4 1 (Sb0-1-2-3 ∷ []) (refl) ▸
       at 4 1 (CS12 ∷ []) (refl) ▸ done

  b1 : Chain (Bx0-1432 ∷ Toff234 ∷ Sb0-1-2-3 ∷ Toff234 ∷ CS12 ∷ Sb⁻0-1-2-3 ∷ []) (Sb0-1-43-2 ∷ Sb0-1-2-3 ∷ [])
  b1 = at 5 1 (CS12⁻ ∷ []) (refl) ▸
       at 4 2 (CS12⁻ ∷ CS12 ∷ []) (wl0294 (lit c4)) ▸
       at 4 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 5 1 (Sb0-1-2-3 ∷ []) (refl) ▸
       at 0 5 (Sb0-1-43-2 ∷ []) (refl) ▸ done


-- auto BOX(0;1234) | BOX(0;1234): 6 steps
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨0·1234⟩ : Ws → ⟪ (Bx0-1234 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨0·1234⟩ c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ Bx0-1234 ∷ [])
  b0 = at 1 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-beta-T c4) ▸
       at 0 2 (Toff012 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-TOFF012 c4) ▸
       at 1 2 (CCZ034 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ034 c4) ▸
       at 2 2 (Toff012 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-TOFF012 c4) ▸
       at 3 2 (CCZ034 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ034 c4) ▸
       at 0 4 (Bx0-1234 ∷ []) (sym (lem-beta-T c4)) ▸ done


-- auto BOX(0;1234) | SBOX(0;1;4;3): 3 steps
lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·1·4·3⟩ : Ws → ⟪ (Bx0-1234 ∷ Sb0-1-4-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-4-3 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·1·4·3⟩ c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ Sb0-1-4-3 ∷ []) (Sb0-1-4-3 ∷ Bx0-1234 ∷ [])
  b0 = at 1 1 (CS14 ∷ []) (refl) ▸
       at 0 2 (CS14 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS14 c4) ▸
       at 0 1 (Sb0-1-4-3 ∷ []) (refl) ▸ done


-- auto BOX(0;1234) | SBOXd(0;1;4;3): 3 steps
lem-auto-BOX⟨0·1234⟩-∣-SBOXd⟨0·1·4·3⟩ : Ws → ⟪ (Bx0-1234 ∷ Sb⁻0-1-4-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-4-3 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-SBOXd⟨0·1·4·3⟩ c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ Sb⁻0-1-4-3 ∷ []) (Sb⁻0-1-4-3 ∷ Bx0-1234 ∷ [])
  b0 = at 1 1 (CS14⁻ ∷ []) (refl) ▸
       at 0 2 (CS14⁻ ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd14 c4) ▸
       at 0 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸ done


-- auto BOX(0;1234) TOFF423 | CCZ231: 2 steps
lem-auto-BOX⟨0·1234⟩-TOFF423-∣-CCZ231 : Ws → ⟪ (Bx0-1234 ∷ Toff423 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Bx0-1234 ∷ Toff423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-TOFF423-∣-CCZ231 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ Toff423 ∷ CCZ123 ∷ []) (CCZ123 ∷ Bx0-1234 ∷ Toff423 ∷ [])
  b0 = at 1 2 (CCZ123 ∷ Toff423 ∷ []) (sym (wl0295 (lit c4))) ▸
       at 0 2 (CCZ123 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231 c4) ▸ done


-- T312-beta @3443: 8 steps
lem-T312-beta-at3443 : Ws → ⟪ (Toff412 ∷ Bx0-1243 ∷ Toff412 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1243 ∷ CCZ123 ∷ []) ⟫ʷ
lem-T312-beta-at3443 c4 = run b0
  where
  b0 : Chain (Toff412 ∷ Bx0-1243 ∷ Toff412 ∷ []) (Bx0-1243 ∷ CCZ123 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Toff312 ∷ Sw34 ∷ []) (lem-nat-3-TOFF412 (lit c4)) ▸
       at 2 2 (Bx0-1234 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1243⟩ (lit c4)) ▸
       at 3 2 (Toff312 ∷ Sw34 ∷ []) (lem-nat-3-TOFF412 (lit c4)) ▸
       at 1 3 (Bx0-1234 ∷ CCZ124 ∷ []) (lem-T312-beta c4) ▸
       at 0 2 (Bx0-1243 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1234⟩ (lit c4)) ▸
       at 1 2 (CCZ123 ∷ Sw34 ∷ []) (lem-nat-3-CCZ124 (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- T312-beta @233442: 8 steps
lem-T312-beta-at233442 : Ws → ⟪ (Toff413 ∷ Bx0-1342 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1342 ∷ CCZ123 ∷ []) ⟫ʷ
lem-T312-beta-at233442 c4 = run b0
  where
  b0 : Chain (Toff413 ∷ Bx0-1342 ∷ Toff413 ∷ []) (Bx0-1342 ∷ CCZ123 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Toff412 ∷ Sw23 ∷ []) (lem-nat-2-TOFF413 (lit c4)) ▸
       at 2 2 (Bx0-1243 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1342⟩ (lit c4)) ▸
       at 3 2 (Toff412 ∷ Sw23 ∷ []) (lem-nat-2-TOFF413 (lit c4)) ▸
       at 1 3 (Bx0-1243 ∷ CCZ123 ∷ []) (lem-T312-beta-at3443 c4) ▸
       at 0 2 (Bx0-1342 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1243⟩ (lit c4)) ▸
       at 1 2 (CCZ123 ∷ Sw23 ∷ []) (sym (wl0113 (lit c4))) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- T312-beta @12233441: 8 steps
lem-T312-beta-at12233441 : Ws → ⟪ (Toff423 ∷ Bx0-2341 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2341 ∷ CCZ123 ∷ []) ⟫ʷ
lem-T312-beta-at12233441 c4 = run b0
  where
  b0 : Chain (Toff423 ∷ Bx0-2341 ∷ Toff423 ∷ []) (Bx0-2341 ∷ CCZ123 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Toff413 ∷ Sw12 ∷ []) (wl0091 (lit c4)) ▸
       at 2 2 (Bx0-1342 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2341⟩ (lit c4)) ▸
       at 3 2 (Toff413 ∷ Sw12 ∷ []) (wl0091 (lit c4)) ▸
       at 1 3 (Bx0-1342 ∷ CCZ123 ∷ []) (lem-T312-beta-at233442 c4) ▸
       at 0 2 (Bx0-2341 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1342⟩ (lit c4)) ▸
       at 1 2 (CCZ123 ∷ Sw12 ∷ []) (sym (wl0111 (lit c4))) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto BOX(0;1234) | SBOX(0;1;23;4): 31 steps
lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·1·23·4⟩ : Ws → ⟪ (Bx0-1234 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-23-4 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·1·23·4⟩ c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (Bx0-1234 ∷ Sb0-1-23-4 ∷ []) (Bx0-1234 ∷ Toff423 ∷ Bx0-2314 ∷ CCZ123 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ [])
  b0 = at 1 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 0 2 (Bx0-1234 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨0·1234⟩ c4) ▸
       at 1 0 (Toff423 ∷ Toff423 ∷ []) (sym (wl0296 (lit c4))) ▸
       at 3 1 (Bx0-2134 ∷ []) (lem-sym12 c4) ▸
       at 3 1 (Bx0-2314 ∷ []) (lem-sym23-at1221 c4) ▸
       at 3 1 (Bx0-2341 ∷ []) (lem-sym34-at122331 c4) ▸
       at 2 3 (Bx0-2341 ∷ CCZ123 ∷ []) (lem-T312-beta-at12233441 c4) ▸
       at 2 1 (Bx0-2314 ∷ []) (lem-sym34-at12233441 c4) ▸ done

  b1 : Chain (Bx0-1234 ∷ Toff423 ∷ Bx0-2314 ∷ CCZ123 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (Bx0-1234 ∷ Toff423 ∷ CCZ123 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Toff423 ∷ Bx0-2341 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ [])
  b1 = at 2 1 (Bx0-2134 ∷ []) (lem-sym23-at122331 c4) ▸
       at 2 1 (Bx0-1234 ∷ []) (lem-sym12-at1221 c4) ▸
       at 2 2 (CCZ123 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231 c4) ▸
       at 3 2 (Sb0-1-4-3 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·1·4·3⟩ c4) ▸
       at 4 0 (Toff423 ∷ Toff423 ∷ []) (sym (wl0296 (lit c4))) ▸
       at 6 1 (Bx0-2134 ∷ []) (lem-sym12 c4) ▸
       at 6 1 (Bx0-2314 ∷ []) (lem-sym23-at1221 c4) ▸
       at 6 1 (Bx0-2341 ∷ []) (lem-sym34-at122331 c4) ▸ done

  b2 : Chain (Bx0-1234 ∷ Toff423 ∷ CCZ123 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Toff423 ∷ Bx0-2341 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (CCZ123 ∷ Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ CCZ123 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Bx0-1234 ∷ [])
  b2 = at 5 3 (Bx0-2341 ∷ CCZ123 ∷ []) (lem-T312-beta-at12233441 c4) ▸
       at 5 1 (Bx0-2314 ∷ []) (lem-sym34-at12233441 c4) ▸
       at 5 1 (Bx0-2134 ∷ []) (lem-sym23-at122331 c4) ▸
       at 5 1 (Bx0-1234 ∷ []) (lem-sym12-at1221 c4) ▸
       at 5 2 (CCZ123 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231 c4) ▸
       at 6 2 (Sb⁻0-1-4-3 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-SBOXd⟨0·1·4·3⟩ c4) ▸
       at 0 3 (CCZ123 ∷ Bx0-1234 ∷ Toff423 ∷ []) (lem-auto-BOX⟨0·1234⟩-TOFF423-∣-CCZ231 c4) ▸
       at 4 2 (CCZ123 ∷ Toff423 ∷ []) (sym (wl0295 (lit c4))) ▸ done

  b3 : Chain (CCZ123 ∷ Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ CCZ123 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Bx0-1234 ∷ []) (Sb0-1-23-4 ∷ Bx0-1234 ∷ [])
  b3 = at 3 1 (CS14 ∷ []) (refl) ▸
       at 3 2 (CCZ123 ∷ CS14 ∷ []) (sym (wl0297 (lit c4))) ▸
       at 4 1 (Sb0-1-4-3 ∷ []) (refl) ▸
       at 2 2 (CCZ123 ∷ Toff423 ∷ []) (sym (wl0295 (lit c4))) ▸
       at 1 2 (CCZ123 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231 c4) ▸
       at 0 2 [] (wl0212 (lit c4)) ▸
       at 0 5 (Sb0-1-23-4 ∷ []) (refl) ▸ done


-- auto BOX(0;1234) | CS41: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS41 : Ws → ⟪ (Bx0-1234 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS41 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ CS14 ∷ []) (CS14 ∷ Bx0-1234 ∷ [])
  b0 = at 1 1 (CS14 ∷ []) (wl0298 (lit c4)) ▸
       at 0 1 (Bx0-1243 ∷ []) (lem-sym34 c4) ▸
       at 0 1 (Bx0-1423 ∷ []) (lem-sym23-at3443 c4) ▸
       at 0 2 (CS14 ∷ Bx0-1423 ∷ []) (sym (lem-CS12-beta-at243243 c4)) ▸
       at 1 1 (Bx0-1243 ∷ []) (lem-sym23-at243243 c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym34-at3443 c4) ▸
       at 0 1 (CS14 ∷ []) (wl0298 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | CS41: 9 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS41 : Ws → ⟪ (Sb0-1-23-4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS41 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-1-23-4 ∷ CS14 ∷ []) (CS14 ∷ Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 4 1 (CS14⁻ ∷ []) (refl) ▸
       at 4 2 (CS14 ∷ CS14⁻ ∷ []) (sym (wl0299 (lit c4))) ▸
       at 5 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 2 1 (CS14 ∷ []) (refl) ▸
       at 1 4 (CS14 ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ []) (sym (wl0300 (lit c4))) ▸
       at 3 1 (Sb0-1-4-3 ∷ []) (refl) ▸
       at 0 2 (CS14 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS41 c4) ▸ done

  b1 : Chain (CS14 ∷ Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (CS14 ∷ Sb0-1-23-4 ∷ [])
  b1 = at 1 5 (Sb0-1-23-4 ∷ []) (refl) ▸ done


-- auto BOX(0;1234) | K0: 1 steps
lem-auto-BOX⟨0·1234⟩-∣-K0 : Ws → ⟪ (Bx0-1234 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-K0 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ K0 ∷ []) (K0 ∷ Bx0-1234 ∷ [])
  b0 = at 0 2 (K0 ∷ Bx0-1234 ∷ []) (sym (lem-K0-pass-c c4)) ▸ done


-- F0 @3443: 5 steps
lem-F0-at3443 : Ws → ⟪ (Sb2-0-31-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-0-31-2 ∷ []) ⟫ʷ
lem-F0-at3443 c4 = run b0
  where
  b0 : Chain (Sb2-0-31-4 ∷ []) (Sb4-0-31-2 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Sb2-0-41-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨2·0·31·4⟩ (lit c4)) ▸
       at 1 1 (Sb3-0-41-2 ∷ []) (lem-F0 c4) ▸
       at 0 2 (Sb4-0-31-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨3·0·41·2⟩ (lit c4)) ▸
       at 1 2 [] (wl0007 (lit c4)) ▸ done


-- F0 @12213443: 5 steps
lem-F0-at12213443 : Ws → ⟪ (Sb1-0-32-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-0-32-1 ∷ []) ⟫ʷ
lem-F0-at12213443 c4 = run b0
  where
  b0 : Chain (Sb1-0-32-4 ∷ []) (Sb4-0-32-1 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Sb2-0-31-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·32·4⟩ (lit c4)) ▸
       at 1 1 (Sb4-0-31-2 ∷ []) (lem-F0-at3443 c4) ▸
       at 0 2 (Sb4-0-32-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨4·0·31·2⟩ (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- F0 @13213442: 5 steps
lem-F0-at13213442 : Ws → ⟪ (Sb1-0-23-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-0-23-1 ∷ []) ⟫ʷ
lem-F0-at13213442 c4 = run b0
  where
  b0 : Chain (Sb1-0-23-4 ∷ []) (Sb4-0-23-1 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb1-0-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·23·4⟩ (lit c4)) ▸
       at 1 1 (Sb4-0-32-1 ∷ []) (lem-F0-at12213443 c4) ▸
       at 0 2 (Sb4-0-23-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨4·0·32·1⟩ (lit c4)) ▸
       at 1 2 [] (wl0006 (lit c4)) ▸ done


-- F0 @0113203442: 5 steps
lem-F0-at0113203442 : Ws → ⟪ (Sb0-1-23-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-1-23-0 ∷ []) ⟫ʷ
lem-F0-at0113203442 c4 = run b0
  where
  b0 : Chain (Sb0-1-23-4 ∷ []) (Sb4-1-23-0 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Sb1-0-23-4 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·23·4⟩ (lit c4)) ▸
       at 1 1 (Sb4-0-23-1 ∷ []) (lem-F0-at13213442 c4) ▸
       at 0 2 (Sb4-1-23-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨4·0·23·1⟩ (lit c4)) ▸
       at 1 2 [] (wl0002 (lit c4)) ▸ done


-- auto BOX(0;1234) | K0 @0110: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-K0-at0110 : Ws → ⟪ (Bx1-0234 ∷ K1 ∷ []) ⟫ʷ ≈ ⟪ (K1 ∷ Bx1-0234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-K0-at0110 c4 = run b0
  where
  b0 : Chain (Bx1-0234 ∷ K1 ∷ []) (K1 ∷ Bx1-0234 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx0-1234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0234⟩ (lit c4)) ▸
       at 2 2 (K0 ∷ Sw01 ∷ []) (sym (wl0031 (lit c4))) ▸
       at 1 2 (K0 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-K0 c4) ▸
       at 0 2 (K1 ∷ Sw01 ∷ []) (sym (wl0076 (lit c4))) ▸
       at 1 2 (Bx1-0234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1234⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto BOX(0;1234) | K0 @021021: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-K0-at021021 : Ws → ⟪ (Bx2-0134 ∷ K2 ∷ []) ⟫ʷ ≈ ⟪ (K2 ∷ Bx2-0134 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-K0-at021021 c4 = run b0
  where
  b0 : Chain (Bx2-0134 ∷ K2 ∷ []) (K2 ∷ Bx2-0134 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx1-0234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0134⟩ (lit c4)) ▸
       at 2 2 (K1 ∷ Sw12 ∷ []) (sym (wl0062 (lit c4))) ▸
       at 1 2 (K1 ∷ Bx1-0234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-K0-at0110 c4) ▸
       at 0 2 (K2 ∷ Sw12 ∷ []) (sym (wl0056 (lit c4))) ▸
       at 1 2 (Bx2-0134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0234⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto BOX(0;1234) | K0 @03102132: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-K0-at03102132 : Ws → ⟪ (Bx3-0124 ∷ K3 ∷ []) ⟫ʷ ≈ ⟪ (K3 ∷ Bx3-0124 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-K0-at03102132 c4 = run b0
  where
  b0 : Chain (Bx3-0124 ∷ K3 ∷ []) (K3 ∷ Bx3-0124 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx2-0134 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0124⟩ (lit c4)) ▸
       at 2 2 (K2 ∷ Sw23 ∷ []) (sym (wl0058 (lit c4))) ▸
       at 1 2 (K2 ∷ Bx2-0134 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-K0-at021021 c4) ▸
       at 0 2 (K3 ∷ Sw23 ∷ []) (sym (wl0057 (lit c4))) ▸
       at 1 2 (Bx3-0124 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0134⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto BOX(0;1234) | K0 @0410213243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-K0-at0410213243 : Ws → ⟪ (Bx4-0123 ∷ K4 ∷ []) ⟫ʷ ≈ ⟪ (K4 ∷ Bx4-0123 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-K0-at0410213243 c4 = run b0
  where
  b0 : Chain (Bx4-0123 ∷ K4 ∷ []) (K4 ∷ Bx4-0123 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Bx3-0124 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·0123⟩ (lit c4)) ▸
       at 2 2 (K3 ∷ Sw34 ∷ []) (sym (wl0068 (lit c4))) ▸
       at 1 2 (K3 ∷ Bx3-0124 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-K0-at03102132 c4) ▸
       at 0 2 (K4 ∷ Sw34 ∷ []) (sym (wl0067 (lit c4))) ▸
       at 1 2 (Bx4-0123 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·0124⟩ (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto BOX(0;1234) | K0 @04102142: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-K0-at04102142 : Ws → ⟪ (Bx4-0132 ∷ K4 ∷ []) ⟫ʷ ≈ ⟪ (K4 ∷ Bx4-0132 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-K0-at04102142 c4 = run b0
  where
  b0 : Chain (Bx4-0132 ∷ K4 ∷ []) (K4 ∷ Bx4-0132 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx4-0123 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·0132⟩ (lit c4)) ▸
       at 2 2 (K4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K)) ▸
       at 1 2 (K4 ∷ Bx4-0123 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-K0-at0410213243 c4) ▸
       at 0 2 (K4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K)) ▸
       at 1 2 (Bx4-0132 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·0123⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto BOX(0;1234) | K0 @041041: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-K0-at041041 : Ws → ⟪ (Bx4-0231 ∷ K4 ∷ []) ⟫ʷ ≈ ⟪ (K4 ∷ Bx4-0231 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-K0-at041041 c4 = run b0
  where
  b0 : Chain (Bx4-0231 ∷ K4 ∷ []) (K4 ∷ Bx4-0231 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx4-0132 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·0231⟩ (lit c4)) ▸
       at 2 2 (K4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K ↑)) ▸
       at 1 2 (K4 ∷ Bx4-0132 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-K0-at04102142 c4) ▸
       at 0 2 (K4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K ↑)) ▸
       at 1 2 (Bx4-0231 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·0132⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto BOX(0;1234) | K0 @0440: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-K0-at0440 : Ws → ⟪ (Bx4-1230 ∷ K4 ∷ []) ⟫ʷ ≈ ⟪ (K4 ∷ Bx4-1230 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-K0-at0440 c4 = run b0
  where
  b0 : Chain (Bx4-1230 ∷ K4 ∷ []) (K4 ∷ Bx4-1230 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx4-0231 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·1230⟩ (lit c4)) ▸
       at 2 2 (K4 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ ↑)) ▸
       at 1 2 (K4 ∷ Bx4-0231 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-K0-at041041 c4) ▸
       at 0 2 (K4 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ ↑)) ▸
       at 1 2 (Bx4-1230 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·0231⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | K4: 13 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-K4 : Ws → ⟪ (Sb0-1-23-4 ∷ K4 ∷ []) ⟫ʷ ≈ ⟪ (K4 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-K4 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-1-23-4 ∷ K4 ∷ []) (Bx4-1230 ∷ Toff023 ∷ K4 ∷ CS01 ∷ Toff023 ∷ Sb⁻4-1-0-3 ∷ [])
  b0 = at 0 1 (Sb4-1-23-0 ∷ []) (lem-F0-at0113203442 c4) ▸
       at 0 1 (Bx4-1230 ∷ Toff023 ∷ Sb4-1-0-3 ∷ Toff023 ∷ Sb⁻4-1-0-3 ∷ []) (refl) ▸
       at 4 1 (CS01⁻ ∷ []) (refl) ▸
       at 4 2 (K4 ∷ CS01⁻ ∷ []) (wl0301 (lit c4)) ▸
       at 5 1 (Sb⁻4-1-0-3 ∷ []) (refl) ▸
       at 3 2 (K4 ∷ Toff023 ∷ []) (sym (wp0094 c4)) ▸
       at 2 1 (CS01 ∷ []) (refl) ▸
       at 2 2 (K4 ∷ CS01 ∷ []) (wl0302 (lit c4)) ▸ done

  b1 : Chain (Bx4-1230 ∷ Toff023 ∷ K4 ∷ CS01 ∷ Toff023 ∷ Sb⁻4-1-0-3 ∷ []) (K4 ∷ Sb0-1-23-4 ∷ [])
  b1 = at 3 1 (Sb4-1-0-3 ∷ []) (refl) ▸
       at 1 2 (K4 ∷ Toff023 ∷ []) (sym (wp0094 c4)) ▸
       at 0 2 (K4 ∷ Bx4-1230 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-K0-at0440 c4) ▸
       at 1 5 (Sb4-1-23-0 ∷ []) (refl) ▸
       at 1 1 (Sb0-1-23-4 ∷ []) (sym (lem-F0-at0113203442 c4)) ▸ done


-- CS12-beta @12243143: 7 steps
lem-CS12-beta-at12243143 : Ws → ⟪ (CS24 ∷ Bx0-2413 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2413 ∷ CS24 ∷ []) ⟫ʷ
lem-CS12-beta-at12243143 c4 = run b0
  where
  b0 : Chain (CS24 ∷ Bx0-2413 ∷ []) (Bx0-2413 ∷ CS24 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0017 (lit c4))) ▸
       at 2 2 (Bx0-1423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2413⟩ (lit c4)) ▸
       at 1 2 (Bx0-1423 ∷ CS14 ∷ []) (lem-CS12-beta-at243243 c4) ▸
       at 0 2 (Bx0-2413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1423⟩ (lit c4)) ▸
       at 1 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0008 (lit c4))) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto BOX(0;1234) | CS24: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS24 : Ws → ⟪ (Bx0-1234 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS24 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ CS24 ∷ []) (CS24 ∷ Bx0-1234 ∷ [])
  b0 = at 0 1 (Bx0-2134 ∷ []) (lem-sym12 c4) ▸
       at 0 1 (Bx0-2143 ∷ []) (lem-sym34-at1221 c4) ▸
       at 0 1 (Bx0-2413 ∷ []) (lem-sym23-at12213443 c4) ▸
       at 0 2 (CS24 ∷ Bx0-2413 ∷ []) (sym (lem-CS12-beta-at12243143 c4)) ▸
       at 1 1 (Bx0-2143 ∷ []) (lem-sym23-at12243143 c4) ▸
       at 1 1 (Bx0-2134 ∷ []) (lem-sym34-at12213443 c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym12-at1221 c4) ▸ done


-- auto SBOX(0;1;23;4) | CS24: 9 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS24 : Ws → ⟪ (Sb0-1-23-4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS24 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-1-23-4 ∷ CS24 ∷ []) (CS24 ∷ Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 4 1 (CS14⁻ ∷ []) (refl) ▸
       at 4 2 (CS24 ∷ CS14⁻ ∷ []) (wl0303 (lit c4)) ▸
       at 5 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 2 1 (CS14 ∷ []) (refl) ▸
       at 1 4 (CS24 ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ []) (sym (wl0304 (lit c4))) ▸
       at 3 1 (Sb0-1-4-3 ∷ []) (refl) ▸
       at 0 2 (CS24 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS24 c4) ▸ done

  b1 : Chain (CS24 ∷ Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (CS24 ∷ Sb0-1-23-4 ∷ [])
  b1 = at 1 5 (Sb0-1-23-4 ∷ []) (refl) ▸ done


-- SBsym @3443: 5 steps
lem-SBsym-at3443 : Ws → ⟪ (Sb2-0-31-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-13-4 ∷ []) ⟫ʷ
lem-SBsym-at3443 c4 = run b0
  where
  b0 : Chain (Sb2-0-31-4 ∷ []) (Sb2-0-13-4 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Sb2-0-41-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨2·0·31·4⟩ (lit c4)) ▸
       at 1 1 (Sb2-0-14-3 ∷ []) (lem-SBsym c4) ▸
       at 0 2 (Sb2-0-13-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨2·0·14·3⟩ (lit c4)) ▸
       at 1 2 [] (wl0007 (lit c4)) ▸ done


-- SBsym @12213443: 5 steps
lem-SBsym-at12213443 : Ws → ⟪ (Sb1-0-32-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-23-4 ∷ []) ⟫ʷ
lem-SBsym-at12213443 c4 = run b0
  where
  b0 : Chain (Sb1-0-32-4 ∷ []) (Sb1-0-23-4 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Sb2-0-31-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·32·4⟩ (lit c4)) ▸
       at 1 1 (Sb2-0-13-4 ∷ []) (lem-SBsym-at3443 c4) ▸
       at 0 2 (Sb1-0-23-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·13·4⟩ (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- SBsym @13213442: 5 steps
lem-SBsym-at13213442 : Ws → ⟪ (Sb1-0-23-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-32-4 ∷ []) ⟫ʷ
lem-SBsym-at13213442 c4 = run b0
  where
  b0 : Chain (Sb1-0-23-4 ∷ []) (Sb1-0-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb1-0-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·23·4⟩ (lit c4)) ▸
       at 1 1 (Sb1-0-23-4 ∷ []) (lem-SBsym-at12213443 c4) ▸
       at 0 2 (Sb1-0-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·23·4⟩ (lit c4)) ▸
       at 1 2 [] (wl0006 (lit c4)) ▸ done


-- SBsym @0113203442: 5 steps
lem-SBsym-at0113203442 : Ws → ⟪ (Sb0-1-23-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-32-4 ∷ []) ⟫ʷ
lem-SBsym-at0113203442 c4 = run b0
  where
  b0 : Chain (Sb0-1-23-4 ∷ []) (Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Sb1-0-23-4 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·23·4⟩ (lit c4)) ▸
       at 1 1 (Sb1-0-32-4 ∷ []) (lem-SBsym-at13213442 c4) ▸
       at 0 2 (Sb0-1-32-4 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·32·4⟩ (lit c4)) ▸
       at 1 2 [] (wl0002 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | CS24 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS24-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS24-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ CS34 ∷ []) (CS34 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0015 (lit c4))) ▸
       at 1 2 (CS24 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS24 c4) ▸
       at 0 2 (CS34 ∷ Sw23 ∷ []) (sym (wl0011 (lit c4))) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | CS34 CS34: 6 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS34-CS34 : Ws → ⟪ (Sb0-1-23-4 ∷ CS34 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ CS34 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS34-CS34 c4 = run b0
  where
  b0 : Chain (Sb0-1-23-4 ∷ CS34 ∷ CS34 ∷ []) (CS34 ∷ CS34 ∷ Sb0-1-23-4 ∷ [])
  b0 = at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (CS34 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS24-at2332 c4) ▸
       at 1 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 1 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 1 2 (CS34 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS24-at2332 c4) ▸
       at 2 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸ done


-- auto SBOX(0;1;23;4) | CS34 CS34 @2332: 9 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS34-CS34-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ CS24 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CS24 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS34-CS34-at2332 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-1-32-4 ∷ CS24 ∷ CS24 ∷ []) (CS24 ∷ CS24 ∷ Sb0-1-32-4 ∷ Sw23 ∷ Sw23 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 (CS34 ∷ Sw23 ∷ []) (sym (wl0011 (lit c4))) ▸
       at 3 2 (CS34 ∷ Sw23 ∷ []) (sym (wl0011 (lit c4))) ▸
       at 1 3 (CS34 ∷ CS34 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS34-CS34 c4) ▸
       at 0 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0015 (lit c4))) ▸
       at 1 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0015 (lit c4))) ▸
       at 2 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ (lit c4)) ▸ done

  b1 : Chain (CS24 ∷ CS24 ∷ Sb0-1-32-4 ∷ Sw23 ∷ Sw23 ∷ []) (CS24 ∷ CS24 ∷ Sb0-1-32-4 ∷ [])
  b1 = at 3 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | CZ24: 5 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CZ24 : Ws → ⟪ (Sb0-1-23-4 ∷ CZ24 ∷ []) ⟫ʷ ≈ ⟪ (CZ24 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CZ24 c4 = run b0
  where
  b0 : Chain (Sb0-1-23-4 ∷ CZ24 ∷ []) (CZ24 ∷ Sb0-1-23-4 ∷ [])
  b0 = at 1 1 (CS24 ∷ CS24 ∷ []) (sym (wl0305 (lit c4))) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 3 (CS24 ∷ CS24 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS34-CS34-at2332 c4) ▸
       at 2 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 0 2 (CZ24 ∷ []) (wl0305 (lit c4)) ▸ done


-- auto BOX(0;1234) | Kd0: 1 steps
lem-auto-BOX⟨0·1234⟩-∣-Kd0 : Ws → ⟪ (Bx0-1234 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-Kd0 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ K0⁻ ∷ []) (K0⁻ ∷ Bx0-1234 ∷ [])
  b0 = at 0 2 (K0⁻ ∷ Bx0-1234 ∷ []) (sym (lem-K0-pass-ci c4)) ▸ done


-- auto BOX(0;1234) | Kd0 @0110: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-Kd0-at0110 : Ws → ⟪ (Bx1-0234 ∷ K1⁻ ∷ []) ⟫ʷ ≈ ⟪ (K1⁻ ∷ Bx1-0234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-Kd0-at0110 c4 = run b0
  where
  b0 : Chain (Bx1-0234 ∷ K1⁻ ∷ []) (K1⁻ ∷ Bx1-0234 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx0-1234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0234⟩ (lit c4)) ▸
       at 2 2 (K0⁻ ∷ Sw01 ∷ []) (sym (wl0257 (lit c4))) ▸
       at 1 2 (K0⁻ ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-Kd0 c4) ▸
       at 0 2 (K1⁻ ∷ Sw01 ∷ []) (sym (wl0306 (lit c4))) ▸
       at 1 2 (Bx1-0234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1234⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto BOX(0;1234) | Kd0 @021021: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-Kd0-at021021 : Ws → ⟪ (Bx2-0134 ∷ K2⁻ ∷ []) ⟫ʷ ≈ ⟪ (K2⁻ ∷ Bx2-0134 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-Kd0-at021021 c4 = run b0
  where
  b0 : Chain (Bx2-0134 ∷ K2⁻ ∷ []) (K2⁻ ∷ Bx2-0134 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx1-0234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0134⟩ (lit c4)) ▸
       at 2 2 (K1⁻ ∷ Sw12 ∷ []) (sym (wl0307 (lit c4))) ▸
       at 1 2 (K1⁻ ∷ Bx1-0234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-Kd0-at0110 c4) ▸
       at 0 2 (K2⁻ ∷ Sw12 ∷ []) (sym (wl0308 (lit c4))) ▸
       at 1 2 (Bx2-0134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0234⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto BOX(0;1234) | Kd0 @03102132: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-Kd0-at03102132 : Ws → ⟪ (Bx3-0124 ∷ K3⁻ ∷ []) ⟫ʷ ≈ ⟪ (K3⁻ ∷ Bx3-0124 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-Kd0-at03102132 c4 = run b0
  where
  b0 : Chain (Bx3-0124 ∷ K3⁻ ∷ []) (K3⁻ ∷ Bx3-0124 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx2-0134 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0124⟩ (lit c4)) ▸
       at 2 2 (K2⁻ ∷ Sw23 ∷ []) (sym (wl0309 (lit c4))) ▸
       at 1 2 (K2⁻ ∷ Bx2-0134 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-Kd0-at021021 c4) ▸
       at 0 2 (K3⁻ ∷ Sw23 ∷ []) (sym (wl0310 (lit c4))) ▸
       at 1 2 (Bx3-0124 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0134⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto BOX(0;1234) | Kd0 @0410213243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-Kd0-at0410213243 : Ws → ⟪ (Bx4-0123 ∷ K4⁻ ∷ []) ⟫ʷ ≈ ⟪ (K4⁻ ∷ Bx4-0123 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-Kd0-at0410213243 c4 = run b0
  where
  b0 : Chain (Bx4-0123 ∷ K4⁻ ∷ []) (K4⁻ ∷ Bx4-0123 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Bx3-0124 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·0123⟩ (lit c4)) ▸
       at 2 2 (K3⁻ ∷ Sw34 ∷ []) (sym (wl0311 (lit c4))) ▸
       at 1 2 (K3⁻ ∷ Bx3-0124 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-Kd0-at03102132 c4) ▸
       at 0 2 (K4⁻ ∷ Sw34 ∷ []) (sym (wl0312 (lit c4))) ▸
       at 1 2 (Bx4-0123 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·0124⟩ (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto BOX(0;1234) | Kd0 @04102142: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-Kd0-at04102142 : Ws → ⟪ (Bx4-0132 ∷ K4⁻ ∷ []) ⟫ʷ ≈ ⟪ (K4⁻ ∷ Bx4-0132 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-Kd0-at04102142 c4 = run b0
  where
  b0 : Chain (Bx4-0132 ∷ K4⁻ ∷ []) (K4⁻ ∷ Bx4-0132 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx4-0123 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·0132⟩ (lit c4)) ▸
       at 2 2 (K4⁻ ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K • iI)) ▸
       at 1 2 (K4⁻ ∷ Bx4-0123 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-Kd0-at0410213243 c4) ▸
       at 0 2 (K4⁻ ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K • iI)) ▸
       at 1 2 (Bx4-0132 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·0123⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto BOX(0;1234) | Kd0 @041041: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-Kd0-at041041 : Ws → ⟪ (Bx4-0231 ∷ K4⁻ ∷ []) ⟫ʷ ≈ ⟪ (K4⁻ ∷ Bx4-0231 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-Kd0-at041041 c4 = run b0
  where
  b0 : Chain (Bx4-0231 ∷ K4⁻ ∷ []) (K4⁻ ∷ Bx4-0231 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx4-0132 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·0231⟩ (lit c4)) ▸
       at 2 2 (K4⁻ ∷ Sw12 ∷ []) (c₃ (Swap ↑) ((K • iI) ↑)) ▸
       at 1 2 (K4⁻ ∷ Bx4-0132 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-Kd0-at04102142 c4) ▸
       at 0 2 (K4⁻ ∷ Sw12 ∷ []) (c₃ (Swap ↑) ((K • iI) ↑)) ▸
       at 1 2 (Bx4-0231 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·0132⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto BOX(0;1234) | Kd0 @0440: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-Kd0-at0440 : Ws → ⟪ (Bx4-1230 ∷ K4⁻ ∷ []) ⟫ʷ ≈ ⟪ (K4⁻ ∷ Bx4-1230 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-Kd0-at0440 c4 = run b0
  where
  b0 : Chain (Bx4-1230 ∷ K4⁻ ∷ []) (K4⁻ ∷ Bx4-1230 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx4-0231 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·1230⟩ (lit c4)) ▸
       at 2 2 (K4⁻ ∷ Sw01 ∷ []) (c₂ (Swap) ((K • iI) ↑ ↑)) ▸
       at 1 2 (K4⁻ ∷ Bx4-0231 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-Kd0-at041041 c4) ▸
       at 0 2 (K4⁻ ∷ Sw01 ∷ []) (c₂ (Swap) ((K • iI) ↑ ↑)) ▸
       at 1 2 (Bx4-1230 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·0231⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | Kd4: 13 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd4 : Ws → ⟪ (Sb0-1-23-4 ∷ K4⁻ ∷ []) ⟫ʷ ≈ ⟪ (K4⁻ ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd4 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-1-23-4 ∷ K4⁻ ∷ []) (Bx4-1230 ∷ Toff023 ∷ K4⁻ ∷ CS01 ∷ Toff023 ∷ Sb⁻4-1-0-3 ∷ [])
  b0 = at 0 1 (Sb4-1-23-0 ∷ []) (lem-F0-at0113203442 c4) ▸
       at 0 1 (Bx4-1230 ∷ Toff023 ∷ Sb4-1-0-3 ∷ Toff023 ∷ Sb⁻4-1-0-3 ∷ []) (refl) ▸
       at 4 1 (CS01⁻ ∷ []) (refl) ▸
       at 4 2 (K4⁻ ∷ CS01⁻ ∷ []) (wl0313 (lit c4)) ▸
       at 5 1 (Sb⁻4-1-0-3 ∷ []) (refl) ▸
       at 3 2 (K4⁻ ∷ Toff023 ∷ []) (sym (wp0095 c4)) ▸
       at 2 1 (CS01 ∷ []) (refl) ▸
       at 2 2 (K4⁻ ∷ CS01 ∷ []) (wl0314 (lit c4)) ▸ done

  b1 : Chain (Bx4-1230 ∷ Toff023 ∷ K4⁻ ∷ CS01 ∷ Toff023 ∷ Sb⁻4-1-0-3 ∷ []) (K4⁻ ∷ Sb0-1-23-4 ∷ [])
  b1 = at 3 1 (Sb4-1-0-3 ∷ []) (refl) ▸
       at 1 2 (K4⁻ ∷ Toff023 ∷ []) (sym (wp0095 c4)) ▸
       at 0 2 (K4⁻ ∷ Bx4-1230 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-Kd0-at0440 c4) ▸
       at 1 5 (Sb4-1-23-0 ∷ []) (refl) ▸
       at 1 1 (Sb0-1-23-4 ∷ []) (sym (lem-F0-at0113203442 c4)) ▸ done


-- auto SBOX(0;1;23;4) | K4 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ K4 ∷ []) ⟫ʷ ≈ ⟪ (K4 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ K4 ∷ []) (K4 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 (K4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K)) ▸
       at 1 2 (K4 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-K4 c4) ▸
       at 0 2 (K4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K)) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | CZ24 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CZ24-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ CZ34 ∷ []) ⟫ʷ ≈ ⟪ (CZ34 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CZ24-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ CZ34 ∷ []) (CZ34 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 (CZ24 ∷ Sw23 ∷ []) (sym (wl0027 (lit c4))) ▸
       at 1 2 (CZ24 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CZ24 c4) ▸
       at 0 2 (CZ34 ∷ Sw23 ∷ []) (sym (wl0028 (lit c4))) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | Kd4 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd4-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ K4⁻ ∷ []) ⟫ʷ ≈ ⟪ (K4⁻ ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd4-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ K4⁻ ∷ []) (K4⁻ ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 (K4⁻ ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K • iI)) ▸
       at 1 2 (K4⁻ ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd4 c4) ▸
       at 0 2 (K4⁻ ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K • iI)) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | CX34: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CX34 : Ws → ⟪ (Sb0-1-23-4 ∷ CX34 ∷ []) ⟫ʷ ≈ ⟪ (CX34 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CX34 c4 = run b0
  where
  b0 : Chain (Sb0-1-23-4 ∷ CX34 ∷ []) (CX34 ∷ Sb0-1-23-4 ∷ [])
  b0 = at 1 1 (K4 ∷ CZ34 ∷ K4⁻ ∷ []) (wl0315 (lit c4)) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (K4 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at2332 c4) ▸
       at 1 2 (CZ34 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CZ24-at2332 c4) ▸
       at 2 2 (K4⁻ ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd4-at2332 c4) ▸
       at 3 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 0 3 (CX34 ∷ []) (sym (wl0315 (lit c4))) ▸ done


-- auto BOX(0;1234) | CSd41: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd41 : Ws → ⟪ (Bx0-1234 ∷ CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS14⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd41 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ Bx0-1234 ∷ [])
  b0 = at 1 1 (CS14⁻ ∷ []) (wl0316 (lit c4)) ▸
       at 0 1 (Bx0-1243 ∷ []) (lem-sym34 c4) ▸
       at 0 1 (Bx0-1423 ∷ []) (lem-sym23-at3443 c4) ▸
       at 0 2 (CS14⁻ ∷ Bx0-1423 ∷ []) (sym (lem-CSd12-beta-at243243 c4)) ▸
       at 1 1 (Bx0-1243 ∷ []) (lem-sym23-at243243 c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym34-at3443 c4) ▸
       at 0 1 (CS14⁻ ∷ []) (wl0316 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | CSd41: 9 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd41 : Ws → ⟪ (Sb0-1-23-4 ∷ CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS14⁻ ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd41 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-1-23-4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 4 1 (CS14⁻ ∷ []) (refl) ▸
       at 4 2 (CS14⁻ ∷ CS14⁻ ∷ []) (wl0317 (lit c4)) ▸
       at 5 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 2 1 (CS14 ∷ []) (refl) ▸
       at 1 4 (CS14⁻ ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ []) (sym (wl0318 (lit c4))) ▸
       at 3 1 (Sb0-1-4-3 ∷ []) (refl) ▸
       at 0 2 (CS14⁻ ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd41 c4) ▸ done

  b1 : Chain (CS14⁻ ∷ Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (CS14⁻ ∷ Sb0-1-23-4 ∷ [])
  b1 = at 1 5 (Sb0-1-23-4 ∷ []) (refl) ▸ done


-- auto BOX(0;1234) | CS31: 5 steps
lem-auto-BOX⟨0·1234⟩-∣-CS31 : Ws → ⟪ (Bx0-1234 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS31 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ CS13 ∷ []) (CS13 ∷ Bx0-1234 ∷ [])
  b0 = at 1 1 (CS13 ∷ []) (wl0319 (lit c4)) ▸
       at 0 1 (Bx0-1324 ∷ []) (lem-sym23 c4) ▸
       at 0 2 (CS13 ∷ Bx0-1324 ∷ []) (sym (lem-CS12-beta-at2332 c4)) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym23-at2332 c4) ▸
       at 0 1 (CS13 ∷ []) (wl0319 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | CS31: 11 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS31 : Ws → ⟪ (Sb0-1-23-4 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS31 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-1-23-4 ∷ CS13 ∷ []) (Bx0-1234 ∷ Toff423 ∷ CS13 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 4 1 (CS14⁻ ∷ []) (refl) ▸
       at 4 2 (CS13 ∷ CS14⁻ ∷ []) (sym (wl0320 (lit c4))) ▸
       at 5 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 3 2 (CS13 ∷ Toff423 ∷ []) (sym (wl0321 (lit c4))) ▸
       at 2 1 (CS14 ∷ []) (refl) ▸
       at 2 2 (CS13 ∷ CS14 ∷ []) (sym (wl0322 (lit c4))) ▸
       at 3 1 (Sb0-1-4-3 ∷ []) (refl) ▸ done

  b1 : Chain (Bx0-1234 ∷ Toff423 ∷ CS13 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (CS13 ∷ Sb0-1-23-4 ∷ [])
  b1 = at 1 2 (CS13 ∷ Toff423 ∷ []) (sym (wl0321 (lit c4))) ▸
       at 0 2 (CS13 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS31 c4) ▸
       at 1 5 (Sb0-1-23-4 ∷ []) (refl) ▸ done


-- auto SBOX(0;1;23;4) | CS41 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS41-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS41-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ CS14 ∷ []) (CS14 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 (CS14 ∷ Sw23 ∷ []) (sym (wl0021 (lit c4))) ▸
       at 1 2 (CS14 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS41 c4) ▸
       at 0 2 (CS14 ∷ Sw23 ∷ []) (sym (wl0021 (lit c4))) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | CX34 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CX34-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ CX24 ∷ []) ⟫ʷ ≈ ⟪ (CX24 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CX34-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ CX24 ∷ []) (CX24 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 (CX34 ∷ Sw23 ∷ []) (sym (wl0051 (lit c4))) ▸
       at 1 2 (CX34 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CX34 c4) ▸
       at 0 2 (CX24 ∷ Sw23 ∷ []) (sym (wl0050 (lit c4))) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | CSd41 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd41-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS14⁻ ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd41-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 (CS14⁻ ∷ Sw23 ∷ []) (sym (wl0033 (lit c4))) ▸
       at 1 2 (CS14⁻ ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd41 c4) ▸
       at 0 2 (CS14⁻ ∷ Sw23 ∷ []) (sym (wl0033 (lit c4))) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | CS31 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS31-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS31-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ CS12 ∷ []) (CS12 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 (CS13 ∷ Sw23 ∷ []) (lem-nat-2-CS12 (lit c4)) ▸
       at 1 2 (CS13 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS31 c4) ▸
       at 0 2 (CS12 ∷ Sw23 ∷ []) (lem-nat-2-CS13 (lit c4)) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | CCZ124: 9 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ124 : Ws → ⟪ (Sb0-1-23-4 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ124 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-1-23-4 ∷ CCZ124 ∷ []) (CS14 ∷ CX24 ∷ CS14⁻ ∷ CX24 ∷ CS12 ∷ Sb0-1-23-4 ∷ [])
  b0 = at 1 1 (CS14 ∷ CX24 ∷ CS14⁻ ∷ CX24 ∷ CS12 ∷ []) (wl0323 (lit c4)) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (CS14 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS41-at2332 c4) ▸
       at 1 2 (CX24 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CX34-at2332 c4) ▸
       at 2 2 (CS14⁻ ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd41-at2332 c4) ▸
       at 3 2 (CX24 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CX34-at2332 c4) ▸
       at 4 2 (CS12 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS31-at2332 c4) ▸
       at 5 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸ done

  b1 : Chain (CS14 ∷ CX24 ∷ CS14⁻ ∷ CX24 ∷ CS12 ∷ Sb0-1-23-4 ∷ []) (CCZ124 ∷ Sb0-1-23-4 ∷ [])
  b1 = at 0 5 (CCZ124 ∷ []) (sym (wl0323 (lit c4))) ▸ done


-- F5d CS01: 64 steps
lem-F5d-CS01 : Ws → ⟪ (CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-0-41-3 ∷ X4 ∷ Sb⁻2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-F5d-CS01 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (run b7)))))))
  where
  b0 : Chain (CS01⁻ ∷ []) (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CS01⁻ ∷ [])
  b0 = at 0 0 (CS03 ∷ CS03⁻ ∷ []) (sym (wl0250 (lit c4))) ▸
       at 0 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 1 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 1 0 (Toff314 ∷ Toff314 ∷ []) (sym (wl0248 (lit c4))) ▸
       at 2 0 (CS03⁻ ∷ CS03 ∷ []) (sym (wl0249 (lit c4))) ▸
       at 2 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 3 0 (Toff314 ∷ Toff314 ∷ []) (sym (wl0248 (lit c4))) ▸ done

  b1 : Chain (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CS01⁻ ∷ []) (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻0-213 ∷ CCZ024 ∷ CCZ024 ∷ Bx0-213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CS01⁻ ∷ [])
  b1 = at 4 0 (CZ03 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ []) (sym (wl0247 (lit c4))) ▸
       at 4 1 (Bx⁻2-03 ∷ []) (refl) ▸
       at 7 1 (Bx⁻2-03 ∷ []) (refl) ▸
       at 4 6 (Bx⁻0-213 ∷ []) (refl) ▸
       at 7 1 (Bx2-03 ∷ []) (refl) ▸
       at 10 1 (Bx2-03 ∷ []) (refl) ▸
       at 5 6 (Bx0-213 ∷ []) (refl) ▸
       at 5 0 (CCZ024 ∷ CCZ024 ∷ []) (sym (wp0034 c4)) ▸ done

  b2 : Chain (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻0-213 ∷ CCZ024 ∷ CCZ024 ∷ Bx0-213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CS01⁻ ∷ []) (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻0-213 ∷ CCZ024 ∷ Toff204 ∷ Bx⁻0-213 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CS01⁻ ∷ [])
  b2 = at 6 0 (Toff204 ∷ Toff204 ∷ []) (sym (wp0059 c4)) ▸
       at 7 0 (CZ03 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ []) (sym (wl0247 (lit c4))) ▸
       at 7 1 (Bx⁻2-03 ∷ []) (refl) ▸
       at 10 1 (Bx⁻2-03 ∷ []) (refl) ▸
       at 7 6 (Bx⁻0-213 ∷ []) (refl) ▸
       at 10 1 (Bx2-03 ∷ []) (refl) ▸
       at 13 1 (Bx2-03 ∷ []) (refl) ▸
       at 8 6 (Bx0-213 ∷ []) (refl) ▸ done

  b3 : Chain (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻0-213 ∷ CCZ024 ∷ Toff204 ∷ Bx⁻0-213 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CS01⁻ ∷ []) (Sb⁻2-0-41-3 ∷ X4 ∷ CS03 ∷ CS03⁻ ∷ X4 ∷ Sb2-0-41-3 ∷ CS01⁻ ∷ [])
  b3 = at 8 0 (Toff204 ∷ Toff204 ∷ []) (sym (wp0059 c4)) ▸
       at 9 0 (CCZ024 ∷ CCZ024 ∷ []) (sym (wp0034 c4)) ▸
       at 4 6 (Bx⁻2-0413 ∷ []) (refl) ▸
       at 5 6 (Bx2-0413 ∷ []) (refl) ▸
       at 0 5 (Sb⁻2-0-41-3 ∷ []) (refl) ▸
       at 1 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 1 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 2 0 (CS03 ∷ CS03⁻ ∷ []) (sym (wl0250 (lit c4))) ▸ done

  b4 : Chain (Sb⁻2-0-41-3 ∷ X4 ∷ CS03 ∷ CS03⁻ ∷ X4 ∷ Sb2-0-41-3 ∷ CS01⁻ ∷ []) (Sb⁻2-0-41-3 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ CZ03 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb2-0-41-3 ∷ CS01⁻ ∷ [])
  b4 = at 2 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 3 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 0 (Toff314 ∷ Toff314 ∷ []) (sym (wl0248 (lit c4))) ▸
       at 4 0 (CS03⁻ ∷ CS03 ∷ []) (sym (wl0249 (lit c4))) ▸
       at 4 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 5 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 5 0 (Toff314 ∷ Toff314 ∷ []) (sym (wl0248 (lit c4))) ▸
       at 6 0 (CZ03 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ []) (sym (wl0247 (lit c4))) ▸ done

  b5 : Chain (Sb⁻2-0-41-3 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ CZ03 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb2-0-41-3 ∷ CS01⁻ ∷ []) (Sb⁻2-0-41-3 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻0-213 ∷ CCZ024 ∷ Toff204 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb2-0-41-3 ∷ CS01⁻ ∷ [])
  b5 = at 6 1 (Bx⁻2-03 ∷ []) (refl) ▸
       at 9 1 (Bx⁻2-03 ∷ []) (refl) ▸
       at 6 6 (Bx⁻0-213 ∷ []) (refl) ▸
       at 9 1 (Bx2-03 ∷ []) (refl) ▸
       at 12 1 (Bx2-03 ∷ []) (refl) ▸
       at 7 6 (Bx0-213 ∷ []) (refl) ▸
       at 7 0 (CCZ024 ∷ CCZ024 ∷ []) (sym (wp0034 c4)) ▸
       at 8 0 (Toff204 ∷ Toff204 ∷ []) (sym (wp0059 c4)) ▸ done

  b6 : Chain (Sb⁻2-0-41-3 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻0-213 ∷ CCZ024 ∷ Toff204 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb2-0-41-3 ∷ CS01⁻ ∷ []) (Sb⁻2-0-41-3 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻0-213 ∷ CCZ024 ∷ Toff204 ∷ Bx⁻0-213 ∷ Toff204 ∷ Toff204 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb2-0-41-3 ∷ CS01⁻ ∷ [])
  b6 = at 9 0 (CZ03 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ []) (sym (wl0247 (lit c4))) ▸
       at 9 1 (Bx⁻2-03 ∷ []) (refl) ▸
       at 12 1 (Bx⁻2-03 ∷ []) (refl) ▸
       at 9 6 (Bx⁻0-213 ∷ []) (refl) ▸
       at 12 1 (Bx2-03 ∷ []) (refl) ▸
       at 15 1 (Bx2-03 ∷ []) (refl) ▸
       at 10 6 (Bx0-213 ∷ []) (refl) ▸
       at 10 0 (Toff204 ∷ Toff204 ∷ []) (sym (wp0059 c4)) ▸ done

  b7 : Chain (Sb⁻2-0-41-3 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻0-213 ∷ CCZ024 ∷ Toff204 ∷ Bx⁻0-213 ∷ Toff204 ∷ Toff204 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb2-0-41-3 ∷ CS01⁻ ∷ []) (Sb⁻2-0-41-3 ∷ X4 ∷ Sb⁻2-0-41-3 ∷ X4 ∷ [])
  b7 = at 11 0 (CCZ024 ∷ CCZ024 ∷ []) (sym (wp0034 c4)) ▸
       at 6 6 (Bx⁻2-0413 ∷ []) (refl) ▸
       at 7 6 (Bx2-0413 ∷ []) (refl) ▸
       at 2 5 (Sb⁻2-0-41-3 ∷ []) (refl) ▸
       at 3 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 3 0 (X4 ∷ X4 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 4 4 (CS01 ∷ []) (lem-F5-CS01 c4) ▸
       at 4 2 [] (wl0324 (lit c4)) ▸ done

