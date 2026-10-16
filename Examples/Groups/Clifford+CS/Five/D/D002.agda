{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D002 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0001 ; wl0002 ; wl0003 ; wl0006 ; wl0007 ; wl0008 ; wl0010 ; wl0017 ; wl0019 ; wl0021 ; wl0022 ; wl0023 ; wl0024 ; wl0025 ; wl0031 ; wl0033 ; wl0034 ; wl0047 ; wl0061 ; wl0070 ; wl0084 ; wl0086 ; wl0096 ; wl0099 ; wl0103 ; wl0108 ; wl0111 ; wl0113 ; wl0116 ; wl0121 ; wl0130 ; wl0146 ; wl0149 ; wl0152 ; wl0154 ; wl0155 ; wl0158 ; wl0183 ; wl0212 ; wl0247 ; wl0248 ; wl0249 ; wl0250 ; wl0251 ; wl0252 ; wl0253 ; wl0254 ; wl0255 ; wl0256 ; wl0257 ; wl0258 ; wl0259 ; wl0260 ; wl0261 ; wl0262 ; wl0263 ; wl0264 ; wl0265 ; wl0266 ; wl0267 ; wl0268 ; wl0269 ; wl0270 ; wl0271 ; wl0272 ; wl0273 ; wl0274 ; wl0275 ; wl0276 ; wl0277 ; wp0011 ; wp0012 ; wp0024 ; wp0034 ; wp0055 ; wp0056 ; wp0059 ; wp0060 ; wp0061 ; wp0062 ; wp0063 ; wp0064 ; wp0065 ; wp0066 ; wp0067 ; wp0068 ; wp0069 ; wp0070 ; wp0071 ; wp0072 ; wp0073 ; wp0074 ; wp0075 ; wp0076 ; wp0077 ; wp0078)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-BOXd-BOX ; lem-CS12-beta ; lem-CS20-beta-c ; lem-CSd12-beta ; lem-CX23-beta ; lem-CZ10-beta-c-at011220 ; lem-Cz-beta ; lem-K0-pass ; lem-T-beta ; lem-T312-beta ; lem-T312-beta-at14213243 ; lem-auto-CCZ012-∣-CCZ314-at2332 ; lem-auto-CX01-∣-BOX⟨1·2034⟩ ; lem-beta-T ; lem-beta-T-at2332 ; lem-beta-T-at243243 ; lem-beta-form ; lem-beta-inv-at0210243143 ; lem-beta-mirror ; lem-c124-beta ; lem-c124-beta-at3443 ; lem-sym12 ; lem-sym12-at0110 ; lem-sym12-at0214203143 ; lem-sym12-at1221 ; lem-sym12-at132132 ; lem-sym23 ; lem-sym23-at0214203143 ; lem-sym23-at0214213043 ; lem-sym23-at1221 ; lem-sym34 ; lem-sym34-at01103443 ; lem-sym34-at0214203143 ; lem-sym34-at03102132 ; lem-sym34-at0310213442 ; lem-sym34-at1221 ; lem-sym34-at14213243 ; lem-sym34-at3443)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-nat-1-BOX⟨0·2134⟩ ; lem-nat-1-BOX⟨0·2413⟩ ; lem-nat-1-CCZ024 ; lem-nat-1-CCZ034 ; lem-nat-2-BOX⟨0·1234⟩ ; lem-nat-2-BOX⟨0·1324⟩ ; lem-nat-2-BOX⟨0·3412⟩ ; lem-nat-2-CCZ012 ; lem-nat-2-CCZ013 ; lem-nat-2-CCZ024 ; lem-nat-2-CCZ034 ; lem-nat-2-TOFF012 ; lem-nat-2-TOFF013 ; lem-nat-3-BOX⟨0·1243⟩ ; lem-nat-3-BOX⟨0·1423⟩ ; lem-nat-3-CCZ014 ; lem-nat-3-CCZ024 ; lem-nat-3-TOFF013 ; lem-nat-3-TOFF014)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-0-CCZ024 ; lem-nat-0-CCZ124 ; lem-nat-1-BOX⟨0·1423⟩ ; lem-nat-1-CCZ014 ; lem-nat-1-TOFF301 ; lem-nat-2-BOX⟨0·2413⟩ ; lem-nat-2-CCZ124 ; lem-nat-2-CCZ134 ; lem-nat-2-TOFF201 ; lem-nat-2-TOFF204 ; lem-nat-3-BOX⟨0·1324⟩ ; lem-nat-3-CCZ013 ; lem-nat-3-CCZ023)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-0-CCZ014 ; lem-nat-0-CCZ034 ; lem-nat-0-CCZ134 ; lem-nat-0-TOFF014 ; lem-nat-0-TOFF104 ; lem-nat-0-TOFF304 ; lem-nat-0-TOFF314 ; lem-nat-1-BOX⟨0·1243⟩ ; lem-nat-1-TOFF104 ; lem-nat-2-BOX⟨0·2143⟩)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-0-BOX⟨0·4123⟩ ; lem-nat-0-BOX⟨0·4132⟩ ; lem-nat-1-BOX⟨0·1234⟩ ; lem-nat-1-BOX⟨0·1324⟩ ; lem-nat-1-BOX⟨1·4023⟩ ; lem-nat-1-BOX⟨1·4032⟩ ; lem-nat-1-TOFF013 ; lem-nat-1-TOFF304 ; lem-nat-2-BOX⟨0·2134⟩ ; lem-nat-3-BOX⟨0·3124⟩)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-0-BOX⟨0·1234⟩ ; lem-nat-0-BOX⟨0·1243⟩ ; lem-nat-0-BOX⟨0·1423⟩ ; lem-nat-0-BOX⟨1·0234⟩ ; lem-nat-0-BOX⟨1·0243⟩ ; lem-nat-0-BOX⟨1·0423⟩ ; lem-nat-0-BOX⟨2·4103⟩ ; lem-nat-1-BOX⟨1·0243⟩ ; lem-nat-1-BOX⟨1·0423⟩ ; lem-nat-1-BOX⟨2·0134⟩ ; lem-nat-1-BOX⟨2·0143⟩ ; lem-nat-1-BOX⟨2·0413⟩ ; lem-nat-1-BOX⟨3·0214⟩ ; lem-nat-2-BOX⟨2·0143⟩ ; lem-nat-2-BOX⟨2·0314⟩ ; lem-nat-2-BOX⟨2·0413⟩ ; lem-nat-2-BOX⟨3·0124⟩ ; lem-nat-2-BOX⟨3·0142⟩ ; lem-nat-2-BOX⟨3·0412⟩ ; lem-nat-3-BOX⟨0·1234⟩ ; lem-nat-3-CCZ123 ; lem-nat-3-CCZ124)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-comm-CKd40-CCZ123 ; lem-nat-0-BOX⟨0·1324⟩ ; lem-nat-0-BOX⟨0·2134⟩ ; lem-nat-0-BOX⟨0·2143⟩ ; lem-nat-0-BOX⟨0·2314⟩ ; lem-nat-0-BOX⟨1·2034⟩ ; lem-nat-0-BOX⟨1·2043⟩ ; lem-nat-0-BOX⟨1·2304⟩ ; lem-nat-0-BOX⟨2·4031⟩ ; lem-nat-0-BOX⟨3·0214⟩ ; lem-nat-0-BOX⟨3·1024⟩ ; lem-nat-0-BOX⟨3·1204⟩ ; lem-nat-0-BOXd⟨1·0423⟩ ; lem-nat-0-BOXd⟨1·4023⟩ ; lem-nat-1-BOX⟨0·1342⟩ ; lem-nat-1-BOX⟨0·2143⟩ ; lem-nat-1-BOX⟨0·2314⟩ ; lem-nat-1-BOX⟨0·2341⟩ ; lem-nat-1-BOX⟨1·0324⟩ ; lem-nat-1-BOX⟨1·2034⟩ ; lem-nat-1-BOXd⟨0·2134⟩ ; lem-nat-1-BOXd⟨2·0413⟩ ; lem-nat-1-BOXd⟨2·4013⟩ ; lem-nat-1-CS01 ; lem-nat-1-CS02 ; lem-nat-1-CX10 ; lem-nat-1-CX20 ; lem-nat-1-CZ01 ; lem-nat-1-CZ02 ; lem-nat-2-BOX⟨0·1243⟩ ; lem-nat-2-BOX⟨0·1342⟩ ; lem-nat-2-BOX⟨0·3142⟩ ; lem-nat-2-BOX⟨2·1034⟩ ; lem-nat-2-BOXd⟨0·1324⟩ ; lem-nat-2-BOXd⟨0·3124⟩ ; lem-nat-2-CS12 ; lem-nat-2-CS13 ; lem-nat-2-CSd12 ; lem-nat-2-CSd13 ; lem-nat-2-TOFF314 ; lem-nat-3-BOX⟨0·2134⟩ ; lem-nat-3-BOXd⟨0·1423⟩ ; lem-nat-3-BOXd⟨0·4123⟩ ; lem-nat-3-CS13 ; lem-nat-3-CS14 ; lem-nat-3-CSd13 ; lem-nat-3-CSd14)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-0-BOX⟨1·4032⟩ ; lem-nat-0-BOX⟨2·0413⟩ ; lem-nat-0-BOX⟨2·1403⟩ ; lem-nat-0-BOX⟨2·4013⟩ ; lem-nat-0-BOX⟨2·4130⟩ ; lem-nat-0-CS04 ; lem-nat-0-CS14 ; lem-nat-0-CX40 ; lem-nat-0-SBOX⟨0·1·42·3⟩ ; lem-nat-0-SBOX⟨1·0·42·3⟩ ; lem-nat-1-BOX⟨2·4031⟩ ; lem-nat-1-CS04 ; lem-nat-1-SBOX⟨1·0·42·3⟩ ; lem-nat-1-SBOX⟨2·0·41·3⟩ ; lem-nat-2-BOX⟨0·4123⟩ ; lem-nat-2-BOX⟨0·4132⟩ ; lem-nat-2-SBOX⟨0·1·23·4⟩ ; lem-nat-2-SBOX⟨0·1·32·4⟩ ; lem-nat-3-CS23 ; lem-nat-3-CS24 ; lem-nat-3-CX42 ; lem-nat-3-SBOX⟨0·1·32·4⟩ ; lem-nat-3-SBOX⟨0·1·42·3⟩)
-- auto CZ01 | BOX(1;2034): 3 steps
lem-auto-CZ01-∣-BOX⟨1·2034⟩ : Ws → ⟪ (CZ01 ∷ Bx1-2034 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2034 ∷ CZ01 ∷ []) ⟫ʷ
lem-auto-CZ01-∣-BOX⟨1·2034⟩ c4 = run b0
  where
  b0 : Chain (CZ01 ∷ Bx1-2034 ∷ []) (Bx1-2034 ∷ CZ01 ∷ [])
  b0 = at 0 1 (CZ01 ∷ []) (wl0252 (lit c4)) ▸
       at 0 2 (Bx1-2034 ∷ CZ01 ∷ []) (lem-CZ10-beta-c-at011220 c4) ▸
       at 1 1 (CZ01 ∷ []) (wl0252 (lit c4)) ▸ done


-- auto CZ01 CX01 | BOX(1;2034): 2 steps
lem-auto-CZ01-CX01-∣-BOX⟨1·2034⟩ : Ws → ⟪ (CZ01 ∷ CX01 ∷ Bx1-2034 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2034 ∷ CZ01 ∷ CX01 ∷ []) ⟫ʷ
lem-auto-CZ01-CX01-∣-BOX⟨1·2034⟩ c4 = run b0
  where
  b0 : Chain (CZ01 ∷ CX01 ∷ Bx1-2034 ∷ []) (Bx1-2034 ∷ CZ01 ∷ CX01 ∷ [])
  b0 = at 1 2 (Bx1-2034 ∷ CX01 ∷ []) (lem-auto-CX01-∣-BOX⟨1·2034⟩ c4) ▸
       at 0 2 (Bx1-2034 ∷ CZ01 ∷ []) (lem-auto-CZ01-∣-BOX⟨1·2034⟩ c4) ▸ done


-- c124-beta @2332: 7 steps
lem-c124-beta-at2332 : Ws → ⟪ (CCZ134 ∷ Bx0-1324 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ CCZ134 ∷ []) ⟫ʷ
lem-c124-beta-at2332 c4 = run b0
  where
  b0 : Chain (CCZ134 ∷ Bx0-1324 ∷ []) (Bx0-1324 ∷ CCZ134 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 (lit c4)) ▸
       at 2 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ (lit c4)) ▸
       at 1 2 (Bx0-1234 ∷ CCZ124 ∷ []) (lem-c124-beta c4) ▸
       at 0 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ (lit c4)) ▸
       at 1 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- c124-beta @122331: 7 steps
lem-c124-beta-at122331 : Ws → ⟪ (CCZ234 ∷ Bx0-2314 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2314 ∷ CCZ234 ∷ []) ⟫ʷ
lem-c124-beta-at122331 c4 = run b0
  where
  b0 : Chain (CCZ234 ∷ Bx0-2314 ∷ []) (Bx0-2314 ∷ CCZ234 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0034 (lit c4))) ▸
       at 2 2 (Bx0-1324 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2314⟩ (lit c4)) ▸
       at 1 2 (Bx0-1324 ∷ CCZ134 ∷ []) (lem-c124-beta-at2332 c4) ▸
       at 0 2 (Bx0-2314 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1324⟩ (lit c4)) ▸
       at 1 2 (CCZ234 ∷ Sw12 ∷ []) (sym (wl0084 (lit c4))) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- sym23 @2332: 5 steps
lem-sym23-at2332 : Ws → ⟪ (Bx0-1324 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-sym23-at2332 c4 = run b0
  where
  b0 : Chain (Bx0-1324 ∷ []) (Bx0-1234 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ (lit c4)) ▸
       at 1 1 (Bx0-1324 ∷ []) (lem-sym23 c4) ▸
       at 0 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ (lit c4)) ▸
       at 1 2 [] (wl0006 (lit c4)) ▸ done


-- sym23 @122331: 5 steps
lem-sym23-at122331 : Ws → ⟪ (Bx0-2314 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ []) ⟫ʷ
lem-sym23-at122331 c4 = run b0
  where
  b0 : Chain (Bx0-2314 ∷ []) (Bx0-2134 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx0-1324 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2314⟩ (lit c4)) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym23-at2332 c4) ▸
       at 0 2 (Bx0-2134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1234⟩ (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- auto BOX(0;1234) | CCZ234: 5 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ234 : Ws → ⟪ (Bx0-1234 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ234 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ CCZ234 ∷ []) (CCZ234 ∷ Bx0-1234 ∷ [])
  b0 = at 0 1 (Bx0-2134 ∷ []) (lem-sym12 c4) ▸
       at 0 1 (Bx0-2314 ∷ []) (lem-sym23-at1221 c4) ▸
       at 0 2 (CCZ234 ∷ Bx0-2314 ∷ []) (sym (lem-c124-beta-at122331 c4)) ▸
       at 1 1 (Bx0-2134 ∷ []) (lem-sym23-at122331 c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym12-at1221 c4) ▸ done


-- auto CZ01 CX01 | BOX(1;2034) @0110: 9 steps
lem-auto-CZ01-CX01-∣-BOX⟨1·2034⟩-at0110 : Ws → ⟪ (CZ01 ∷ CX10 ∷ Bx0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ CZ01 ∷ CX10 ∷ []) ⟫ʷ
lem-auto-CZ01-CX01-∣-BOX⟨1·2034⟩-at0110 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CZ01 ∷ CX10 ∷ Bx0-2134 ∷ []) (Bx0-2134 ∷ CZ01 ∷ CX10 ∷ Sw01 ∷ Sw01 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (CZ01 ∷ Sw01 ∷ []) (sym (wl0130 (lit c4))) ▸
       at 2 2 (CX01 ∷ Sw01 ∷ []) (sym (wl0251 (lit c4))) ▸
       at 3 2 (Bx1-2034 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·2134⟩ (lit c4)) ▸
       at 1 3 (Bx1-2034 ∷ CZ01 ∷ CX01 ∷ []) (lem-auto-CZ01-CX01-∣-BOX⟨1·2034⟩ c4) ▸
       at 0 2 (Bx0-2134 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·2034⟩ (lit c4)) ▸
       at 1 2 (CZ01 ∷ Sw01 ∷ []) (sym (wl0130 (lit c4))) ▸
       at 2 2 (CX10 ∷ Sw01 ∷ []) (sym (wl0070 (lit c4))) ▸ done

  b1 : Chain (Bx0-2134 ∷ CZ01 ∷ CX10 ∷ Sw01 ∷ Sw01 ∷ []) (Bx0-2134 ∷ CZ01 ∷ CX10 ∷ [])
  b1 = at 3 2 [] (wl0002 (lit c4)) ▸ done


-- auto CZ01 CX01 | BOX(1;2034) @021021: 9 steps
lem-auto-CZ01-CX01-∣-BOX⟨1·2034⟩-at021021 : Ws → ⟪ (CZ02 ∷ CX20 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CZ02 ∷ CX20 ∷ []) ⟫ʷ
lem-auto-CZ01-CX01-∣-BOX⟨1·2034⟩-at021021 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CZ02 ∷ CX20 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CZ02 ∷ CX20 ∷ Sw12 ∷ Sw12 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CZ01 ∷ Sw12 ∷ []) (lem-nat-1-CZ02 (lit c4)) ▸
       at 2 2 (CX10 ∷ Sw12 ∷ []) (lem-nat-1-CX20 (lit c4)) ▸
       at 3 2 (Bx0-2134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1234⟩ (lit c4)) ▸
       at 1 3 (Bx0-2134 ∷ CZ01 ∷ CX10 ∷ []) (lem-auto-CZ01-CX01-∣-BOX⟨1·2034⟩-at0110 c4) ▸
       at 0 2 (Bx0-1234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2134⟩ (lit c4)) ▸
       at 1 2 (CZ02 ∷ Sw12 ∷ []) (lem-nat-1-CZ01 (lit c4)) ▸
       at 2 2 (CX20 ∷ Sw12 ∷ []) (lem-nat-1-CX10 (lit c4)) ▸ done

  b1 : Chain (Bx0-1234 ∷ CZ02 ∷ CX20 ∷ Sw12 ∷ Sw12 ∷ []) (Bx0-1234 ∷ CZ02 ∷ CX20 ∷ [])
  b1 = at 3 2 [] (wl0001 (lit c4)) ▸ done


-- X1-beta: 10 steps
lem-X1-beta : Ws → ⟪ (X1 ∷ Bx0-1234 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-X1-beta c4 = trans (run b0) (run b1)
  where
  b0 : Chain (X1 ∷ Bx0-1234 ∷ X1 ∷ []) (Bx0-1234 ∷ CZ02 ∷ CX20 ∷ CCZ034 ∷ CX20 ∷ CZ02 ∷ CCZ034 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) (lem-beta-form c4) ▸
       at 0 3 (CZ02 ∷ CX20 ∷ Toff012 ∷ CCZ012 ∷ X1 ∷ []) (sym (wl0253 (lit c4))) ▸
       at 4 2 (CCZ034 ∷ X1 ∷ []) (sym (wp0060 c4)) ▸
       at 5 3 (CCZ012 ∷ Toff012 ∷ CX20 ∷ CZ02 ∷ X1 ∷ []) (sym (wl0254 (lit c4))) ▸
       at 9 3 (CCZ034 ∷ []) (sym (wp0061 c4)) ▸
       at 7 0 (CCZ034 ∷ CCZ034 ∷ []) (sym (wp0024 c4)) ▸
       at 2 6 (Bx0-1234 ∷ []) (sym (lem-beta-mirror c4)) ▸
       at 0 3 (Bx0-1234 ∷ CZ02 ∷ CX20 ∷ []) (lem-auto-CZ01-CX01-∣-BOX⟨1·2034⟩-at021021 c4) ▸ done

  b1 : Chain (Bx0-1234 ∷ CZ02 ∷ CX20 ∷ CCZ034 ∷ CX20 ∷ CZ02 ∷ CCZ034 ∷ []) (CCZ234 ∷ Bx0-1234 ∷ [])
  b1 = at 1 6 (CCZ234 ∷ []) (sym (wp0062 c4)) ▸
       at 0 2 (CCZ234 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ234 c4) ▸ done


-- sym34 @2332: 5 steps
lem-sym34-at2332 : Ws → ⟪ (Bx0-1324 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1342 ∷ []) ⟫ʷ
lem-sym34-at2332 c4 = run b0
  where
  b0 : Chain (Bx0-1324 ∷ []) (Bx0-1342 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ (lit c4)) ▸
       at 1 1 (Bx0-1243 ∷ []) (lem-sym34 c4) ▸
       at 0 2 (Bx0-1342 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1243⟩ (lit c4)) ▸
       at 1 2 [] (wl0006 (lit c4)) ▸ done


-- sym12 @3443: 5 steps
lem-sym12-at3443 : Ws → ⟪ (Bx0-1243 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2143 ∷ []) ⟫ʷ
lem-sym12-at3443 c4 = run b0
  where
  b0 : Chain (Bx0-1243 ∷ []) (Bx0-2143 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Bx0-1234 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1243⟩ (lit c4)) ▸
       at 1 1 (Bx0-2134 ∷ []) (lem-sym12 c4) ▸
       at 0 2 (Bx0-2143 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·2134⟩ (lit c4)) ▸
       at 1 2 [] (wl0007 (lit c4)) ▸ done


-- sym12 @233442: 5 steps
lem-sym12-at233442 : Ws → ⟪ (Bx0-1342 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3142 ∷ []) ⟫ʷ
lem-sym12-at233442 c4 = run b0
  where
  b0 : Chain (Bx0-1342 ∷ []) (Bx0-3142 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx0-1243 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1342⟩ (lit c4)) ▸
       at 1 1 (Bx0-2143 ∷ []) (lem-sym12-at3443 c4) ▸
       at 0 2 (Bx0-3142 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·2143⟩ (lit c4)) ▸
       at 1 2 [] (wl0006 (lit c4)) ▸ done


-- sym23 @3443: 5 steps
lem-sym23-at3443 : Ws → ⟪ (Bx0-1243 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ []) ⟫ʷ
lem-sym23-at3443 c4 = run b0
  where
  b0 : Chain (Bx0-1243 ∷ []) (Bx0-1423 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Bx0-1234 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1243⟩ (lit c4)) ▸
       at 1 1 (Bx0-1324 ∷ []) (lem-sym23 c4) ▸
       at 0 2 (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ (lit c4)) ▸
       at 1 2 [] (wl0007 (lit c4)) ▸ done


-- sym23 @12213443: 5 steps
lem-sym23-at12213443 : Ws → ⟪ (Bx0-2143 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2413 ∷ []) ⟫ʷ
lem-sym23-at12213443 c4 = run b0
  where
  b0 : Chain (Bx0-2143 ∷ []) (Bx0-2413 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx0-1243 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2143⟩ (lit c4)) ▸
       at 1 1 (Bx0-1423 ∷ []) (lem-sym23-at3443 c4) ▸
       at 0 2 (Bx0-2413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1423⟩ (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- sym23 @13213442: 5 steps
lem-sym23-at13213442 : Ws → ⟪ (Bx0-3142 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3412 ∷ []) ⟫ʷ
lem-sym23-at13213442 c4 = run b0
  where
  b0 : Chain (Bx0-3142 ∷ []) (Bx0-3412 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx0-2143 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3142⟩ (lit c4)) ▸
       at 1 1 (Bx0-2413 ∷ []) (lem-sym23-at12213443 c4) ▸
       at 0 2 (Bx0-3412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·2413⟩ (lit c4)) ▸
       at 1 2 [] (wl0006 (lit c4)) ▸ done


-- Cz-beta @2332: 7 steps
lem-Cz-beta-at2332 : Ws → ⟪ (CCZ013 ∷ Bx0-1324 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ CCZ013 ∷ []) ⟫ʷ
lem-Cz-beta-at2332 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ Bx0-1324 ∷ []) (Bx0-1324 ∷ CCZ013 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 (lit c4)) ▸
       at 2 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ (lit c4)) ▸
       at 1 2 (Bx0-1234 ∷ CCZ012 ∷ []) (lem-Cz-beta c4) ▸
       at 0 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ (lit c4)) ▸
       at 1 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- Cz-beta @243243: 7 steps
lem-Cz-beta-at243243 : Ws → ⟪ (CCZ014 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ CCZ014 ∷ []) ⟫ʷ
lem-Cz-beta-at243243 c4 = run b0
  where
  b0 : Chain (CCZ014 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ CCZ014 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 (lit c4)) ▸
       at 2 2 (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ (lit c4)) ▸
       at 1 2 (Bx0-1324 ∷ CCZ013 ∷ []) (lem-Cz-beta-at2332 c4) ▸
       at 0 2 (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ (lit c4)) ▸
       at 1 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- Cz-beta @12243143: 7 steps
lem-Cz-beta-at12243143 : Ws → ⟪ (CCZ024 ∷ Bx0-2413 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2413 ∷ CCZ024 ∷ []) ⟫ʷ
lem-Cz-beta-at12243143 c4 = run b0
  where
  b0 : Chain (CCZ024 ∷ Bx0-2413 ∷ []) (Bx0-2413 ∷ CCZ024 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 (lit c4)) ▸
       at 2 2 (Bx0-1423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2413⟩ (lit c4)) ▸
       at 1 2 (Bx0-1423 ∷ CCZ014 ∷ []) (lem-Cz-beta-at243243 c4) ▸
       at 0 2 (Bx0-2413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1423⟩ (lit c4)) ▸
       at 1 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- Cz-beta @13243142: 7 steps
lem-Cz-beta-at13243142 : Ws → ⟪ (CCZ034 ∷ Bx0-3412 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3412 ∷ CCZ034 ∷ []) ⟫ʷ
lem-Cz-beta-at13243142 c4 = run b0
  where
  b0 : Chain (CCZ034 ∷ Bx0-3412 ∷ []) (Bx0-3412 ∷ CCZ034 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 (lit c4)) ▸
       at 2 2 (Bx0-2413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3412⟩ (lit c4)) ▸
       at 1 2 (Bx0-2413 ∷ CCZ024 ∷ []) (lem-Cz-beta-at12243143 c4) ▸
       at 0 2 (Bx0-3412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·2413⟩ (lit c4)) ▸
       at 1 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- sym23 @243243: 5 steps
lem-sym23-at243243 : Ws → ⟪ (Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1243 ∷ []) ⟫ʷ
lem-sym23-at243243 c4 = run b0
  where
  b0 : Chain (Bx0-1423 ∷ []) (Bx0-1243 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ (lit c4)) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym23-at2332 c4) ▸
       at 0 2 (Bx0-1243 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1234⟩ (lit c4)) ▸
       at 1 2 [] (wl0007 (lit c4)) ▸ done


-- sym23 @12243143: 5 steps
lem-sym23-at12243143 : Ws → ⟪ (Bx0-2413 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2143 ∷ []) ⟫ʷ
lem-sym23-at12243143 c4 = run b0
  where
  b0 : Chain (Bx0-2413 ∷ []) (Bx0-2143 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx0-1423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2413⟩ (lit c4)) ▸
       at 1 1 (Bx0-1243 ∷ []) (lem-sym23-at243243 c4) ▸
       at 0 2 (Bx0-2143 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1243⟩ (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- sym23 @13243142: 5 steps
lem-sym23-at13243142 : Ws → ⟪ (Bx0-3412 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3142 ∷ []) ⟫ʷ
lem-sym23-at13243142 c4 = run b0
  where
  b0 : Chain (Bx0-3412 ∷ []) (Bx0-3142 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx0-2413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3412⟩ (lit c4)) ▸
       at 1 1 (Bx0-2143 ∷ []) (lem-sym23-at12243143 c4) ▸
       at 0 2 (Bx0-3142 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·2143⟩ (lit c4)) ▸
       at 1 2 [] (wl0006 (lit c4)) ▸ done


-- sym34 @12213443: 5 steps
lem-sym34-at12213443 : Ws → ⟪ (Bx0-2143 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ []) ⟫ʷ
lem-sym34-at12213443 c4 = run b0
  where
  b0 : Chain (Bx0-2143 ∷ []) (Bx0-2134 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx0-1243 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2143⟩ (lit c4)) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym34-at3443 c4) ▸
       at 0 2 (Bx0-2134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1234⟩ (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- sym34 @13213442: 5 steps
lem-sym34-at13213442 : Ws → ⟪ (Bx0-3142 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3124 ∷ []) ⟫ʷ
lem-sym34-at13213442 c4 = run b0
  where
  b0 : Chain (Bx0-3142 ∷ []) (Bx0-3124 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx0-2143 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3142⟩ (lit c4)) ▸
       at 1 1 (Bx0-2134 ∷ []) (lem-sym34-at12213443 c4) ▸
       at 0 2 (Bx0-3124 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·2134⟩ (lit c4)) ▸
       at 1 2 [] (wl0006 (lit c4)) ▸ done


-- auto BOX(0;1234) | CCZ034: 9 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ034 : Ws → ⟪ (Bx0-1234 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ034 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-1234 ∷ CCZ034 ∷ []) (CCZ034 ∷ Bx0-1324 ∷ [])
  b0 = at 0 1 (Bx0-1324 ∷ []) (lem-sym23 c4) ▸
       at 0 1 (Bx0-1342 ∷ []) (lem-sym34-at2332 c4) ▸
       at 0 1 (Bx0-3142 ∷ []) (lem-sym12-at233442 c4) ▸
       at 0 1 (Bx0-3412 ∷ []) (lem-sym23-at13213442 c4) ▸
       at 0 2 (CCZ034 ∷ Bx0-3412 ∷ []) (sym (lem-Cz-beta-at13243142 c4)) ▸
       at 1 1 (Bx0-3142 ∷ []) (lem-sym23-at13243142 c4) ▸
       at 1 1 (Bx0-3124 ∷ []) (lem-sym34-at13213442 c4) ▸
       at 1 1 (Bx0-1324 ∷ []) (lem-sym12-at132132 c4) ▸ done

  b1 : Chain (CCZ034 ∷ Bx0-1324 ∷ []) (CCZ034 ∷ Bx0-1234 ∷ [])
  b1 = at 1 1 (Bx0-1234 ∷ []) (lem-sym23-at2332 c4) ▸ done


-- auto BOX(0;1234) | CCZ342: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ342 : Ws → ⟪ (Bx0-1234 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ342 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ CCZ234 ∷ []) (CCZ234 ∷ Bx0-1234 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ []) (wl0255 (lit c4)) ▸
       at 0 1 (Bx0-2134 ∷ []) (lem-sym12 c4) ▸
       at 0 1 (Bx0-2314 ∷ []) (lem-sym23-at1221 c4) ▸
       at 0 2 (CCZ234 ∷ Bx0-2314 ∷ []) (sym (lem-c124-beta-at122331 c4)) ▸
       at 1 1 (Bx0-2134 ∷ []) (lem-sym23-at122331 c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym12-at1221 c4) ▸
       at 0 1 (CCZ234 ∷ []) (wl0255 (lit c4)) ▸ done


-- auto BOX(0;1234) | TOFF012: 1 steps
lem-auto-BOX⟨0·1234⟩-∣-TOFF012 : Ws → ⟪ (Bx0-1234 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-TOFF012 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ Toff012 ∷ []) (Toff012 ∷ Bx0-1234 ∷ [])
  b0 = at 0 2 (Toff012 ∷ Bx0-1234 ∷ []) (sym (lem-T-beta c4)) ▸ done


-- auto BOX(0;1234) | CCZ103: 5 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ103 : Ws → ⟪ (Bx0-1234 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ103 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ CCZ013 ∷ []) (CCZ013 ∷ Bx0-1234 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ []) (wl0256 (lit c4)) ▸
       at 0 1 (Bx0-1324 ∷ []) (lem-sym23 c4) ▸
       at 0 2 (CCZ013 ∷ Bx0-1324 ∷ []) (sym (lem-Cz-beta-at2332 c4)) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym23-at2332 c4) ▸
       at 0 1 (CCZ013 ∷ []) (wl0256 (lit c4)) ▸ done


-- beta-T @122331: 8 steps
lem-beta-T-at122331 : Ws → ⟪ (Bx0-2314 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ []) ⟫ʷ
lem-beta-T-at122331 c4 = run b0
  where
  b0 : Chain (Bx0-2314 ∷ []) (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx0-1324 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2314⟩ (lit c4)) ▸
       at 1 1 (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) (lem-beta-T-at2332 c4) ▸
       at 0 2 (Toff023 ∷ Sw12 ∷ []) (lem-nat-1-TOFF013 (lit c4)) ▸
       at 1 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 (lit c4)) ▸
       at 2 2 (Toff023 ∷ Sw12 ∷ []) (lem-nat-1-TOFF013 (lit c4)) ▸
       at 3 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 (lit c4)) ▸
       at 4 2 [] (wl0001 (lit c4)) ▸ done


-- beta-T @0110243243: 8 steps
lem-beta-T-at0110243243 : Ws → ⟪ (Bx1-0423 ∷ []) ⟫ʷ ≈ ⟪ (Toff104 ∷ CCZ123 ∷ Toff104 ∷ CCZ123 ∷ []) ⟫ʷ
lem-beta-T-at0110243243 c4 = run b0
  where
  b0 : Chain (Bx1-0423 ∷ []) (Toff104 ∷ CCZ123 ∷ Toff104 ∷ CCZ123 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4)) ▸
       at 1 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-beta-T-at243243 c4) ▸
       at 0 2 (Toff104 ∷ Sw01 ∷ []) (lem-nat-0-TOFF014 (lit c4)) ▸
       at 1 2 (CCZ123 ∷ Sw01 ∷ []) (sym (wl0103 (lit c4))) ▸
       at 2 2 (Toff104 ∷ Sw01 ∷ []) (lem-nat-0-TOFF014 (lit c4)) ▸
       at 3 2 (CCZ123 ∷ Sw01 ∷ []) (sym (wl0103 (lit c4))) ▸
       at 4 2 [] (wl0002 (lit c4)) ▸ done


-- sym23 @0110243243: 5 steps
lem-sym23-at0110243243 : Ws → ⟪ (Bx1-0423 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0243 ∷ []) ⟫ʷ
lem-sym23-at0110243243 c4 = run b0
  where
  b0 : Chain (Bx1-0423 ∷ []) (Bx1-0243 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4)) ▸
       at 1 1 (Bx0-1243 ∷ []) (lem-sym23-at243243 c4) ▸
       at 0 2 (Bx1-0243 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1243⟩ (lit c4)) ▸
       at 1 2 [] (wl0002 (lit c4)) ▸ done


-- sym23 @011220: 5 steps
lem-sym23-at011220 : Ws → ⟪ (Bx1-2034 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2304 ∷ []) ⟫ʷ
lem-sym23-at011220 c4 = run b0
  where
  b0 : Chain (Bx1-2034 ∷ []) (Bx1-2304 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx0-2134 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·2034⟩ (lit c4)) ▸
       at 1 1 (Bx0-2314 ∷ []) (lem-sym23-at1221 c4) ▸
       at 0 2 (Bx1-2304 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·2314⟩ (lit c4)) ▸
       at 1 2 [] (wl0002 (lit c4)) ▸ done


-- T312-beta @2332: 8 steps
lem-T312-beta-at2332 : Ws → ⟪ (Toff213 ∷ Bx0-1324 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ CCZ134 ∷ []) ⟫ʷ
lem-T312-beta-at2332 c4 = run b0
  where
  b0 : Chain (Toff213 ∷ Bx0-1324 ∷ Toff213 ∷ []) (Bx0-1324 ∷ CCZ134 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Toff312 ∷ Sw23 ∷ []) (wl0158 (lit c4)) ▸
       at 2 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ (lit c4)) ▸
       at 3 2 (Toff312 ∷ Sw23 ∷ []) (wl0158 (lit c4)) ▸
       at 1 3 (Bx0-1234 ∷ CCZ124 ∷ []) (lem-T312-beta c4) ▸
       at 0 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ (lit c4)) ▸
       at 1 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- T312-beta @122331: 8 steps
lem-T312-beta-at122331 : Ws → ⟪ (Toff123 ∷ Bx0-2314 ∷ Toff123 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2314 ∷ CCZ234 ∷ []) ⟫ʷ
lem-T312-beta-at122331 c4 = run b0
  where
  b0 : Chain (Toff123 ∷ Bx0-2314 ∷ Toff123 ∷ []) (Bx0-2314 ∷ CCZ234 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Toff213 ∷ Sw12 ∷ []) (wl0146 (lit c4)) ▸
       at 2 2 (Bx0-1324 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2314⟩ (lit c4)) ▸
       at 3 2 (Toff213 ∷ Sw12 ∷ []) (wl0146 (lit c4)) ▸
       at 1 3 (Bx0-1324 ∷ CCZ134 ∷ []) (lem-T312-beta-at2332 c4) ▸
       at 0 2 (Bx0-2314 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1324⟩ (lit c4)) ▸
       at 1 2 (CCZ234 ∷ Sw12 ∷ []) (sym (wl0084 (lit c4))) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- T312-beta @01122330: 8 steps
lem-T312-beta-at01122330 : Ws → ⟪ (Toff023 ∷ Bx1-2304 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2304 ∷ CCZ234 ∷ []) ⟫ʷ
lem-T312-beta-at01122330 c4 = run b0
  where
  b0 : Chain (Toff023 ∷ Bx1-2304 ∷ Toff023 ∷ []) (Bx1-2304 ∷ CCZ234 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Toff123 ∷ Sw01 ∷ []) (wl0108 (lit c4)) ▸
       at 2 2 (Bx0-2314 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·2304⟩ (lit c4)) ▸
       at 3 2 (Toff123 ∷ Sw01 ∷ []) (wl0108 (lit c4)) ▸
       at 1 3 (Bx0-2314 ∷ CCZ234 ∷ []) (lem-T312-beta-at122331 c4) ▸
       at 0 2 (Bx1-2304 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·2314⟩ (lit c4)) ▸
       at 1 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- sym23 @01122330: 5 steps
lem-sym23-at01122330 : Ws → ⟪ (Bx1-2304 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2034 ∷ []) ⟫ʷ
lem-sym23-at01122330 c4 = run b0
  where
  b0 : Chain (Bx1-2304 ∷ []) (Bx1-2034 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx0-2314 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·2304⟩ (lit c4)) ▸
       at 1 1 (Bx0-2134 ∷ []) (lem-sym23-at122331 c4) ▸
       at 0 2 (Bx1-2034 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·2134⟩ (lit c4)) ▸
       at 1 2 [] (wl0002 (lit c4)) ▸ done


-- sym34 @011220: 5 steps
lem-sym34-at011220 : Ws → ⟪ (Bx1-2034 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2043 ∷ []) ⟫ʷ
lem-sym34-at011220 c4 = run b0
  where
  b0 : Chain (Bx1-2034 ∷ []) (Bx1-2043 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx0-2134 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·2034⟩ (lit c4)) ▸
       at 1 1 (Bx0-2143 ∷ []) (lem-sym34-at1221 c4) ▸
       at 0 2 (Bx1-2043 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·2143⟩ (lit c4)) ▸
       at 1 2 [] (wl0002 (lit c4)) ▸ done


-- sym12 @12213443: 5 steps
lem-sym12-at12213443 : Ws → ⟪ (Bx0-2143 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1243 ∷ []) ⟫ʷ
lem-sym12-at12213443 c4 = run b0
  where
  b0 : Chain (Bx0-2143 ∷ []) (Bx0-1243 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx0-1243 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2143⟩ (lit c4)) ▸
       at 1 1 (Bx0-2143 ∷ []) (lem-sym12-at3443 c4) ▸
       at 0 2 (Bx0-1243 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2143⟩ (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- sym12 @0112203443: 5 steps
lem-sym12-at0112203443 : Ws → ⟪ (Bx1-2043 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0243 ∷ []) ⟫ʷ
lem-sym12-at0112203443 c4 = run b0
  where
  b0 : Chain (Bx1-2043 ∷ []) (Bx1-0243 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx0-2143 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·2043⟩ (lit c4)) ▸
       at 1 1 (Bx0-1243 ∷ []) (lem-sym12-at12213443 c4) ▸
       at 0 2 (Bx1-0243 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1243⟩ (lit c4)) ▸
       at 1 2 [] (wl0002 (lit c4)) ▸ done


-- sym23 @01103443: 5 steps
lem-sym23-at01103443 : Ws → ⟪ (Bx1-0243 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0423 ∷ []) ⟫ʷ
lem-sym23-at01103443 c4 = run b0
  where
  b0 : Chain (Bx1-0243 ∷ []) (Bx1-0423 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx0-1243 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0243⟩ (lit c4)) ▸
       at 1 1 (Bx0-1423 ∷ []) (lem-sym23-at3443 c4) ▸
       at 0 2 (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ (lit c4)) ▸
       at 1 2 [] (wl0002 (lit c4)) ▸ done


-- auto BOX(0;1234) | CCZ034 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ034-at2332 : Ws → ⟪ (Bx0-1324 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ034-at2332 c4 = run b0
  where
  b0 : Chain (Bx0-1324 ∷ CCZ024 ∷ []) (CCZ024 ∷ Bx0-1324 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ (lit c4)) ▸
       at 2 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 (lit c4)) ▸
       at 1 2 (CCZ034 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ034 c4) ▸
       at 0 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 (lit c4)) ▸
       at 1 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto BOX(0;1234) | CCZ034 @243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ034-at243243 : Ws → ⟪ (Bx0-1423 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ Bx0-1423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ034-at243243 c4 = run b0
  where
  b0 : Chain (Bx0-1423 ∷ CCZ023 ∷ []) (CCZ023 ∷ Bx0-1423 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ (lit c4)) ▸
       at 2 2 (CCZ024 ∷ Sw34 ∷ []) (lem-nat-3-CCZ023 (lit c4)) ▸
       at 1 2 (CCZ024 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ034-at2332 c4) ▸
       at 0 2 (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 (lit c4)) ▸
       at 1 2 (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto BOX(0;1234) | CCZ034 @0110243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ034-at0110243243 : Ws → ⟪ (Bx1-0423 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Bx1-0423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ034-at0110243243 c4 = run b0
  where
  b0 : Chain (Bx1-0423 ∷ CCZ123 ∷ []) (CCZ123 ∷ Bx1-0423 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4)) ▸
       at 2 2 (CCZ023 ∷ Sw01 ∷ []) (sym (wl0003 (lit c4))) ▸
       at 1 2 (CCZ023 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ034-at243243 c4) ▸
       at 0 2 (CCZ123 ∷ Sw01 ∷ []) (sym (wl0103 (lit c4))) ▸
       at 1 2 (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto CCZ012 | CCZ314 @243243: 7 steps
lem-auto-CCZ012-∣-CCZ314-at243243 : Ws → ⟪ (CCZ014 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CCZ014 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-CCZ314-at243243 c4 = run b0
  where
  b0 : Chain (CCZ014 ∷ CCZ123 ∷ []) (CCZ123 ∷ CCZ014 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 (lit c4)) ▸
       at 2 2 (CCZ124 ∷ Sw34 ∷ []) (lem-nat-3-CCZ123 (lit c4)) ▸
       at 1 2 (CCZ124 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-CCZ314-at2332 c4) ▸
       at 0 2 (CCZ123 ∷ Sw34 ∷ []) (lem-nat-3-CCZ124 (lit c4)) ▸
       at 1 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto CCZ012 | CCZ314 @12243143: 7 steps
lem-auto-CCZ012-∣-CCZ314-at12243143 : Ws → ⟪ (CCZ024 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CCZ024 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-CCZ314-at12243143 c4 = run b0
  where
  b0 : Chain (CCZ024 ∷ CCZ123 ∷ []) (CCZ123 ∷ CCZ024 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 (lit c4)) ▸
       at 2 2 (CCZ123 ∷ Sw12 ∷ []) (sym (wl0111 (lit c4))) ▸
       at 1 2 (CCZ123 ∷ CCZ014 ∷ []) (lem-auto-CCZ012-∣-CCZ314-at243243 c4) ▸
       at 0 2 (CCZ123 ∷ Sw12 ∷ []) (sym (wl0111 (lit c4))) ▸
       at 1 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto BOX(0;1234) | CCZ342 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ342-at2332 : Ws → ⟪ (Bx0-1324 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ342-at2332 c4 = run b0
  where
  b0 : Chain (Bx0-1324 ∷ CCZ234 ∷ []) (CCZ234 ∷ Bx0-1324 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ (lit c4)) ▸
       at 2 2 (CCZ234 ∷ Sw23 ∷ []) (sym (wl0086 (lit c4))) ▸
       at 1 2 (CCZ234 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ342 c4) ▸
       at 0 2 (CCZ234 ∷ Sw23 ∷ []) (sym (wl0086 (lit c4))) ▸
       at 1 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto BOX(0;1234) | CCZ342 @243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ342-at243243 : Ws → ⟪ (Bx0-1423 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Bx0-1423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ342-at243243 c4 = run b0
  where
  b0 : Chain (Bx0-1423 ∷ CCZ234 ∷ []) (CCZ234 ∷ Bx0-1423 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ (lit c4)) ▸
       at 2 2 (CCZ234 ∷ Sw34 ∷ []) (sym (wl0155 (lit c4))) ▸
       at 1 2 (CCZ234 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ342-at2332 c4) ▸
       at 0 2 (CCZ234 ∷ Sw34 ∷ []) (sym (wl0155 (lit c4))) ▸
       at 1 2 (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto BOX(0;1234) | CCZ342 @0110243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ342-at0110243243 : Ws → ⟪ (Bx1-0423 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Bx1-0423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ342-at0110243243 c4 = run b0
  where
  b0 : Chain (Bx1-0423 ∷ CCZ234 ∷ []) (CCZ234 ∷ Bx1-0423 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4)) ▸
       at 2 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 1 2 (CCZ234 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ342-at243243 c4) ▸
       at 0 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 1 2 (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto BOX(0;1234) | TOFF012 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-TOFF012-at2332 : Ws → ⟪ (Bx0-1324 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-TOFF012-at2332 c4 = run b0
  where
  b0 : Chain (Bx0-1324 ∷ Toff013 ∷ []) (Toff013 ∷ Bx0-1324 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ (lit c4)) ▸
       at 2 2 (Toff012 ∷ Sw23 ∷ []) (lem-nat-2-TOFF013 (lit c4)) ▸
       at 1 2 (Toff012 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-TOFF012 c4) ▸
       at 0 2 (Toff013 ∷ Sw23 ∷ []) (lem-nat-2-TOFF012 (lit c4)) ▸
       at 1 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto BOX(0;1234) | TOFF012 @243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-TOFF012-at243243 : Ws → ⟪ (Bx0-1423 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ Bx0-1423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-TOFF012-at243243 c4 = run b0
  where
  b0 : Chain (Bx0-1423 ∷ Toff014 ∷ []) (Toff014 ∷ Bx0-1423 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ (lit c4)) ▸
       at 2 2 (Toff013 ∷ Sw34 ∷ []) (lem-nat-3-TOFF014 (lit c4)) ▸
       at 1 2 (Toff013 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-TOFF012-at2332 c4) ▸
       at 0 2 (Toff014 ∷ Sw34 ∷ []) (lem-nat-3-TOFF013 (lit c4)) ▸
       at 1 2 (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto BOX(0;1234) | TOFF012 @0110243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-TOFF012-at0110243243 : Ws → ⟪ (Bx1-0423 ∷ Toff104 ∷ []) ⟫ʷ ≈ ⟪ (Toff104 ∷ Bx1-0423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-TOFF012-at0110243243 c4 = run b0
  where
  b0 : Chain (Bx1-0423 ∷ Toff104 ∷ []) (Toff104 ∷ Bx1-0423 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4)) ▸
       at 2 2 (Toff014 ∷ Sw01 ∷ []) (lem-nat-0-TOFF104 (lit c4)) ▸
       at 1 2 (Toff014 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-TOFF012-at243243 c4) ▸
       at 0 2 (Toff104 ∷ Sw01 ∷ []) (lem-nat-0-TOFF014 (lit c4)) ▸
       at 1 2 (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto BOX(0;1234) | CCZ103 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ103-at2332 : Ws → ⟪ (Bx0-1324 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ103-at2332 c4 = run b0
  where
  b0 : Chain (Bx0-1324 ∷ CCZ012 ∷ []) (CCZ012 ∷ Bx0-1324 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ (lit c4)) ▸
       at 2 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 (lit c4)) ▸
       at 1 2 (CCZ013 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ103 c4) ▸
       at 0 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 (lit c4)) ▸
       at 1 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto BOX(0;1234) | CCZ103 @243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ103-at243243 : Ws → ⟪ (Bx0-1423 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Bx0-1423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ103-at243243 c4 = run b0
  where
  b0 : Chain (Bx0-1423 ∷ CCZ012 ∷ []) (CCZ012 ∷ Bx0-1423 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ (lit c4)) ▸
       at 2 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 1 2 (CCZ012 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ103-at2332 c4) ▸
       at 0 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 1 2 (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto BOX(0;1234) | CCZ103 @0110243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ103-at0110243243 : Ws → ⟪ (Bx1-0423 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Bx1-0423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ103-at0110243243 c4 = run b0
  where
  b0 : Chain (Bx1-0423 ∷ CCZ012 ∷ []) (CCZ012 ∷ Bx1-0423 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4)) ▸
       at 2 2 (CCZ012 ∷ Sw01 ∷ []) (sym (wl0096 (lit c4))) ▸
       at 1 2 (CCZ012 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ103-at243243 c4) ▸
       at 0 2 (CCZ012 ∷ Sw01 ∷ []) (sym (wl0096 (lit c4))) ▸
       at 1 2 (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- K0-pass @0110: 7 steps
lem-K0-pass-at0110 : Ws → ⟪ (K1 ∷ Bx1-0234 ∷ K1⁻ ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0234 ∷ []) ⟫ʷ
lem-K0-pass-at0110 c4 = run b0
  where
  b0 : Chain (K1 ∷ Bx1-0234 ∷ K1⁻ ∷ []) (Bx1-0234 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (K0 ∷ Sw01 ∷ []) (sym (wl0031 (lit c4))) ▸
       at 2 2 (Bx0-1234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0234⟩ (lit c4)) ▸
       at 3 2 (K0⁻ ∷ Sw01 ∷ []) (sym (wl0257 (lit c4))) ▸
       at 1 3 (Bx0-1234 ∷ []) (lem-K0-pass c4) ▸
       at 0 2 (Bx1-0234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1234⟩ (lit c4)) ▸
       at 1 2 [] (wl0002 (lit c4)) ▸ done


-- TW: 54 steps
lem-TW : Ws → ⟪ (Toff102 ∷ Bx0-1234 ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ Bx1-0234 ∷ []) ⟫ʷ
lem-TW c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (run b6))))))
  where
  b0 : Chain (Toff102 ∷ Bx0-1234 ∷ Toff102 ∷ []) (K1 ∷ CCZ012 ∷ Toff023 ∷ Toff104 ∷ Toff023 ∷ K1⁻ ∷ CCZ014 ∷ K1 ∷ CCZ012 ∷ K1⁻ ∷ [])
  b0 = at 0 1 (K1 ∷ CCZ012 ∷ K1⁻ ∷ []) (sym (wl0258 (lit c4))) ▸
       at 4 1 (K1 ∷ CCZ012 ∷ K1⁻ ∷ []) (sym (wl0258 (lit c4))) ▸
       at 3 1 (Bx0-2134 ∷ []) (lem-sym12 c4) ▸
       at 3 1 (Bx0-2314 ∷ []) (lem-sym23-at1221 c4) ▸
       at 3 1 (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ []) (lem-beta-T-at122331 c4) ▸
       at 2 2 (Toff023 ∷ K1⁻ ∷ []) (wl0259 (lit c4)) ▸
       at 3 2 (Toff104 ∷ K1⁻ ∷ []) (wp0063 c4) ▸
       at 4 2 (Toff023 ∷ K1⁻ ∷ []) (wl0259 (lit c4)) ▸ done

  b1 : Chain (K1 ∷ CCZ012 ∷ Toff023 ∷ Toff104 ∷ Toff023 ∷ K1⁻ ∷ CCZ014 ∷ K1 ∷ CCZ012 ∷ K1⁻ ∷ []) (K1 ∷ Toff023 ∷ Toff104 ∷ CCZ012 ∷ CCZ024 ∷ Bx1-0423 ∷ Toff023 ∷ CCZ123 ∷ Toff104 ∷ CCZ012 ∷ K1⁻ ∷ [])
  b1 = at 5 2 (Toff104 ∷ K1⁻ ∷ []) (wp0063 c4) ▸
       at 6 2 [] (wl0260 (lit c4)) ▸
       at 1 2 (Toff023 ∷ CCZ012 ∷ CCZ123 ∷ []) (wl0261 (lit c4)) ▸
       at 3 0 (Toff104 ∷ Toff104 ∷ []) (sym (wp0064 c4)) ▸
       at 7 0 (CCZ123 ∷ CCZ123 ∷ []) (sym (wl0212 (lit c4))) ▸
       at 4 4 (Bx1-0423 ∷ []) (sym (lem-beta-T-at0110243243 c4)) ▸
       at 2 2 (Toff104 ∷ CCZ012 ∷ CCZ024 ∷ []) (wp0065 c4) ▸
       at 6 2 (Toff023 ∷ CCZ123 ∷ []) (wl0262 (lit c4)) ▸ done

  b2 : Chain (K1 ∷ Toff023 ∷ Toff104 ∷ CCZ012 ∷ CCZ024 ∷ Bx1-0423 ∷ Toff023 ∷ CCZ123 ∷ Toff104 ∷ CCZ012 ∷ K1⁻ ∷ []) (K1 ∷ Toff023 ∷ Toff104 ∷ CCZ012 ∷ CCZ024 ∷ Toff023 ∷ Bx1-2043 ∷ CCZ234 ∷ CCZ123 ∷ Toff104 ∷ CCZ012 ∷ K1⁻ ∷ [])
  b2 = at 5 0 (Toff023 ∷ Toff023 ∷ []) (sym (wl0263 (lit c4))) ▸
       at 7 1 (Bx1-0243 ∷ []) (lem-sym23-at0110243243 c4) ▸
       at 7 1 (Bx1-0234 ∷ []) (lem-sym34-at01103443 c4) ▸
       at 7 1 (Bx1-2034 ∷ []) (lem-sym12-at0110 c4) ▸
       at 7 1 (Bx1-2304 ∷ []) (lem-sym23-at011220 c4) ▸
       at 6 3 (Bx1-2304 ∷ CCZ234 ∷ []) (lem-T312-beta-at01122330 c4) ▸
       at 6 1 (Bx1-2034 ∷ []) (lem-sym23-at01122330 c4) ▸
       at 6 1 (Bx1-2043 ∷ []) (lem-sym34-at011220 c4) ▸ done

  b3 : Chain (K1 ∷ Toff023 ∷ Toff104 ∷ CCZ012 ∷ CCZ024 ∷ Toff023 ∷ Bx1-2043 ∷ CCZ234 ∷ CCZ123 ∷ Toff104 ∷ CCZ012 ∷ K1⁻ ∷ []) (K1 ∷ Toff023 ∷ Toff104 ∷ Toff023 ∷ CCZ012 ∷ CCZ123 ∷ CCZ123 ∷ CCZ024 ∷ CCZ234 ∷ Bx1-0423 ∷ CCZ234 ∷ Toff104 ∷ CCZ012 ∷ K1⁻ ∷ [])
  b3 = at 6 1 (Bx1-0243 ∷ []) (lem-sym12-at0112203443 c4) ▸
       at 6 1 (Bx1-0423 ∷ []) (lem-sym23-at01103443 c4) ▸
       at 4 2 (Toff023 ∷ CCZ024 ∷ CCZ234 ∷ []) (wp0066 c4) ▸
       at 3 2 (Toff023 ∷ CCZ012 ∷ CCZ123 ∷ []) (wl0261 (lit c4)) ▸
       at 9 2 (CCZ123 ∷ CCZ234 ∷ []) (sym (wl0264 (lit c4))) ▸
       at 8 2 (CCZ123 ∷ Bx1-0423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ034-at0110243243 c4) ▸
       at 7 2 (CCZ123 ∷ CCZ234 ∷ []) (sym (wl0264 (lit c4))) ▸
       at 6 2 (CCZ123 ∷ CCZ024 ∷ []) (lem-auto-CCZ012-∣-CCZ314-at12243143 c4) ▸ done

  b4 : Chain (K1 ∷ Toff023 ∷ Toff104 ∷ Toff023 ∷ CCZ012 ∷ CCZ123 ∷ CCZ123 ∷ CCZ024 ∷ CCZ234 ∷ Bx1-0423 ∷ CCZ234 ∷ Toff104 ∷ CCZ012 ∷ K1⁻ ∷ []) (K1 ∷ Toff023 ∷ Toff104 ∷ Toff023 ∷ Toff104 ∷ CCZ012 ∷ CCZ024 ∷ CCZ012 ∷ CCZ024 ∷ Bx1-0423 ∷ K1⁻ ∷ [])
  b4 = at 5 2 [] (wl0212 (lit c4)) ▸
       at 7 2 (CCZ234 ∷ Bx1-0423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ342-at0110243243 c4) ▸
       at 6 2 [] (wl0265 (lit c4)) ▸
       at 6 2 (Toff104 ∷ Bx1-0423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-TOFF012-at0110243243 c4) ▸
       at 5 2 (Toff104 ∷ CCZ024 ∷ []) (wp0067 c4) ▸
       at 4 2 (Toff104 ∷ CCZ012 ∷ CCZ024 ∷ []) (wp0065 c4) ▸
       at 8 2 (CCZ012 ∷ Bx1-0423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ103-at0110243243 c4) ▸
       at 7 2 (CCZ012 ∷ CCZ024 ∷ []) (sym (wp0068 c4)) ▸ done

  b5 : Chain (K1 ∷ Toff023 ∷ Toff104 ∷ Toff023 ∷ Toff104 ∷ CCZ012 ∷ CCZ024 ∷ CCZ012 ∷ CCZ024 ∷ Bx1-0423 ∷ K1⁻ ∷ []) (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ K1 ∷ Bx1-0423 ∷ K1⁻ ∷ [])
  b5 = at 6 2 (CCZ012 ∷ CCZ024 ∷ []) (sym (wp0068 c4)) ▸
       at 5 2 [] (wl0183 (lit c4)) ▸
       at 5 2 [] (wp0034 c4) ▸
       at 5 0 (K1⁻ ∷ K1 ∷ []) (sym (wl0260 (lit c4))) ▸
       at 0 2 (Toff023 ∷ K1 ∷ []) (wl0266 (lit c4)) ▸
       at 1 2 (CCZ014 ∷ K1 ∷ []) (sym (wp0069 c4)) ▸
       at 2 2 (Toff023 ∷ K1 ∷ []) (wl0266 (lit c4)) ▸
       at 3 3 (CCZ014 ∷ []) (sym (wp0070 c4)) ▸ done

  b6 : Chain (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ K1 ∷ Bx1-0423 ∷ K1⁻ ∷ []) (Bx0-1234 ∷ Bx1-0234 ∷ [])
  b6 = at 0 4 (Bx0-2314 ∷ []) (sym (lem-beta-T-at122331 c4)) ▸
       at 0 1 (Bx0-2134 ∷ []) (lem-sym23-at122331 c4) ▸
       at 0 1 (Bx0-1234 ∷ []) (lem-sym12-at1221 c4) ▸
       at 2 1 (Bx1-0243 ∷ []) (lem-sym23-at0110243243 c4) ▸
       at 2 1 (Bx1-0234 ∷ []) (lem-sym34-at01103443 c4) ▸
       at 1 3 (Bx1-0234 ∷ []) (lem-K0-pass-at0110 c4) ▸ done


-- sym34 @233442: 5 steps
lem-sym34-at233442 : Ws → ⟪ (Bx0-1342 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ []) ⟫ʷ
lem-sym34-at233442 c4 = run b0
  where
  b0 : Chain (Bx0-1342 ∷ []) (Bx0-1324 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx0-1243 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1342⟩ (lit c4)) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym34-at3443 c4) ▸
       at 0 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ (lit c4)) ▸
       at 1 2 [] (wl0006 (lit c4)) ▸ done


-- sym34 @12233441: 5 steps
lem-sym34-at12233441 : Ws → ⟪ (Bx0-2341 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2314 ∷ []) ⟫ʷ
lem-sym34-at12233441 c4 = run b0
  where
  b0 : Chain (Bx0-2341 ∷ []) (Bx0-2314 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx0-1342 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2341⟩ (lit c4)) ▸
       at 1 1 (Bx0-1324 ∷ []) (lem-sym34-at233442 c4) ▸
       at 0 2 (Bx0-2314 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1324⟩ (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- CS20-beta-c @1221: 7 steps
lem-CS20-beta-c-at1221 : Ws → ⟪ (CS01 ∷ Bx0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ CS01 ∷ []) ⟫ʷ
lem-CS20-beta-c-at1221 c4 = run b0
  where
  b0 : Chain (CS01 ∷ Bx0-2134 ∷ []) (Bx0-2134 ∷ CS01 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CS02 ∷ Sw12 ∷ []) (lem-nat-1-CS01 (lit c4)) ▸
       at 2 2 (Bx0-1234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2134⟩ (lit c4)) ▸
       at 1 2 (Bx0-1234 ∷ CS02 ∷ []) (lem-CS20-beta-c c4) ▸
       at 0 2 (Bx0-2134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1234⟩ (lit c4)) ▸
       at 1 2 (CS01 ∷ Sw12 ∷ []) (lem-nat-1-CS02 (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- sym34 @122331: 5 steps
lem-sym34-at122331 : Ws → ⟪ (Bx0-2314 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2341 ∷ []) ⟫ʷ
lem-sym34-at122331 c4 = run b0
  where
  b0 : Chain (Bx0-2314 ∷ []) (Bx0-2341 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx0-1324 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2314⟩ (lit c4)) ▸
       at 1 1 (Bx0-1342 ∷ []) (lem-sym34-at2332 c4) ▸
       at 0 2 (Bx0-2341 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1342⟩ (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- auto CS01 | BOX(0;2341): 5 steps
lem-auto-CS01-∣-BOX⟨0·2341⟩ : Ws → ⟪ (CS01 ∷ Bx0-2341 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2341 ∷ CS01 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨0·2341⟩ c4 = run b0
  where
  b0 : Chain (CS01 ∷ Bx0-2341 ∷ []) (Bx0-2341 ∷ CS01 ∷ [])
  b0 = at 1 1 (Bx0-2314 ∷ []) (lem-sym34-at12233441 c4) ▸
       at 1 1 (Bx0-2134 ∷ []) (lem-sym23-at122331 c4) ▸
       at 0 2 (Bx0-2134 ∷ CS01 ∷ []) (lem-CS20-beta-c-at1221 c4) ▸
       at 0 1 (Bx0-2314 ∷ []) (lem-sym23-at1221 c4) ▸
       at 0 1 (Bx0-2341 ∷ []) (lem-sym34-at122331 c4) ▸ done


-- AX-SB: 8 steps
lem-AX-SB : Ws → ⟪ (CS01 ∷ Sb0-2-34-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-34-1 ∷ CS01 ∷ []) ⟫ʷ
lem-AX-SB c4 = run b0
  where
  b0 : Chain (CS01 ∷ Sb0-2-34-1 ∷ []) (Sb0-2-34-1 ∷ CS01 ∷ [])
  b0 = at 1 1 (Bx0-2341 ∷ Toff134 ∷ Sb0-2-1-4 ∷ Toff134 ∷ Sb⁻0-2-1-4 ∷ []) (refl) ▸
       at 3 1 (CS12 ∷ []) (refl) ▸
       at 5 1 (CS12⁻ ∷ []) (refl) ▸
       at 0 2 (Bx0-2341 ∷ CS01 ∷ []) (lem-auto-CS01-∣-BOX⟨0·2341⟩ c4) ▸
       at 1 5 (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CS01 ∷ []) (axAX) ▸
       at 2 1 (Sb0-2-1-4 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-2-1-4 ∷ []) (refl) ▸
       at 0 5 (Sb0-2-34-1 ∷ []) (refl) ▸ done


-- sym23 @0210243143: 5 steps
lem-sym23-at0210243143 : Ws → ⟪ (Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0143 ∷ []) ⟫ʷ
lem-sym23-at0210243143 c4 = run b0
  where
  b0 : Chain (Bx2-0413 ∷ []) (Bx2-0143 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4)) ▸
       at 1 1 (Bx1-0243 ∷ []) (lem-sym23-at0110243243 c4) ▸
       at 0 2 (Bx2-0143 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0243⟩ (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- SBsym: 9 steps
lem-SBsym : Ws → ⟪ (Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-14-3 ∷ []) ⟫ʷ
lem-SBsym c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb2-0-41-3 ∷ []) (Bx2-0143 ∷ Toff314 ∷ Sb2-0-3-4 ∷ Toff314 ∷ Sb⁻2-0-3-4 ∷ [])
  b0 = at 0 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 2 1 (CS03 ∷ []) (refl) ▸
       at 4 1 (CS03⁻ ∷ []) (refl) ▸
       at 0 1 (Bx2-0143 ∷ []) (lem-sym23-at0210243143 c4) ▸
       at 1 1 (Toff314 ∷ []) (wl0267 (lit c4)) ▸
       at 3 1 (Toff314 ∷ []) (wl0267 (lit c4)) ▸
       at 2 1 (Sb2-0-3-4 ∷ []) (refl) ▸
       at 4 1 (Sb⁻2-0-3-4 ∷ []) (refl) ▸ done

  b1 : Chain (Bx2-0143 ∷ Toff314 ∷ Sb2-0-3-4 ∷ Toff314 ∷ Sb⁻2-0-3-4 ∷ []) (Sb2-0-14-3 ∷ [])
  b1 = at 0 5 (Sb2-0-14-3 ∷ []) (refl) ▸ done


-- SBsymd: 61 steps
lem-SBsymd : Ws → ⟪ (Sb⁻2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-0-14-3 ∷ []) ⟫ʷ
lem-SBsymd c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (run b7)))))))
  where
  b0 : Chain (Sb⁻2-0-41-3 ∷ []) (Sb⁻2-0-41-3 ∷ CCZ012 ∷ Toff201 ∷ Bx0-243 ∷ Bx⁻2-03 ∷ CCZ024 ∷ Toff024 ∷ Bx⁻2-03 ∷ Toff024 ∷ CCZ024 ∷ Toff201 ∷ CCZ012 ∷ [])
  b0 = at 1 0 (CCZ012 ∷ CCZ012 ∷ []) (sym (wl0183 (lit c4))) ▸
       at 2 0 (Toff201 ∷ Toff201 ∷ []) (sym (wl0268 (lit c4))) ▸
       at 3 0 (CCZ024 ∷ Toff024 ∷ CZ03 ∷ Toff024 ∷ CCZ024 ∷ CZ03 ∷ CZ03 ∷ CCZ024 ∷ Toff024 ∷ CZ03 ∷ Toff024 ∷ CCZ024 ∷ []) (sym (wp0071 c4)) ▸
       at 5 1 (Bx2-03 ∷ []) (refl) ▸
       at 8 1 (Bx2-03 ∷ []) (refl) ▸
       at 3 6 (Bx0-243 ∷ []) (refl) ▸
       at 4 1 (Bx⁻2-03 ∷ []) (refl) ▸
       at 7 1 (Bx⁻2-03 ∷ []) (refl) ▸ done

  b1 : Chain (Sb⁻2-0-41-3 ∷ CCZ012 ∷ Toff201 ∷ Bx0-243 ∷ Bx⁻2-03 ∷ CCZ024 ∷ Toff024 ∷ Bx⁻2-03 ∷ Toff024 ∷ CCZ024 ∷ Toff201 ∷ CCZ012 ∷ []) (Sb⁻2-0-41-3 ∷ CCZ012 ∷ Toff201 ∷ Bx0-243 ∷ Toff201 ∷ CCZ012 ∷ Bx0-243 ∷ Bx⁻2-03 ∷ CCZ024 ∷ Toff024 ∷ CZ03 ∷ Toff024 ∷ CCZ024 ∷ CCZ012 ∷ Toff201 ∷ Bx⁻0-243 ∷ Toff201 ∷ CCZ012 ∷ [])
  b1 = at 4 6 (Bx⁻0-243 ∷ []) (refl) ▸
       at 4 0 (Toff201 ∷ Toff201 ∷ []) (sym (wl0268 (lit c4))) ▸
       at 5 0 (CCZ012 ∷ CCZ012 ∷ []) (sym (wl0183 (lit c4))) ▸
       at 6 0 (CCZ024 ∷ Toff024 ∷ CZ03 ∷ Toff024 ∷ CCZ024 ∷ CZ03 ∷ CZ03 ∷ CCZ024 ∷ Toff024 ∷ CZ03 ∷ Toff024 ∷ CCZ024 ∷ []) (sym (wp0071 c4)) ▸
       at 8 1 (Bx2-03 ∷ []) (refl) ▸
       at 11 1 (Bx2-03 ∷ []) (refl) ▸
       at 6 6 (Bx0-243 ∷ []) (refl) ▸
       at 7 1 (Bx⁻2-03 ∷ []) (refl) ▸ done

  b2 : Chain (Sb⁻2-0-41-3 ∷ CCZ012 ∷ Toff201 ∷ Bx0-243 ∷ Toff201 ∷ CCZ012 ∷ Bx0-243 ∷ Bx⁻2-03 ∷ CCZ024 ∷ Toff024 ∷ CZ03 ∷ Toff024 ∷ CCZ024 ∷ CCZ012 ∷ Toff201 ∷ Bx⁻0-243 ∷ Toff201 ∷ CCZ012 ∷ []) (Sb⁻2-0-41-3 ∷ Bx2-0143 ∷ Toff314 ∷ Sb2-0-3-4 ∷ Sb⁻2-0-3-4 ∷ Toff314 ∷ Bx⁻2-0143 ∷ [])
  b2 = at 10 1 (Bx⁻2-03 ∷ []) (refl) ▸
       at 7 6 (Bx⁻0-243 ∷ []) (refl) ▸
       at 1 6 (Bx2-0143 ∷ []) (refl) ▸
       at 2 6 (Bx⁻2-0143 ∷ []) (refl) ▸
       at 2 0 (Toff314 ∷ Toff314 ∷ []) (sym (wl0248 (lit c4))) ▸
       at 3 0 (CS03 ∷ CS03⁻ ∷ []) (sym (wl0250 (lit c4))) ▸
       at 3 1 (Sb2-0-3-4 ∷ []) (refl) ▸
       at 4 1 (Sb⁻2-0-3-4 ∷ []) (refl) ▸ done

  b3 : Chain (Sb⁻2-0-41-3 ∷ Bx2-0143 ∷ Toff314 ∷ Sb2-0-3-4 ∷ Sb⁻2-0-3-4 ∷ Toff314 ∷ Bx⁻2-0143 ∷ []) (Sb⁻2-0-41-3 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Sb⁻2-0-14-3 ∷ [])
  b3 = at 4 0 (Toff314 ∷ Toff314 ∷ []) (sym (wl0248 (lit c4))) ▸
       at 5 0 (CS03⁻ ∷ CS03 ∷ []) (sym (wl0249 (lit c4))) ▸
       at 5 1 (Sb⁻2-0-3-4 ∷ []) (refl) ▸
       at 6 1 (Sb2-0-3-4 ∷ []) (refl) ▸
       at 1 5 (Sb2-0-14-3 ∷ []) (refl) ▸
       at 2 5 (Sb⁻2-0-14-3 ∷ []) (refl) ▸
       at 1 1 (Sb2-0-41-3 ∷ []) (sym (lem-SBsym c4)) ▸
       at 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸ done

  b4 : Chain (Sb⁻2-0-41-3 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Sb⁻2-0-14-3 ∷ []) (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻0-213 ∷ CCZ024 ∷ Toff204 ∷ CZ03 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Sb⁻2-0-14-3 ∷ [])
  b4 = at 0 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) (refl) ▸
       at 5 1 (CCZ024 ∷ Toff204 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ []) (refl) ▸
       at 4 1 (Bx⁻0-213 ∷ CCZ024 ∷ Toff204 ∷ Bx⁻0-213 ∷ Toff204 ∷ CCZ024 ∷ []) (refl) ▸
       at 9 2 [] (wp0034 c4) ▸
       at 8 2 [] (wp0059 c4) ▸
       at 7 1 (Bx⁻2-03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-03 ∷ Toff012 ∷ CCZ012 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 10 1 (CZ03 ∷ []) (refl) ▸ done

  b5 : Chain (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻0-213 ∷ CCZ024 ∷ Toff204 ∷ CZ03 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Sb⁻2-0-14-3 ∷ []) (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ CZ03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx0-213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Sb⁻2-0-14-3 ∷ [])
  b5 = at 13 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) (refl) ▸
       at 15 1 (CZ03 ∷ []) (refl) ▸
       at 18 1 (CZ03 ∷ []) (refl) ▸
       at 7 12 [] (wl0247 (lit c4)) ▸
       at 6 2 [] (wp0059 c4) ▸
       at 5 2 [] (wp0034 c4) ▸
       at 4 1 (Bx⁻2-03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-03 ∷ Toff012 ∷ CCZ012 ∷ []) (refl) ▸
       at 4 1 (CZ03 ∷ []) (refl) ▸ done

  b6 : Chain (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ CZ03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx0-213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Sb⁻2-0-14-3 ∷ []) (Sb2-0-3-1 ∷ Toff314 ∷ CS03⁻ ∷ CS03 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Sb⁻2-0-14-3 ∷ [])
  b6 = at 7 1 (CZ03 ∷ []) (refl) ▸
       at 10 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) (refl) ▸
       at 12 1 (CZ03 ∷ []) (refl) ▸
       at 15 1 (CZ03 ∷ []) (refl) ▸
       at 4 12 [] (wl0247 (lit c4)) ▸
       at 3 2 [] (wl0248 (lit c4)) ▸
       at 2 1 (CS03⁻ ∷ []) (refl) ▸
       at 3 1 (CS03 ∷ []) (refl) ▸ done

  b7 : Chain (Sb2-0-3-1 ∷ Toff314 ∷ CS03⁻ ∷ CS03 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Sb⁻2-0-14-3 ∷ []) (Sb⁻2-0-14-3 ∷ [])
  b7 = at 2 2 [] (wl0249 (lit c4)) ▸
       at 1 2 [] (wl0248 (lit c4)) ▸
       at 0 1 (CS03 ∷ []) (refl) ▸
       at 1 1 (CS03⁻ ∷ []) (refl) ▸
       at 0 2 [] (wl0250 (lit c4)) ▸ done


-- sym12 @2332: 5 steps
lem-sym12-at2332 : Ws → ⟪ (Bx0-1324 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3124 ∷ []) ⟫ʷ
lem-sym12-at2332 c4 = run b0
  where
  b0 : Chain (Bx0-1324 ∷ []) (Bx0-3124 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ (lit c4)) ▸
       at 1 1 (Bx0-2134 ∷ []) (lem-sym12 c4) ▸
       at 0 2 (Bx0-3124 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·2134⟩ (lit c4)) ▸
       at 1 2 [] (wl0006 (lit c4)) ▸ done


-- sym12 @243243: 5 steps
lem-sym12-at243243 : Ws → ⟪ (Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4123 ∷ []) ⟫ʷ
lem-sym12-at243243 c4 = run b0
  where
  b0 : Chain (Bx0-1423 ∷ []) (Bx0-4123 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ (lit c4)) ▸
       at 1 1 (Bx0-3124 ∷ []) (lem-sym12-at2332 c4) ▸
       at 0 2 (Bx0-4123 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·3124⟩ (lit c4)) ▸
       at 1 2 [] (wl0007 (lit c4)) ▸ done


-- sym12 @0110243243: 5 steps
lem-sym12-at0110243243 : Ws → ⟪ (Bx1-0423 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-4023 ∷ []) ⟫ʷ
lem-sym12-at0110243243 c4 = run b0
  where
  b0 : Chain (Bx1-0423 ∷ []) (Bx1-4023 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4)) ▸
       at 1 1 (Bx0-4123 ∷ []) (lem-sym12-at243243 c4) ▸
       at 0 2 (Bx1-4023 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·4123⟩ (lit c4)) ▸
       at 1 2 [] (wl0002 (lit c4)) ▸ done


-- sym12 @0210243143: 5 steps
lem-sym12-at0210243143 : Ws → ⟪ (Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4013 ∷ []) ⟫ʷ
lem-sym12-at0210243143 c4 = run b0
  where
  b0 : Chain (Bx2-0413 ∷ []) (Bx2-4013 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4)) ▸
       at 1 1 (Bx1-4023 ∷ []) (lem-sym12-at0110243243 c4) ▸
       at 0 2 (Bx2-4013 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·4023⟩ (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- SBtgt: 8 steps
lem-SBtgt : Ws → ⟪ (Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-01-3 ∷ []) ⟫ʷ
lem-SBtgt c4 = run b0
  where
  b0 : Chain (Sb2-0-41-3 ∷ []) (Sb2-4-01-3 ∷ [])
  b0 = at 0 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 2 1 (CS03 ∷ []) (refl) ▸
       at 4 1 (CS03⁻ ∷ []) (refl) ▸
       at 0 1 (Bx2-4013 ∷ []) (lem-sym12-at0210243143 c4) ▸
       at 1 4 (Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (sym (wp0072 c4)) ▸
       at 2 1 (Sb2-4-3-1 ∷ []) (refl) ▸
       at 4 1 (Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 0 5 (Sb2-4-01-3 ∷ []) (refl) ▸ done


-- BOXd-BOX @2332: 5 steps
lem-BOXd-BOX-at2332 : Ws → ⟪ (Bx⁻0-1324 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ []) ⟫ʷ
lem-BOXd-BOX-at2332 c4 = run b0
  where
  b0 : Chain (Bx⁻0-1324 ∷ []) (Bx0-1324 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx⁻0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·1324⟩ (lit c4)) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-BOXd-BOX c4) ▸
       at 0 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ (lit c4)) ▸
       at 1 2 [] (wl0006 (lit c4)) ▸ done


-- BOXd-BOX @243243: 5 steps
lem-BOXd-BOX-at243243 : Ws → ⟪ (Bx⁻0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ []) ⟫ʷ
lem-BOXd-BOX-at243243 c4 = run b0
  where
  b0 : Chain (Bx⁻0-1423 ∷ []) (Bx0-1423 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Bx⁻0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨0·1423⟩ (lit c4)) ▸
       at 1 1 (Bx0-1324 ∷ []) (lem-BOXd-BOX-at2332 c4) ▸
       at 0 2 (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ (lit c4)) ▸
       at 1 2 [] (wl0007 (lit c4)) ▸ done


-- BOXd-BOX @0110243243: 5 steps
lem-BOXd-BOX-at0110243243 : Ws → ⟪ (Bx⁻1-0423 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0423 ∷ []) ⟫ʷ
lem-BOXd-BOX-at0110243243 c4 = run b0
  where
  b0 : Chain (Bx⁻1-0423 ∷ []) (Bx1-0423 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx⁻0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨1·0423⟩ (lit c4)) ▸
       at 1 1 (Bx0-1423 ∷ []) (lem-BOXd-BOX-at243243 c4) ▸
       at 0 2 (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ (lit c4)) ▸
       at 1 2 [] (wl0002 (lit c4)) ▸ done


-- BOXd-BOX @0210243143: 5 steps
lem-BOXd-BOX-at0210243143 : Ws → ⟪ (Bx⁻2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ []) ⟫ʷ
lem-BOXd-BOX-at0210243143 c4 = run b0
  where
  b0 : Chain (Bx⁻2-0413 ∷ []) (Bx2-0413 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx⁻1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨2·0413⟩ (lit c4)) ▸
       at 1 1 (Bx1-0423 ∷ []) (lem-BOXd-BOX-at0110243243 c4) ▸
       at 0 2 (Bx2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0423⟩ (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- BOXd-BOX @1221: 5 steps
lem-BOXd-BOX-at1221 : Ws → ⟪ (Bx⁻0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ []) ⟫ʷ
lem-BOXd-BOX-at1221 c4 = run b0
  where
  b0 : Chain (Bx⁻0-2134 ∷ []) (Bx0-2134 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx⁻0-1234 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨0·2134⟩ (lit c4)) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-BOXd-BOX c4) ▸
       at 0 2 (Bx0-2134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1234⟩ (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- BOXd-BOX @132132: 5 steps
lem-BOXd-BOX-at132132 : Ws → ⟪ (Bx⁻0-3124 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3124 ∷ []) ⟫ʷ
lem-BOXd-BOX-at132132 c4 = run b0
  where
  b0 : Chain (Bx⁻0-3124 ∷ []) (Bx0-3124 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx⁻0-2134 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·3124⟩ (lit c4)) ▸
       at 1 1 (Bx0-2134 ∷ []) (lem-BOXd-BOX-at1221 c4) ▸
       at 0 2 (Bx0-3124 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·2134⟩ (lit c4)) ▸
       at 1 2 [] (wl0006 (lit c4)) ▸ done


-- BOXd-BOX @14213243: 5 steps
lem-BOXd-BOX-at14213243 : Ws → ⟪ (Bx⁻0-4123 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4123 ∷ []) ⟫ʷ
lem-BOXd-BOX-at14213243 c4 = run b0
  where
  b0 : Chain (Bx⁻0-4123 ∷ []) (Bx0-4123 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Bx⁻0-3124 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨0·4123⟩ (lit c4)) ▸
       at 1 1 (Bx0-3124 ∷ []) (lem-BOXd-BOX-at132132 c4) ▸
       at 0 2 (Bx0-4123 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·3124⟩ (lit c4)) ▸
       at 1 2 [] (wl0007 (lit c4)) ▸ done


-- BOXd-BOX @0114203243: 5 steps
lem-BOXd-BOX-at0114203243 : Ws → ⟪ (Bx⁻1-4023 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-4023 ∷ []) ⟫ʷ
lem-BOXd-BOX-at0114203243 c4 = run b0
  where
  b0 : Chain (Bx⁻1-4023 ∷ []) (Bx1-4023 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx⁻0-4123 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨1·4023⟩ (lit c4)) ▸
       at 1 1 (Bx0-4123 ∷ []) (lem-BOXd-BOX-at14213243 c4) ▸
       at 0 2 (Bx1-4023 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·4123⟩ (lit c4)) ▸
       at 1 2 [] (wl0002 (lit c4)) ▸ done


-- BOXd-BOX @0214203143: 5 steps
lem-BOXd-BOX-at0214203143 : Ws → ⟪ (Bx⁻2-4013 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4013 ∷ []) ⟫ʷ
lem-BOXd-BOX-at0214203143 c4 = run b0
  where
  b0 : Chain (Bx⁻2-4013 ∷ []) (Bx2-4013 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx⁻1-4023 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨2·4013⟩ (lit c4)) ▸
       at 1 1 (Bx1-4023 ∷ []) (lem-BOXd-BOX-at0114203243 c4) ▸
       at 0 2 (Bx2-4013 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·4023⟩ (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- SBtgtd: 10 steps
lem-SBtgtd : Ws → ⟪ (Sb⁻2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-4-01-3 ∷ []) ⟫ʷ
lem-SBtgtd c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb⁻2-0-41-3 ∷ []) (Sb2-4-3-1 ∷ Toff301 ∷ CS34⁻ ∷ Toff301 ∷ Bx⁻2-4013 ∷ [])
  b0 = at 0 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) (refl) ▸
       at 0 1 (CS03 ∷ []) (refl) ▸
       at 2 1 (CS03⁻ ∷ []) (refl) ▸
       at 0 4 (CS34 ∷ Toff301 ∷ CS34⁻ ∷ Toff301 ∷ []) (wp0073 c4) ▸
       at 4 1 (Bx2-0413 ∷ []) (lem-BOXd-BOX-at0210243143 c4) ▸
       at 4 1 (Bx2-4013 ∷ []) (lem-sym12-at0210243143 c4) ▸
       at 4 1 (Bx⁻2-4013 ∷ []) (sym (lem-BOXd-BOX-at0214203143 c4)) ▸
       at 0 1 (Sb2-4-3-1 ∷ []) (refl) ▸ done

  b1 : Chain (Sb2-4-3-1 ∷ Toff301 ∷ CS34⁻ ∷ Toff301 ∷ Bx⁻2-4013 ∷ []) (Sb⁻2-4-01-3 ∷ [])
  b1 = at 2 1 (Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 0 5 (Sb⁻2-4-01-3 ∷ []) (refl) ▸ done


-- sym12 @021021: 5 steps
lem-sym12-at021021 : Ws → ⟪ (Bx2-0134 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1034 ∷ []) ⟫ʷ
lem-sym12-at021021 c4 = run b0
  where
  b0 : Chain (Bx2-0134 ∷ []) (Bx2-1034 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx1-0234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0134⟩ (lit c4)) ▸
       at 1 1 (Bx1-2034 ∷ []) (lem-sym12-at0110 c4) ▸
       at 0 2 (Bx2-1034 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·2034⟩ (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- sym12 @03102132: 5 steps
lem-sym12-at03102132 : Ws → ⟪ (Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1024 ∷ []) ⟫ʷ
lem-sym12-at03102132 c4 = run b0
  where
  b0 : Chain (Bx3-0124 ∷ []) (Bx3-1024 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx2-0134 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0124⟩ (lit c4)) ▸
       at 1 1 (Bx2-1034 ∷ []) (lem-sym12-at021021 c4) ▸
       at 0 2 (Bx3-1024 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·1034⟩ (lit c4)) ▸
       at 1 2 [] (wl0006 (lit c4)) ▸ done


-- sym23 @0110: 5 steps
lem-sym23-at0110 : Ws → ⟪ (Bx1-0234 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0324 ∷ []) ⟫ʷ
lem-sym23-at0110 c4 = run b0
  where
  b0 : Chain (Bx1-0234 ∷ []) (Bx1-0324 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx0-1234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0234⟩ (lit c4)) ▸
       at 1 1 (Bx0-1324 ∷ []) (lem-sym23 c4) ▸
       at 0 2 (Bx1-0324 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1324⟩ (lit c4)) ▸
       at 1 2 [] (wl0002 (lit c4)) ▸ done


-- sym23 @021021: 5 steps
lem-sym23-at021021 : Ws → ⟪ (Bx2-0134 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0314 ∷ []) ⟫ʷ
lem-sym23-at021021 c4 = run b0
  where
  b0 : Chain (Bx2-0134 ∷ []) (Bx2-0314 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx1-0234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0134⟩ (lit c4)) ▸
       at 1 1 (Bx1-0324 ∷ []) (lem-sym23-at0110 c4) ▸
       at 0 2 (Bx2-0314 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0324⟩ (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- sym23 @03102132: 5 steps
lem-sym23-at03102132 : Ws → ⟪ (Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0214 ∷ []) ⟫ʷ
lem-sym23-at03102132 c4 = run b0
  where
  b0 : Chain (Bx3-0124 ∷ []) (Bx3-0214 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx2-0134 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0124⟩ (lit c4)) ▸
       at 1 1 (Bx2-0314 ∷ []) (lem-sym23-at021021 c4) ▸
       at 0 2 (Bx3-0214 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0314⟩ (lit c4)) ▸
       at 1 2 [] (wl0006 (lit c4)) ▸ done


-- sym23 @032032: 5 steps
lem-sym23-at032032 : Ws → ⟪ (Bx3-1024 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1204 ∷ []) ⟫ʷ
lem-sym23-at032032 c4 = run b0
  where
  b0 : Chain (Bx3-1024 ∷ []) (Bx3-1204 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx3-0124 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1024⟩ (lit c4)) ▸
       at 1 1 (Bx3-0214 ∷ []) (lem-sym23-at03102132 c4) ▸
       at 0 2 (Bx3-1204 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·0214⟩ (lit c4)) ▸
       at 1 2 [] (wl0002 (lit c4)) ▸ done


-- beta-T @0110: 8 steps
lem-beta-T-at0110 : Ws → ⟪ (Bx1-0234 ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ CCZ134 ∷ Toff102 ∷ CCZ134 ∷ []) ⟫ʷ
lem-beta-T-at0110 c4 = run b0
  where
  b0 : Chain (Bx1-0234 ∷ []) (Toff102 ∷ CCZ134 ∷ Toff102 ∷ CCZ134 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx0-1234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0234⟩ (lit c4)) ▸
       at 1 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-beta-T c4) ▸
       at 0 2 (Toff102 ∷ Sw01 ∷ []) (wl0099 (lit c4)) ▸
       at 1 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 (lit c4)) ▸
       at 2 2 (Toff102 ∷ Sw01 ∷ []) (wl0099 (lit c4)) ▸
       at 3 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 (lit c4)) ▸
       at 4 2 [] (wl0002 (lit c4)) ▸ done


-- beta-T @021021: 8 steps
lem-beta-T-at021021 : Ws → ⟪ (Bx2-0134 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) ⟫ʷ
lem-beta-T-at021021 c4 = run b0
  where
  b0 : Chain (Bx2-0134 ∷ []) (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx1-0234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0134⟩ (lit c4)) ▸
       at 1 1 (Toff102 ∷ CCZ134 ∷ Toff102 ∷ CCZ134 ∷ []) (lem-beta-T-at0110 c4) ▸
       at 0 2 (Toff201 ∷ Sw12 ∷ []) (wl0047 (lit c4)) ▸
       at 1 2 (CCZ234 ∷ Sw12 ∷ []) (sym (wl0084 (lit c4))) ▸
       at 2 2 (Toff201 ∷ Sw12 ∷ []) (wl0047 (lit c4)) ▸
       at 3 2 (CCZ234 ∷ Sw12 ∷ []) (sym (wl0084 (lit c4))) ▸
       at 4 2 [] (wl0001 (lit c4)) ▸ done


-- beta-T @03102132: 8 steps
lem-beta-T-at03102132 : Ws → ⟪ (Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ []) ⟫ʷ
lem-beta-T-at03102132 c4 = run b0
  where
  b0 : Chain (Bx3-0124 ∷ []) (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx2-0134 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0124⟩ (lit c4)) ▸
       at 1 1 (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-beta-T-at021021 c4) ▸
       at 0 2 (Toff301 ∷ Sw23 ∷ []) (lem-nat-2-TOFF201 (lit c4)) ▸
       at 1 2 (CCZ234 ∷ Sw23 ∷ []) (sym (wl0086 (lit c4))) ▸
       at 2 2 (Toff301 ∷ Sw23 ∷ []) (lem-nat-2-TOFF201 (lit c4)) ▸
       at 3 2 (CCZ234 ∷ Sw23 ∷ []) (sym (wl0086 (lit c4))) ▸
       at 4 2 [] (wl0006 (lit c4)) ▸ done


-- beta-T @031031: 8 steps
lem-beta-T-at031031 : Ws → ⟪ (Bx3-0214 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ []) ⟫ʷ
lem-beta-T-at031031 c4 = run b0
  where
  b0 : Chain (Bx3-0214 ∷ []) (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx3-0124 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0214⟩ (lit c4)) ▸
       at 1 1 (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ []) (lem-beta-T-at03102132 c4) ▸
       at 0 2 (Toff302 ∷ Sw12 ∷ []) (lem-nat-1-TOFF301 (lit c4)) ▸
       at 1 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0034 (lit c4))) ▸
       at 2 2 (Toff302 ∷ Sw12 ∷ []) (lem-nat-1-TOFF301 (lit c4)) ▸
       at 3 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0034 (lit c4))) ▸
       at 4 2 [] (wl0001 (lit c4)) ▸ done


-- beta-T @0330: 8 steps
lem-beta-T-at0330 : Ws → ⟪ (Bx3-1204 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ []) ⟫ʷ
lem-beta-T-at0330 c4 = run b0
  where
  b0 : Chain (Bx3-1204 ∷ []) (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx3-0214 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1204⟩ (lit c4)) ▸
       at 1 1 (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ []) (lem-beta-T-at031031 c4) ▸
       at 0 2 (Toff312 ∷ Sw01 ∷ []) (wl0116 (lit c4)) ▸
       at 1 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 (lit c4)) ▸
       at 2 2 (Toff312 ∷ Sw01 ∷ []) (wl0116 (lit c4)) ▸
       at 3 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 (lit c4)) ▸
       at 4 2 [] (wl0002 (lit c4)) ▸ done


-- KB-form: 7 steps
lem-KB-form : Ws → ⟪ (K0 ∷ Bx3-0124 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ []) ⟫ʷ
lem-KB-form c4 = run b0
  where
  b0 : Chain (K0 ∷ Bx3-0124 ∷ K0⁻ ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ [])
  b0 = at 1 1 (Bx3-1024 ∷ []) (lem-sym12-at03102132 c4) ▸
       at 1 1 (Bx3-1204 ∷ []) (lem-sym23-at032032 c4) ▸
       at 1 1 (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ []) (lem-beta-T-at0330 c4) ▸
       at 0 2 (Toff312 ∷ K0 ∷ []) (c₁ (K) (Toffᵗ)) ▸
       at 1 2 (Toff034 ∷ K0 ∷ []) (wp0011 c4) ▸
       at 2 2 (Toff312 ∷ K0 ∷ []) (c₁ (K) (Toffᵗ)) ▸
       at 3 3 (Toff034 ∷ []) (wp0012 c4) ▸ done


-- sym23 @0210213443: 5 steps
lem-sym23-at0210213443 : Ws → ⟪ (Bx2-0143 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ []) ⟫ʷ
lem-sym23-at0210213443 c4 = run b0
  where
  b0 : Chain (Bx2-0143 ∷ []) (Bx2-0413 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx1-0243 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0143⟩ (lit c4)) ▸
       at 1 1 (Bx1-0423 ∷ []) (lem-sym23-at01103443 c4) ▸
       at 0 2 (Bx2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0423⟩ (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- sym23 @0310213442: 5 steps
lem-sym23-at0310213442 : Ws → ⟪ (Bx3-0142 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ []) ⟫ʷ
lem-sym23-at0310213442 c4 = run b0
  where
  b0 : Chain (Bx3-0142 ∷ []) (Bx3-0412 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx2-0143 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0142⟩ (lit c4)) ▸
       at 1 1 (Bx2-0413 ∷ []) (lem-sym23-at0210213443 c4) ▸
       at 0 2 (Bx3-0412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0413⟩ (lit c4)) ▸
       at 1 2 [] (wl0006 (lit c4)) ▸ done


-- beta-T @0210243143: 8 steps
lem-beta-T-at0210243143 : Ws → ⟪ (Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) ⟫ʷ
lem-beta-T-at0210243143 c4 = run b0
  where
  b0 : Chain (Bx2-0413 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4)) ▸
       at 1 1 (Toff104 ∷ CCZ123 ∷ Toff104 ∷ CCZ123 ∷ []) (lem-beta-T-at0110243243 c4) ▸
       at 0 2 (Toff204 ∷ Sw12 ∷ []) (lem-nat-1-TOFF104 (lit c4)) ▸
       at 1 2 (CCZ123 ∷ Sw12 ∷ []) (sym (wl0111 (lit c4))) ▸
       at 2 2 (Toff204 ∷ Sw12 ∷ []) (lem-nat-1-TOFF104 (lit c4)) ▸
       at 3 2 (CCZ123 ∷ Sw12 ∷ []) (sym (wl0111 (lit c4))) ▸
       at 4 2 [] (wl0001 (lit c4)) ▸ done


-- beta-T @0310243142: 8 steps
lem-beta-T-at0310243142 : Ws → ⟪ (Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) ⟫ʷ
lem-beta-T-at0310243142 c4 = run b0
  where
  b0 : Chain (Bx3-0412 ∷ []) (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx2-0413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0412⟩ (lit c4)) ▸
       at 1 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸
       at 0 2 (Toff304 ∷ Sw23 ∷ []) (lem-nat-2-TOFF204 (lit c4)) ▸
       at 1 2 (CCZ123 ∷ Sw23 ∷ []) (sym (wl0113 (lit c4))) ▸
       at 2 2 (Toff304 ∷ Sw23 ∷ []) (lem-nat-2-TOFF204 (lit c4)) ▸
       at 3 2 (CCZ123 ∷ Sw23 ∷ []) (sym (wl0113 (lit c4))) ▸
       at 4 2 [] (wl0006 (lit c4)) ▸ done


-- sym23 @0310243142: 5 steps
lem-sym23-at0310243142 : Ws → ⟪ (Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0142 ∷ []) ⟫ʷ
lem-sym23-at0310243142 c4 = run b0
  where
  b0 : Chain (Bx3-0412 ∷ []) (Bx3-0142 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx2-0413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0412⟩ (lit c4)) ▸
       at 1 1 (Bx2-0143 ∷ []) (lem-sym23-at0210243143 c4) ▸
       at 0 2 (Bx3-0142 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0143⟩ (lit c4)) ▸
       at 1 2 [] (wl0006 (lit c4)) ▸ done


-- CKbox: 17 steps
lem-CKbox : Ws → ⟪ (CK40 ∷ Bx3-0124 ∷ CK40 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ Bx3-0124 ∷ K0⁻ ∷ []) ⟫ʷ
lem-CKbox c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CK40 ∷ Bx3-0124 ∷ CK40 ∷ S4 ∷ []) (K0 ∷ Toff304 ∷ X4 ∷ CCZ123 ∷ CK40⁻ ∷ X4 ∷ Toff304 ∷ CCZ123 ∷ K0 ∷ X4 ∷ CK40⁻ ∷ X4 ∷ S4 ∷ [])
  b0 = at 0 1 (K0 ∷ X4 ∷ CK40⁻ ∷ X4 ∷ []) (wp0074 c4) ▸
       at 5 1 (K0 ∷ X4 ∷ CK40⁻ ∷ X4 ∷ []) (wp0074 c4) ▸
       at 4 1 (Bx3-0142 ∷ []) (lem-sym34-at03102132 c4) ▸
       at 4 1 (Bx3-0412 ∷ []) (lem-sym23-at0310213442 c4) ▸
       at 4 1 (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) (lem-beta-T-at0310243142 c4) ▸
       at 1 4 (Toff304 ∷ X4 ∷ CK40⁻ ∷ X4 ∷ []) (sym (wp0075 c4)) ▸
       at 4 2 (CCZ123 ∷ X4 ∷ []) (sym (c₄ (CCZ ↑) (X))) ▸
       at 3 2 (CCZ123 ∷ CK40⁻ ∷ []) (lem-comm-CKd40-CCZ123 (lit c4)) ▸ done

  b1 : Chain (K0 ∷ Toff304 ∷ X4 ∷ CCZ123 ∷ CK40⁻ ∷ X4 ∷ Toff304 ∷ CCZ123 ∷ K0 ∷ X4 ∷ CK40⁻ ∷ X4 ∷ S4 ∷ []) (K0 ∷ Bx3-0124 ∷ X4 ∷ CK40⁻ ∷ X4 ∷ K0 ∷ X4 ∷ CK40⁻ ∷ X4 ∷ S4 ∷ [])
  b1 = at 2 2 (CCZ123 ∷ X4 ∷ []) (sym (c₄ (CCZ ↑) (X))) ▸
       at 3 4 (Toff304 ∷ X4 ∷ CK40⁻ ∷ X4 ∷ []) (sym (wp0075 c4)) ▸
       at 6 2 (CCZ123 ∷ X4 ∷ []) (sym (c₄ (CCZ ↑) (X))) ▸
       at 5 2 (CCZ123 ∷ CK40⁻ ∷ []) (lem-comm-CKd40-CCZ123 (lit c4)) ▸
       at 4 2 (CCZ123 ∷ X4 ∷ []) (sym (c₄ (CCZ ↑) (X))) ▸
       at 1 4 (Bx3-0412 ∷ []) (sym (lem-beta-T-at0310243142 c4)) ▸
       at 1 1 (Bx3-0142 ∷ []) (lem-sym23-at0310243142 c4) ▸
       at 1 1 (Bx3-0124 ∷ []) (lem-sym34-at0310213442 c4) ▸ done

  b2 : Chain (K0 ∷ Bx3-0124 ∷ X4 ∷ CK40⁻ ∷ X4 ∷ K0 ∷ X4 ∷ CK40⁻ ∷ X4 ∷ S4 ∷ []) (K0 ∷ Bx3-0124 ∷ K0⁻ ∷ [])
  b2 = at 2 8 (K0⁻ ∷ []) (sym (wp0076 c4)) ▸ done


-- auto BOX(0;1234) | CCZ231: 5 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ231 : Ws → ⟪ (Bx0-1234 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ231 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ CCZ123 ∷ []) (CCZ123 ∷ Bx0-1234 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ []) (wl0269 (lit c4)) ▸
       at 0 1 (Bx0-1243 ∷ []) (lem-sym34 c4) ▸
       at 0 2 (CCZ123 ∷ Bx0-1243 ∷ []) (sym (lem-c124-beta-at3443 c4)) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym34-at3443 c4) ▸
       at 0 1 (CCZ123 ∷ []) (wl0269 (lit c4)) ▸ done


-- CS12-beta @2332: 7 steps
lem-CS12-beta-at2332 : Ws → ⟪ (CS13 ∷ Bx0-1324 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ CS13 ∷ []) ⟫ʷ
lem-CS12-beta-at2332 c4 = run b0
  where
  b0 : Chain (CS13 ∷ Bx0-1324 ∷ []) (Bx0-1324 ∷ CS13 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (CS12 ∷ Sw23 ∷ []) (lem-nat-2-CS13 (lit c4)) ▸
       at 2 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ (lit c4)) ▸
       at 1 2 (Bx0-1234 ∷ CS12 ∷ []) (lem-CS12-beta c4) ▸
       at 0 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ (lit c4)) ▸
       at 1 2 (CS13 ∷ Sw23 ∷ []) (lem-nat-2-CS12 (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- CS12-beta @243243: 7 steps
lem-CS12-beta-at243243 : Ws → ⟪ (CS14 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ CS14 ∷ []) ⟫ʷ
lem-CS12-beta-at243243 c4 = run b0
  where
  b0 : Chain (CS14 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ CS14 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (CS13 ∷ Sw34 ∷ []) (lem-nat-3-CS14 (lit c4)) ▸
       at 2 2 (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ (lit c4)) ▸
       at 1 2 (Bx0-1324 ∷ CS13 ∷ []) (lem-CS12-beta-at2332 c4) ▸
       at 0 2 (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ (lit c4)) ▸
       at 1 2 (CS14 ∷ Sw34 ∷ []) (lem-nat-3-CS13 (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto BOX(0;1234) | CS14: 5 steps
lem-auto-BOX⟨0·1234⟩-∣-CS14 : Ws → ⟪ (Bx0-1234 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS14 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ CS14 ∷ []) (CS14 ∷ Bx0-1234 ∷ [])
  b0 = at 0 1 (Bx0-1243 ∷ []) (lem-sym34 c4) ▸
       at 0 1 (Bx0-1423 ∷ []) (lem-sym23-at3443 c4) ▸
       at 0 2 (CS14 ∷ Bx0-1423 ∷ []) (sym (lem-CS12-beta-at243243 c4)) ▸
       at 1 1 (Bx0-1243 ∷ []) (lem-sym23-at243243 c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym34-at3443 c4) ▸ done


-- CSd12-beta @2332: 7 steps
lem-CSd12-beta-at2332 : Ws → ⟪ (CS13⁻ ∷ Bx0-1324 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-CSd12-beta-at2332 c4 = run b0
  where
  b0 : Chain (CS13⁻ ∷ Bx0-1324 ∷ []) (Bx0-1324 ∷ CS13⁻ ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (CS12⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd13 (lit c4)) ▸
       at 2 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ (lit c4)) ▸
       at 1 2 (Bx0-1234 ∷ CS12⁻ ∷ []) (lem-CSd12-beta c4) ▸
       at 0 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ (lit c4)) ▸
       at 1 2 (CS13⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd12 (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- CSd12-beta @243243: 7 steps
lem-CSd12-beta-at243243 : Ws → ⟪ (CS14⁻ ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ CS14⁻ ∷ []) ⟫ʷ
lem-CSd12-beta-at243243 c4 = run b0
  where
  b0 : Chain (CS14⁻ ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ CS14⁻ ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (CS13⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd14 (lit c4)) ▸
       at 2 2 (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ (lit c4)) ▸
       at 1 2 (Bx0-1324 ∷ CS13⁻ ∷ []) (lem-CSd12-beta-at2332 c4) ▸
       at 0 2 (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ (lit c4)) ▸
       at 1 2 (CS14⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd13 (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto BOX(0;1234) | CSd14: 5 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd14 : Ws → ⟪ (Bx0-1234 ∷ CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS14⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd14 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ Bx0-1234 ∷ [])
  b0 = at 0 1 (Bx0-1243 ∷ []) (lem-sym34 c4) ▸
       at 0 1 (Bx0-1423 ∷ []) (lem-sym23-at3443 c4) ▸
       at 0 2 (CS14⁻ ∷ Bx0-1423 ∷ []) (sym (lem-CSd12-beta-at243243 c4)) ▸
       at 1 1 (Bx0-1243 ∷ []) (lem-sym23-at243243 c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym34-at3443 c4) ▸ done


-- sym34 @0214213043: 5 steps
lem-sym34-at0214213043 : Ws → ⟪ (Bx2-4103 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4130 ∷ []) ⟫ʷ
lem-sym34-at0214213043 c4 = run b0
  where
  b0 : Chain (Bx2-4103 ∷ []) (Bx2-4130 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx2-4013 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·4103⟩ (lit c4)) ▸
       at 1 1 (Bx2-4031 ∷ []) (lem-sym34-at0214203143 c4) ▸
       at 0 2 (Bx2-4130 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·4031⟩ (lit c4)) ▸
       at 1 2 [] (wl0002 (lit c4)) ▸ done


-- T312-beta @142142: 8 steps
lem-T312-beta-at142142 : Ws → ⟪ (Toff314 ∷ Bx0-4132 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4132 ∷ CCZ124 ∷ []) ⟫ʷ
lem-T312-beta-at142142 c4 = run b0
  where
  b0 : Chain (Toff314 ∷ Bx0-4132 ∷ Toff314 ∷ []) (Bx0-4132 ∷ CCZ124 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Toff214 ∷ Sw23 ∷ []) (lem-nat-2-TOFF314 (lit c4)) ▸
       at 2 2 (Bx0-4123 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·4132⟩ (lit c4)) ▸
       at 3 2 (Toff214 ∷ Sw23 ∷ []) (lem-nat-2-TOFF314 (lit c4)) ▸
       at 1 3 (Bx0-4123 ∷ CCZ134 ∷ []) (lem-T312-beta-at14213243 c4) ▸
       at 0 2 (Bx0-4132 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·4123⟩ (lit c4)) ▸
       at 1 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- T312-beta @01142042: 8 steps
lem-T312-beta-at01142042 : Ws → ⟪ (Toff304 ∷ Bx1-4032 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-4032 ∷ CCZ024 ∷ []) ⟫ʷ
lem-T312-beta-at01142042 c4 = run b0
  where
  b0 : Chain (Toff304 ∷ Bx1-4032 ∷ Toff304 ∷ []) (Bx1-4032 ∷ CCZ024 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Toff314 ∷ Sw01 ∷ []) (lem-nat-0-TOFF304 (lit c4)) ▸
       at 2 2 (Bx0-4132 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·4032⟩ (lit c4)) ▸
       at 3 2 (Toff314 ∷ Sw01 ∷ []) (lem-nat-0-TOFF304 (lit c4)) ▸
       at 1 3 (Bx0-4132 ∷ CCZ124 ∷ []) (lem-T312-beta-at142142 c4) ▸
       at 0 2 (Bx1-4032 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·4132⟩ (lit c4)) ▸
       at 1 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- T312-beta @02142041: 8 steps
lem-T312-beta-at02142041 : Ws → ⟪ (Toff304 ∷ Bx2-4031 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4031 ∷ CCZ014 ∷ []) ⟫ʷ
lem-T312-beta-at02142041 c4 = run b0
  where
  b0 : Chain (Toff304 ∷ Bx2-4031 ∷ Toff304 ∷ []) (Bx2-4031 ∷ CCZ014 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Toff304 ∷ Sw12 ∷ []) (lem-nat-1-TOFF304 (lit c4)) ▸
       at 2 2 (Bx1-4032 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·4031⟩ (lit c4)) ▸
       at 3 2 (Toff304 ∷ Sw12 ∷ []) (lem-nat-1-TOFF304 (lit c4)) ▸
       at 1 3 (Bx1-4032 ∷ CCZ024 ∷ []) (lem-T312-beta-at01142042 c4) ▸
       at 0 2 (Bx2-4031 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·4032⟩ (lit c4)) ▸
       at 1 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- T312-beta @02142140: 8 steps
lem-T312-beta-at02142140 : Ws → ⟪ (Toff314 ∷ Bx2-4130 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4130 ∷ CCZ014 ∷ []) ⟫ʷ
lem-T312-beta-at02142140 c4 = run b0
  where
  b0 : Chain (Toff314 ∷ Bx2-4130 ∷ Toff314 ∷ []) (Bx2-4130 ∷ CCZ014 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Toff304 ∷ Sw01 ∷ []) (lem-nat-0-TOFF314 (lit c4)) ▸
       at 2 2 (Bx2-4031 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·4130⟩ (lit c4)) ▸
       at 3 2 (Toff304 ∷ Sw01 ∷ []) (lem-nat-0-TOFF314 (lit c4)) ▸
       at 1 3 (Bx2-4031 ∷ CCZ014 ∷ []) (lem-T312-beta-at02142041 c4) ▸
       at 0 2 (Bx2-4130 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·4031⟩ (lit c4)) ▸
       at 1 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- sym34 @142142: 5 steps
lem-sym34-at142142 : Ws → ⟪ (Bx0-4132 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4123 ∷ []) ⟫ʷ
lem-sym34-at142142 c4 = run b0
  where
  b0 : Chain (Bx0-4132 ∷ []) (Bx0-4123 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx0-4123 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·4132⟩ (lit c4)) ▸
       at 1 1 (Bx0-4132 ∷ []) (lem-sym34-at14213243 c4) ▸
       at 0 2 (Bx0-4123 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·4132⟩ (lit c4)) ▸
       at 1 2 [] (wl0006 (lit c4)) ▸ done


-- sym34 @01142042: 5 steps
lem-sym34-at01142042 : Ws → ⟪ (Bx1-4032 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-4023 ∷ []) ⟫ʷ
lem-sym34-at01142042 c4 = run b0
  where
  b0 : Chain (Bx1-4032 ∷ []) (Bx1-4023 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx0-4132 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·4032⟩ (lit c4)) ▸
       at 1 1 (Bx0-4123 ∷ []) (lem-sym34-at142142 c4) ▸
       at 0 2 (Bx1-4023 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·4123⟩ (lit c4)) ▸
       at 1 2 [] (wl0002 (lit c4)) ▸ done


-- sym34 @02142041: 5 steps
lem-sym34-at02142041 : Ws → ⟪ (Bx2-4031 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4013 ∷ []) ⟫ʷ
lem-sym34-at02142041 c4 = run b0
  where
  b0 : Chain (Bx2-4031 ∷ []) (Bx2-4013 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx1-4032 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·4031⟩ (lit c4)) ▸
       at 1 1 (Bx1-4023 ∷ []) (lem-sym34-at01142042 c4) ▸
       at 0 2 (Bx2-4013 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·4023⟩ (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- sym34 @02142140: 5 steps
lem-sym34-at02142140 : Ws → ⟪ (Bx2-4130 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4103 ∷ []) ⟫ʷ
lem-sym34-at02142140 c4 = run b0
  where
  b0 : Chain (Bx2-4130 ∷ []) (Bx2-4103 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx2-4031 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·4130⟩ (lit c4)) ▸
       at 1 1 (Bx2-4013 ∷ []) (lem-sym34-at02142041 c4) ▸
       at 0 2 (Bx2-4103 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·4013⟩ (lit c4)) ▸
       at 1 2 [] (wl0002 (lit c4)) ▸ done


-- auto BOX(0;1234) | CCZ231 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at2332 : Ws → ⟪ (Bx0-1324 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at2332 c4 = run b0
  where
  b0 : Chain (Bx0-1324 ∷ CCZ123 ∷ []) (CCZ123 ∷ Bx0-1324 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ (lit c4)) ▸
       at 2 2 (CCZ123 ∷ Sw23 ∷ []) (sym (wl0113 (lit c4))) ▸
       at 1 2 (CCZ123 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231 c4) ▸
       at 0 2 (CCZ123 ∷ Sw23 ∷ []) (sym (wl0113 (lit c4))) ▸
       at 1 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto BOX(0;1234) | CCZ231 @243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at243243 : Ws → ⟪ (Bx0-1423 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Bx0-1423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at243243 c4 = run b0
  where
  b0 : Chain (Bx0-1423 ∷ CCZ124 ∷ []) (CCZ124 ∷ Bx0-1423 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ (lit c4)) ▸
       at 2 2 (CCZ123 ∷ Sw34 ∷ []) (lem-nat-3-CCZ124 (lit c4)) ▸
       at 1 2 (CCZ123 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at2332 c4) ▸
       at 0 2 (CCZ124 ∷ Sw34 ∷ []) (lem-nat-3-CCZ123 (lit c4)) ▸
       at 1 2 (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto BOX(0;1234) | CCZ231 @0110243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0110243243 : Ws → ⟪ (Bx1-0423 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Bx1-0423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0110243243 c4 = run b0
  where
  b0 : Chain (Bx1-0423 ∷ CCZ024 ∷ []) (CCZ024 ∷ Bx1-0423 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4)) ▸
       at 2 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 (lit c4)) ▸
       at 1 2 (CCZ124 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at243243 c4) ▸
       at 0 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 (lit c4)) ▸
       at 1 2 (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto BOX(0;1234) | CCZ231 @0210243143: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0210243143 : Ws → ⟪ (Bx2-0413 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ Bx2-0413 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0210243143 c4 = run b0
  where
  b0 : Chain (Bx2-0413 ∷ CCZ014 ∷ []) (CCZ014 ∷ Bx2-0413 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4)) ▸
       at 2 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 (lit c4)) ▸
       at 1 2 (CCZ024 ∷ Bx1-0423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0110243243 c4) ▸
       at 0 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 (lit c4)) ▸
       at 1 2 (Bx2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0423⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto BOX(0;1234) | CS14 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS14-at2332 : Ws → ⟪ (Bx0-1324 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS14-at2332 c4 = run b0
  where
  b0 : Chain (Bx0-1324 ∷ CS14 ∷ []) (CS14 ∷ Bx0-1324 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ (lit c4)) ▸
       at 2 2 (CS14 ∷ Sw23 ∷ []) (sym (wl0021 (lit c4))) ▸
       at 1 2 (CS14 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS14 c4) ▸
       at 0 2 (CS14 ∷ Sw23 ∷ []) (sym (wl0021 (lit c4))) ▸
       at 1 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto BOX(0;1234) | CS14 @243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS14-at243243 : Ws → ⟪ (Bx0-1423 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Bx0-1423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS14-at243243 c4 = run b0
  where
  b0 : Chain (Bx0-1423 ∷ CS13 ∷ []) (CS13 ∷ Bx0-1423 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ (lit c4)) ▸
       at 2 2 (CS14 ∷ Sw34 ∷ []) (lem-nat-3-CS13 (lit c4)) ▸
       at 1 2 (CS14 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS14-at2332 c4) ▸
       at 0 2 (CS13 ∷ Sw34 ∷ []) (lem-nat-3-CS14 (lit c4)) ▸
       at 1 2 (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto BOX(0;1234) | CS14 @0110243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS14-at0110243243 : Ws → ⟪ (Bx1-0423 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Bx1-0423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS14-at0110243243 c4 = run b0
  where
  b0 : Chain (Bx1-0423 ∷ CS03 ∷ []) (CS03 ∷ Bx1-0423 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4)) ▸
       at 2 2 (CS13 ∷ Sw01 ∷ []) (sym (wl0061 (lit c4))) ▸
       at 1 2 (CS13 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS14-at243243 c4) ▸
       at 0 2 (CS03 ∷ Sw01 ∷ []) (sym (wl0019 (lit c4))) ▸
       at 1 2 (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto BOX(0;1234) | CS14 @0210243143: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS14-at0210243143 : Ws → ⟪ (Bx2-0413 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Bx2-0413 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS14-at0210243143 c4 = run b0
  where
  b0 : Chain (Bx2-0413 ∷ CS03 ∷ []) (CS03 ∷ Bx2-0413 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4)) ▸
       at 2 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 (lit c4))) ▸
       at 1 2 (CS03 ∷ Bx1-0423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS14-at0110243243 c4) ▸
       at 0 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 (lit c4))) ▸
       at 1 2 (Bx2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0423⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto BOX(0;1234) | CSd14 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd14-at2332 : Ws → ⟪ (Bx0-1324 ∷ CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS14⁻ ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd14-at2332 c4 = run b0
  where
  b0 : Chain (Bx0-1324 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ Bx0-1324 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ (lit c4)) ▸
       at 2 2 (CS14⁻ ∷ Sw23 ∷ []) (sym (wl0033 (lit c4))) ▸
       at 1 2 (CS14⁻ ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd14 c4) ▸
       at 0 2 (CS14⁻ ∷ Sw23 ∷ []) (sym (wl0033 (lit c4))) ▸
       at 1 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto BOX(0;1234) | CSd14 @243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd14-at243243 : Ws → ⟪ (Bx0-1423 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ Bx0-1423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd14-at243243 c4 = run b0
  where
  b0 : Chain (Bx0-1423 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ Bx0-1423 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ (lit c4)) ▸
       at 2 2 (CS14⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd13 (lit c4)) ▸
       at 1 2 (CS14⁻ ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd14-at2332 c4) ▸
       at 0 2 (CS13⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd14 (lit c4)) ▸
       at 1 2 (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto BOX(0;1234) | CSd14 @0110243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd14-at0110243243 : Ws → ⟪ (Bx1-0423 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ Bx1-0423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd14-at0110243243 c4 = run b0
  where
  b0 : Chain (Bx1-0423 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ Bx1-0423 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4)) ▸
       at 2 2 (CS13⁻ ∷ Sw01 ∷ []) (sym (wl0121 (lit c4))) ▸
       at 1 2 (CS13⁻ ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd14-at243243 c4) ▸
       at 0 2 (CS03⁻ ∷ Sw01 ∷ []) (sym (wl0022 (lit c4))) ▸
       at 1 2 (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto BOX(0;1234) | CSd14 @0210243143: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd14-at0210243143 : Ws → ⟪ (Bx2-0413 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ Bx2-0413 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd14-at0210243143 c4 = run b0
  where
  b0 : Chain (Bx2-0413 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ Bx2-0413 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4)) ▸
       at 2 2 (CS03⁻ ∷ Sw12 ∷ []) (sym (wl0023 (lit c4))) ▸
       at 1 2 (CS03⁻ ∷ Bx1-0423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd14-at0110243243 c4) ▸
       at 0 2 (CS03⁻ ∷ Sw12 ∷ []) (sym (wl0023 (lit c4))) ▸
       at 1 2 (Bx2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0423⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- SB2: 31 steps
lem-SB2 : Ws → ⟪ (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ []) ⟫ʷ
lem-SB2 c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ []) (Toff314 ∷ Toff314 ∷ Bx2-4013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b0 = at 0 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 2 1 (CS03 ∷ []) (refl) ▸
       at 4 1 (CS03⁻ ∷ []) (refl) ▸
       at 5 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 7 1 (CS03 ∷ []) (refl) ▸
       at 9 1 (CS03⁻ ∷ []) (refl) ▸
       at 0 0 (Toff314 ∷ Toff314 ∷ []) (sym (wl0248 (lit c4))) ▸
       at 2 1 (Bx2-4013 ∷ []) (lem-sym12-at0210243143 c4) ▸ done

  b1 : Chain (Toff314 ∷ Toff314 ∷ Bx2-4013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Toff314 ∷ CCZ014 ∷ CS03 ∷ Bx2-0413 ∷ Toff314 ∷ CS03⁻ ∷ Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b1 = at 2 1 (Bx2-4103 ∷ []) (lem-sym23-at0214203143 c4) ▸
       at 2 1 (Bx2-4130 ∷ []) (lem-sym34-at0214213043 c4) ▸
       at 1 3 (Bx2-4130 ∷ CCZ014 ∷ []) (lem-T312-beta-at02142140 c4) ▸
       at 1 1 (Bx2-4103 ∷ []) (lem-sym34-at02142140 c4) ▸
       at 1 1 (Bx2-4013 ∷ []) (lem-sym23-at0214213043 c4) ▸
       at 1 1 (Bx2-0413 ∷ []) (lem-sym12-at0214203143 c4) ▸
       at 1 2 (CCZ014 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0210243143 c4) ▸
       at 2 2 (CS03 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS14-at0210243143 c4) ▸ done

  b2 : Chain (Toff314 ∷ CCZ014 ∷ CS03 ∷ Bx2-0413 ∷ Toff314 ∷ CS03⁻ ∷ Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Toff314 ∷ CCZ014 ∷ CS03 ∷ Toff314 ∷ Bx2-0413 ∷ CCZ014 ∷ CS03⁻ ∷ Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b2 = at 3 0 (Toff314 ∷ Toff314 ∷ []) (sym (wl0248 (lit c4))) ▸
       at 5 1 (Bx2-4013 ∷ []) (lem-sym12-at0210243143 c4) ▸
       at 5 1 (Bx2-4103 ∷ []) (lem-sym23-at0214203143 c4) ▸
       at 5 1 (Bx2-4130 ∷ []) (lem-sym34-at0214213043 c4) ▸
       at 4 3 (Bx2-4130 ∷ CCZ014 ∷ []) (lem-T312-beta-at02142140 c4) ▸
       at 4 1 (Bx2-4103 ∷ []) (lem-sym34-at02142140 c4) ▸
       at 4 1 (Bx2-4013 ∷ []) (lem-sym23-at0214213043 c4) ▸
       at 4 1 (Bx2-0413 ∷ []) (lem-sym12-at0214203143 c4) ▸ done

  b3 : Chain (Toff314 ∷ CCZ014 ∷ CS03 ∷ Toff314 ∷ Bx2-0413 ∷ CCZ014 ∷ CS03⁻ ∷ Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (CCZ014 ∷ [])
  b3 = at 4 2 (CCZ014 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0210243143 c4) ▸
       at 5 2 (CS03⁻ ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd14-at0210243143 c4) ▸
       at 0 2 (CCZ014 ∷ Toff314 ∷ []) (sym (wp0077 c4)) ▸
       at 1 4 (CCZ014 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ []) (sym (wp0078 c4)) ▸
       at 0 2 [] (wp0055 c4) ▸
       at 4 2 [] (lem-beta-inv-at0210243143 c4) ▸
       at 0 8 (CCZ014 ∷ []) (sym (wp0056 c4)) ▸ done


-- F1 order-CS [nf of rhs]: 0 steps
lem-F1-order-CS-nf-of-rhs : Ws → ⟪ [] ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-F1-order-CS-nf-of-rhs c4 = refl

-- F1 order-CS: 4 steps
lem-F1-order-CS : Ws → ⟪ (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-F1-order-CS c4 = run b0
  where
  b0 : Chain (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ []) []
  b0 = at 0 2 (CCZ014 ∷ []) (lem-SB2 c4) ▸
       at 1 2 (CCZ014 ∷ []) (lem-SB2 c4) ▸
       at 0 2 [] (wp0055 c4) ▸
       at 0 0 [] (sym (lem-F1-order-CS-nf-of-rhs c4)) ▸ done


-- auto BOX(0;1234) | CS21: 3 steps
lem-auto-BOX⟨0·1234⟩-∣-CS21 : Ws → ⟪ (Bx0-1234 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS21 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ CS12 ∷ []) (CS12 ∷ Bx0-1234 ∷ [])
  b0 = at 1 1 (CS12 ∷ []) (wl0270 (lit c4)) ▸
       at 0 2 (CS12 ∷ Bx0-1234 ∷ []) (sym (lem-CS12-beta c4)) ▸
       at 0 1 (CS12 ∷ []) (wl0270 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | CS21: 11 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS21 : Ws → ⟪ (Sb0-1-23-4 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS21 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-1-23-4 ∷ CS12 ∷ []) (Bx0-1234 ∷ Toff423 ∷ CS12 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 4 1 (CS14⁻ ∷ []) (refl) ▸
       at 4 2 (CS12 ∷ CS14⁻ ∷ []) (sym (wl0271 (lit c4))) ▸
       at 5 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 3 2 (CS12 ∷ Toff423 ∷ []) (sym (wl0272 (lit c4))) ▸
       at 2 1 (CS14 ∷ []) (refl) ▸
       at 2 2 (CS12 ∷ CS14 ∷ []) (sym (wl0273 (lit c4))) ▸
       at 3 1 (Sb0-1-4-3 ∷ []) (refl) ▸ done

  b1 : Chain (Bx0-1234 ∷ Toff423 ∷ CS12 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (CS12 ∷ Sb0-1-23-4 ∷ [])
  b1 = at 1 2 (CS12 ∷ Toff423 ∷ []) (sym (wl0272 (lit c4))) ▸
       at 0 2 (CS12 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS21 c4) ▸
       at 1 5 (Sb0-1-23-4 ∷ []) (refl) ▸ done


-- auto SBOX(0;1;23;4) | CS21 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS21-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS21-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ CS13 ∷ []) (CS13 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 (CS12 ∷ Sw23 ∷ []) (lem-nat-2-CS13 (lit c4)) ▸
       at 1 2 (CS12 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS21 c4) ▸
       at 0 2 (CS13 ∷ Sw23 ∷ []) (lem-nat-2-CS12 (lit c4)) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | CS21 @243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS21-at243243 : Ws → ⟪ (Sb0-1-42-3 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS21-at243243 c4 = run b0
  where
  b0 : Chain (Sb0-1-42-3 ∷ CS14 ∷ []) (CS14 ∷ Sb0-1-42-3 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 2 2 (CS13 ∷ Sw34 ∷ []) (lem-nat-3-CS14 (lit c4)) ▸
       at 1 2 (CS13 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS21-at2332 c4) ▸
       at 0 2 (CS14 ∷ Sw34 ∷ []) (lem-nat-3-CS13 (lit c4)) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | CS21 @0110243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS21-at0110243243 : Ws → ⟪ (Sb1-0-42-3 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS21-at0110243243 c4 = run b0
  where
  b0 : Chain (Sb1-0-42-3 ∷ CS04 ∷ []) (CS04 ∷ Sb1-0-42-3 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 2 2 (CS14 ∷ Sw01 ∷ []) (lem-nat-0-CS04 (lit c4)) ▸
       at 1 2 (CS14 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS21-at243243 c4) ▸
       at 0 2 (CS04 ∷ Sw01 ∷ []) (lem-nat-0-CS14 (lit c4)) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | CS21 @0210243143: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS21-at0210243143 : Ws → ⟪ (Sb2-0-41-3 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS21-at0210243143 c4 = run b0
  where
  b0 : Chain (Sb2-0-41-3 ∷ CS04 ∷ []) (CS04 ∷ Sb2-0-41-3 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·41·3⟩ (lit c4)) ▸
       at 2 2 (CS04 ∷ Sw12 ∷ []) (lem-nat-1-CS04 (lit c4)) ▸
       at 1 2 (CS04 ∷ Sb1-0-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS21-at0110243243 c4) ▸
       at 0 2 (CS04 ∷ Sw12 ∷ []) (lem-nat-1-CS04 (lit c4)) ▸
       at 1 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- F1 comm-CS-S0: 1 steps
lem-F1-comm-CS-S0 : Ws → ⟪ (Sb2-0-41-3 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-F1-comm-CS-S0 c4 = run b0
  where
  b0 : Chain (Sb2-0-41-3 ∷ CS04 ∷ []) (CS04 ∷ Sb2-0-41-3 ∷ [])
  b0 = at 0 2 (CS04 ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS21-at0210243143 c4) ▸ done


-- CS12-beta @122331: 7 steps
lem-CS12-beta-at122331 : Ws → ⟪ (CS23 ∷ Bx0-2314 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2314 ∷ CS23 ∷ []) ⟫ʷ
lem-CS12-beta-at122331 c4 = run b0
  where
  b0 : Chain (CS23 ∷ Bx0-2314 ∷ []) (Bx0-2314 ∷ CS23 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CS13 ∷ Sw12 ∷ []) (sym (wl0024 (lit c4))) ▸
       at 2 2 (Bx0-1324 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2314⟩ (lit c4)) ▸
       at 1 2 (Bx0-1324 ∷ CS13 ∷ []) (lem-CS12-beta-at2332 c4) ▸
       at 0 2 (Bx0-2314 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1324⟩ (lit c4)) ▸
       at 1 2 (CS23 ∷ Sw12 ∷ []) (sym (wl0025 (lit c4))) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto BOX(0;1234) | CS23: 5 steps
lem-auto-BOX⟨0·1234⟩-∣-CS23 : Ws → ⟪ (Bx0-1234 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS23 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ CS23 ∷ []) (CS23 ∷ Bx0-1234 ∷ [])
  b0 = at 0 1 (Bx0-2134 ∷ []) (lem-sym12 c4) ▸
       at 0 1 (Bx0-2314 ∷ []) (lem-sym23-at1221 c4) ▸
       at 0 2 (CS23 ∷ Bx0-2314 ∷ []) (sym (lem-CS12-beta-at122331 c4)) ▸
       at 1 1 (Bx0-2134 ∷ []) (lem-sym23-at122331 c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym12-at1221 c4) ▸ done


-- auto SBOX(0;1;23;4) | CS23: 11 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS23 : Ws → ⟪ (Sb0-1-23-4 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS23 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-1-23-4 ∷ CS23 ∷ []) (Bx0-1234 ∷ Toff423 ∷ CS23 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 4 1 (CS14⁻ ∷ []) (refl) ▸
       at 4 2 (CS23 ∷ CS14⁻ ∷ []) (wl0274 (lit c4)) ▸
       at 5 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 3 2 (CS23 ∷ Toff423 ∷ []) (sym (wl0275 (lit c4))) ▸
       at 2 1 (CS14 ∷ []) (refl) ▸
       at 2 2 (CS23 ∷ CS14 ∷ []) (wl0276 (lit c4)) ▸
       at 3 1 (Sb0-1-4-3 ∷ []) (refl) ▸ done

  b1 : Chain (Bx0-1234 ∷ Toff423 ∷ CS23 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (CS23 ∷ Sb0-1-23-4 ∷ [])
  b1 = at 1 2 (CS23 ∷ Toff423 ∷ []) (sym (wl0275 (lit c4))) ▸
       at 0 2 (CS23 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS23 c4) ▸
       at 1 5 (Sb0-1-23-4 ∷ []) (refl) ▸ done


-- auto SBOX(0;1;23;4) | CS23 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS23-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS23-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ CS23 ∷ []) (CS23 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 (CS23 ∷ Sw23 ∷ []) (sym (wl0152 (lit c4))) ▸
       at 1 2 (CS23 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS23 c4) ▸
       at 0 2 (CS23 ∷ Sw23 ∷ []) (sym (wl0152 (lit c4))) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | CS23 @243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS23-at243243 : Ws → ⟪ (Sb0-1-42-3 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS23-at243243 c4 = run b0
  where
  b0 : Chain (Sb0-1-42-3 ∷ CS24 ∷ []) (CS24 ∷ Sb0-1-42-3 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 2 2 (CS23 ∷ Sw34 ∷ []) (lem-nat-3-CS24 (lit c4)) ▸
       at 1 2 (CS23 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS23-at2332 c4) ▸
       at 0 2 (CS24 ∷ Sw34 ∷ []) (lem-nat-3-CS23 (lit c4)) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | CS23 @0110243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS23-at0110243243 : Ws → ⟪ (Sb1-0-42-3 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS23-at0110243243 c4 = run b0
  where
  b0 : Chain (Sb1-0-42-3 ∷ CS24 ∷ []) (CS24 ∷ Sb1-0-42-3 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 2 2 (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑)) ▸
       at 1 2 (CS24 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS23-at243243 c4) ▸
       at 0 2 (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑)) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | CS23 @0210243143: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS23-at0210243143 : Ws → ⟪ (Sb2-0-41-3 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS23-at0210243143 c4 = run b0
  where
  b0 : Chain (Sb2-0-41-3 ∷ CS14 ∷ []) (CS14 ∷ Sb2-0-41-3 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·41·3⟩ (lit c4)) ▸
       at 2 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0008 (lit c4))) ▸
       at 1 2 (CS24 ∷ Sb1-0-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS23-at0110243243 c4) ▸
       at 0 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0017 (lit c4))) ▸
       at 1 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- F1 comm-CS-S1: 1 steps
lem-F1-comm-CS-S1 : Ws → ⟪ (Sb2-0-41-3 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-F1-comm-CS-S1 c4 = run b0
  where
  b0 : Chain (Sb2-0-41-3 ∷ CS14 ∷ []) (CS14 ∷ Sb2-0-41-3 ∷ [])
  b0 = at 0 2 (CS14 ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS23-at0210243143 c4) ▸ done


-- auto BOX(0;1234) | CCZ324: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ324 : Ws → ⟪ (Bx0-1234 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ324 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ CCZ234 ∷ []) (CCZ234 ∷ Bx0-1234 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ []) (wl0255 (lit c4)) ▸
       at 0 1 (Bx0-2134 ∷ []) (lem-sym12 c4) ▸
       at 0 1 (Bx0-2314 ∷ []) (lem-sym23-at1221 c4) ▸
       at 0 2 (CCZ234 ∷ Bx0-2314 ∷ []) (sym (lem-c124-beta-at122331 c4)) ▸
       at 1 1 (Bx0-2134 ∷ []) (lem-sym23-at122331 c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym12-at1221 c4) ▸
       at 0 1 (CCZ234 ∷ []) (wl0255 (lit c4)) ▸ done


-- sym12 @0214213043: 5 steps
lem-sym12-at0214213043 : Ws → ⟪ (Bx2-4103 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1403 ∷ []) ⟫ʷ
lem-sym12-at0214213043 c4 = run b0
  where
  b0 : Chain (Bx2-4103 ∷ []) (Bx2-1403 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx2-4013 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·4103⟩ (lit c4)) ▸
       at 1 1 (Bx2-0413 ∷ []) (lem-sym12-at0214203143 c4) ▸
       at 0 2 (Bx2-1403 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·0413⟩ (lit c4)) ▸
       at 1 2 [] (wl0002 (lit c4)) ▸ done


-- CX23-beta @2332: 8 steps
lem-CX23-beta-at2332 : Ws → ⟪ (CX32 ∷ Bx0-1324 ∷ CX32 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ CCZ134 ∷ []) ⟫ʷ
lem-CX23-beta-at2332 c4 = run b0
  where
  b0 : Chain (CX32 ∷ Bx0-1324 ∷ CX32 ∷ []) (Bx0-1324 ∷ CCZ134 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (CX23 ∷ Sw23 ∷ []) (sym (wl0277 (lit c4))) ▸
       at 2 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ (lit c4)) ▸
       at 3 2 (CX23 ∷ Sw23 ∷ []) (sym (wl0277 (lit c4))) ▸
       at 1 3 (Bx0-1234 ∷ CCZ124 ∷ []) (lem-CX23-beta c4) ▸
       at 0 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ (lit c4)) ▸
       at 1 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- CX23-beta @243243: 8 steps
lem-CX23-beta-at243243 : Ws → ⟪ (CX42 ∷ Bx0-1423 ∷ CX42 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ CCZ134 ∷ []) ⟫ʷ
lem-CX23-beta-at243243 c4 = run b0
  where
  b0 : Chain (CX42 ∷ Bx0-1423 ∷ CX42 ∷ []) (Bx0-1423 ∷ CCZ134 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (CX32 ∷ Sw34 ∷ []) (lem-nat-3-CX42 (lit c4)) ▸
       at 2 2 (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ (lit c4)) ▸
       at 3 2 (CX32 ∷ Sw34 ∷ []) (lem-nat-3-CX42 (lit c4)) ▸
       at 1 3 (Bx0-1324 ∷ CCZ134 ∷ []) (lem-CX23-beta-at2332 c4) ▸
       at 0 2 (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ (lit c4)) ▸
       at 1 2 (CCZ134 ∷ Sw34 ∷ []) (sym (wl0154 (lit c4))) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- CX23-beta @0110243243: 8 steps
lem-CX23-beta-at0110243243 : Ws → ⟪ (CX42 ∷ Bx1-0423 ∷ CX42 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0423 ∷ CCZ034 ∷ []) ⟫ʷ
lem-CX23-beta-at0110243243 c4 = run b0
  where
  b0 : Chain (CX42 ∷ Bx1-0423 ∷ CX42 ∷ []) (Bx1-0423 ∷ CCZ034 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (CX42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CX₁₀ • Swap ↑)) ▸
       at 2 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4)) ▸
       at 3 2 (CX42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CX₁₀ • Swap ↑)) ▸
       at 1 3 (Bx0-1423 ∷ CCZ134 ∷ []) (lem-CX23-beta-at243243 c4) ▸
       at 0 2 (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ (lit c4)) ▸
       at 1 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- CX23-beta @0210243143: 8 steps
lem-CX23-beta-at0210243143 : Ws → ⟪ (CX41 ∷ Bx2-0413 ∷ CX41 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ CCZ034 ∷ []) ⟫ʷ
lem-CX23-beta-at0210243143 c4 = run b0
  where
  b0 : Chain (CX41 ∷ Bx2-0413 ∷ CX41 ∷ []) (Bx2-0413 ∷ CCZ034 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CX42 ∷ Sw12 ∷ []) (sym (wl0149 (lit c4))) ▸
       at 2 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4)) ▸
       at 3 2 (CX42 ∷ Sw12 ∷ []) (sym (wl0149 (lit c4))) ▸
       at 1 3 (Bx1-0423 ∷ CCZ034 ∷ []) (lem-CX23-beta-at0110243243 c4) ▸
       at 0 2 (Bx2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0423⟩ (lit c4)) ▸
       at 1 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- CX23-beta @02243043: 8 steps
lem-CX23-beta-at02243043 : Ws → ⟪ (CX40 ∷ Bx2-1403 ∷ CX40 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1403 ∷ CCZ134 ∷ []) ⟫ʷ
lem-CX23-beta-at02243043 c4 = run b0
  where
  b0 : Chain (CX40 ∷ Bx2-1403 ∷ CX40 ∷ []) (Bx2-1403 ∷ CCZ134 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (CX41 ∷ Sw01 ∷ []) (lem-nat-0-CX40 (lit c4)) ▸
       at 2 2 (Bx2-0413 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·1403⟩ (lit c4)) ▸
       at 3 2 (CX41 ∷ Sw01 ∷ []) (lem-nat-0-CX40 (lit c4)) ▸
       at 1 3 (Bx2-0413 ∷ CCZ034 ∷ []) (lem-CX23-beta-at0210243143 c4) ▸
       at 0 2 (Bx2-1403 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·0413⟩ (lit c4)) ▸
       at 1 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- sym12 @02243043: 5 steps
lem-sym12-at02243043 : Ws → ⟪ (Bx2-1403 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4103 ∷ []) ⟫ʷ
lem-sym12-at02243043 c4 = run b0
  where
  b0 : Chain (Bx2-1403 ∷ []) (Bx2-4103 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx2-0413 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·1403⟩ (lit c4)) ▸
       at 1 1 (Bx2-4013 ∷ []) (lem-sym12-at0210243143 c4) ▸
       at 0 2 (Bx2-4103 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·4013⟩ (lit c4)) ▸
       at 1 2 [] (wl0002 (lit c4)) ▸ done


-- auto BOX(0;1234) | CCZ324 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ324-at2332 : Ws → ⟪ (Bx0-1324 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ324-at2332 c4 = run b0
  where
  b0 : Chain (Bx0-1324 ∷ CCZ234 ∷ []) (CCZ234 ∷ Bx0-1324 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ (lit c4)) ▸
       at 2 2 (CCZ234 ∷ Sw23 ∷ []) (sym (wl0086 (lit c4))) ▸
       at 1 2 (CCZ234 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ324 c4) ▸
       at 0 2 (CCZ234 ∷ Sw23 ∷ []) (sym (wl0086 (lit c4))) ▸
       at 1 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done

