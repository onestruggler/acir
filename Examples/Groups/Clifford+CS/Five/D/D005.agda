{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D005 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0001 ; wl0002 ; wl0006 ; wl0007 ; wl0008 ; wl0011 ; wl0015 ; wl0017 ; wl0019 ; wl0022 ; wl0024 ; wl0025 ; wl0031 ; wl0034 ; wl0037 ; wl0039 ; wl0043 ; wl0046 ; wl0047 ; wl0056 ; wl0057 ; wl0058 ; wl0061 ; wl0062 ; wl0067 ; wl0068 ; wl0076 ; wl0078 ; wl0084 ; wl0099 ; wl0101 ; wl0104 ; wl0119 ; wl0120 ; wl0121 ; wl0132 ; wl0133 ; wl0154 ; wl0155 ; wl0257 ; wl0280 ; wl0281 ; wl0282 ; wl0306 ; wl0307 ; wl0308 ; wl0309 ; wl0310 ; wl0311 ; wl0312 ; wl0332 ; wl0360 ; wl0361 ; wl0362 ; wl0363 ; wl0364 ; wl0365 ; wl0366 ; wl0367 ; wl0368 ; wl0369 ; wl0370 ; wl0371 ; wp0045 ; wp0046 ; wp0113 ; wp0114 ; wp0123)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-CS20-beta-ci ; lem-T-beta ; lem-auto-TOFF012-∣-CCZ324 ; lem-beta-T ; lem-beta-T-at1221 ; lem-beta-T-at2332 ; lem-sym34 ; lem-sym34-at021021 ; lem-sym34-at3443)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-CS20-beta-c-at1221 ; lem-SBsym ; lem-SBsymd ; lem-X1-beta ; lem-sym12-at3443 ; lem-sym23-at011220 ; lem-sym23-at01122330 ; lem-sym23-at243243 ; lem-sym23-at3443 ; lem-sym34-at122331 ; lem-sym34-at12233441 ; lem-sym34-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-F5-CS01 ; lem-F5d-CS01 ; lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·1·23·4⟩ ; lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩ ; lem-auto-K0-∣-SBOX⟨1·2·34·0⟩ ; lem-auto-Kd0-∣-SBOX⟨1·2·34·0⟩ ; lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ124 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-CS24-at2332 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at2332 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd4-at2332 ; lem-auto-SBOX⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩ ; lem-auto-SBOXd⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-CS20-beta-c-at243243 ; lem-CS20-beta-ci-at243243 ; lem-auto-BOXd⟨0·1234⟩-∣-CS40 ; lem-auto-BOXd⟨0·1234⟩-∣-CSd40 ; lem-auto-CCZ012-∣-BOX⟨3·0142⟩ ; lem-auto-CCZ012-∣-SBOX⟨3·0·14·2⟩ ; lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·1234⟩ ; lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS24 ; lem-auto-SBOXd⟨0·1·23·4⟩-∣-K4 ; lem-auto-SBOXd⟨0·1·23·4⟩-∣-Kd4 ; lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨0·1·4·3⟩ ; lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨0·1·4·3⟩ ; lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF012)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-nat-1-BOX⟨0·2134⟩ ; lem-nat-1-CCZ024 ; lem-nat-1-CCZ034 ; lem-nat-2-BOX⟨0·1234⟩ ; lem-nat-2-BOX⟨0·1324⟩ ; lem-nat-2-CCZ012 ; lem-nat-2-CCZ013 ; lem-nat-2-CCZ024 ; lem-nat-2-CCZ034 ; lem-nat-2-TOFF012 ; lem-nat-2-TOFF013 ; lem-nat-3-BOX⟨0·1243⟩ ; lem-nat-3-BOX⟨0·1423⟩ ; lem-nat-3-CCZ014 ; lem-nat-3-CCZ034 ; lem-nat-3-TOFF013 ; lem-nat-3-TOFF014)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-0-CCZ024 ; lem-nat-0-CCZ124 ; lem-nat-1-CCZ014 ; lem-nat-1-TOFF103 ; lem-nat-2-CCZ124 ; lem-nat-2-CCZ134 ; lem-nat-3-BOX⟨0·1324⟩ ; lem-nat-3-CCZ013)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-0-CCZ034 ; lem-nat-0-CCZ134 ; lem-nat-0-TOFF014 ; lem-nat-0-TOFF104 ; lem-nat-1-TOFF104 ; lem-nat-1-TOFF204)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-1-BOX⟨0·1234⟩)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-0-BOX⟨0·1243⟩ ; lem-nat-0-BOX⟨0·1423⟩ ; lem-nat-0-BOX⟨1·0243⟩ ; lem-nat-0-BOX⟨1·0423⟩ ; lem-nat-1-BOX⟨1·0243⟩ ; lem-nat-1-BOX⟨1·0423⟩ ; lem-nat-1-BOX⟨2·0143⟩ ; lem-nat-1-BOX⟨2·0413⟩ ; lem-nat-3-BOX⟨0·1234⟩)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-0-BOX⟨0·2134⟩ ; lem-nat-0-BOX⟨0·2143⟩ ; lem-nat-0-BOX⟨0·2314⟩ ; lem-nat-0-BOX⟨1·2034⟩ ; lem-nat-0-BOX⟨1·2304⟩ ; lem-nat-0-BOXd⟨1·0423⟩ ; lem-nat-1-BOXd⟨2·0413⟩ ; lem-nat-1-CS01 ; lem-nat-1-CS02 ; lem-nat-2-BOX⟨0·1243⟩ ; lem-nat-2-BOX⟨0·1342⟩ ; lem-nat-2-BOXd⟨0·1324⟩ ; lem-nat-3-BOXd⟨0·1423⟩)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-0-BOX⟨0·1342⟩ ; lem-nat-0-CS04 ; lem-nat-0-CS14 ; lem-nat-0-SBOX⟨0·1·3·2⟩ ; lem-nat-0-SBOX⟨0·1·42·3⟩ ; lem-nat-0-SBOX⟨1·0·3·2⟩ ; lem-nat-0-SBOX⟨1·0·42·3⟩ ; lem-nat-0-SBOXd⟨0·1·3·2⟩ ; lem-nat-0-SBOXd⟨1·0·3·2⟩ ; lem-nat-1-CS04 ; lem-nat-1-CSd02 ; lem-nat-1-SBOX⟨1·0·3·2⟩ ; lem-nat-1-SBOX⟨1·0·42·3⟩ ; lem-nat-1-SBOX⟨2·0·3·1⟩ ; lem-nat-1-SBOX⟨2·0·41·3⟩ ; lem-nat-1-SBOXd⟨1·0·3·2⟩ ; lem-nat-1-SBOXd⟨2·0·3·1⟩ ; lem-nat-2-BOX⟨0·1432⟩ ; lem-nat-2-BOX⟨1·0432⟩ ; lem-nat-2-CS02 ; lem-nat-2-SBOX⟨0·1·23·4⟩ ; lem-nat-2-SBOX⟨0·1·32·4⟩ ; lem-nat-2-SBOX⟨0·1·4·2⟩ ; lem-nat-2-SBOX⟨0·1·4·3⟩ ; lem-nat-2-SBOX⟨1·0·43·2⟩ ; lem-nat-2-SBOXd⟨0·1·4·2⟩ ; lem-nat-2-SBOXd⟨0·1·4·3⟩ ; lem-nat-3-BOX⟨2·0431⟩ ; lem-nat-3-SBOX⟨0·1·32·4⟩ ; lem-nat-3-SBOX⟨0·1·3·2⟩ ; lem-nat-3-SBOX⟨0·1·42·3⟩ ; lem-nat-3-SBOX⟨0·1·4·2⟩ ; lem-nat-3-SBOX⟨1·0·34·2⟩ ; lem-nat-3-SBOX⟨2·0·43·1⟩ ; lem-nat-3-SBOXd⟨0·1·3·2⟩ ; lem-nat-3-SBOXd⟨0·1·4·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-nat-0-BOX⟨1·0324⟩ ; lem-nat-0-BOX⟨1·0342⟩ ; lem-nat-0-BOX⟨1·2340⟩ ; lem-nat-1-BOX⟨1·0342⟩ ; lem-nat-1-BOX⟨2·0314⟩ ; lem-nat-1-BOX⟨2·0341⟩ ; lem-nat-1-CSd01 ; lem-nat-1-CSd04 ; lem-nat-2-CS04 ; lem-nat-2-CSd04 ; lem-nat-3-CS04 ; lem-nat-3-CSd04)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-0-BOX⟨2·1034⟩ ; lem-nat-0-BOX⟨2·1304⟩ ; lem-nat-2-BOX⟨0·1423⟩ ; lem-nat-2-BOXd⟨0·1234⟩ ; lem-nat-2-CS03 ; lem-nat-2-CSd03 ; lem-nat-2-SBOX⟨0·1·2·3⟩ ; lem-nat-2-SBOX⟨0·1·3·2⟩ ; lem-nat-2-SBOXd⟨0·1·23·4⟩ ; lem-nat-2-SBOXd⟨0·1·2·3⟩ ; lem-nat-2-SBOXd⟨0·1·32·4⟩ ; lem-nat-2-SBOXd⟨0·1·3·2⟩ ; lem-nat-3-CS03 ; lem-nat-3-CSd03)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-nat-0-BOX⟨0·2341⟩ ; lem-nat-0-SBOX⟨0·2·43·1⟩ ; lem-nat-0-SBOX⟨1·2·43·0⟩ ; lem-nat-0-SBOX⟨2·3·04·1⟩ ; lem-nat-0-SBOX⟨2·3·14·0⟩ ; lem-nat-1-SBOX⟨0·1·43·2⟩ ; lem-nat-1-SBOX⟨0·2·43·1⟩ ; lem-nat-1-SBOX⟨1·3·24·0⟩ ; lem-nat-1-SBOX⟨2·0·14·3⟩ ; lem-nat-2-SBOX⟨0·1·42·3⟩ ; lem-nat-2-SBOX⟨0·1·43·2⟩ ; lem-nat-2-SBOX⟨1·0·24·3⟩ ; lem-nat-3-SBOX⟨1·2·34·0⟩ ; lem-nat-3-SBOX⟨1·2·43·0⟩)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-nat-0-BOX⟨0·1432⟩ ; lem-nat-0-BOX⟨1·0432⟩ ; lem-nat-0-BOX⟨2·0143⟩ ; lem-nat-0-BOX⟨2·1043⟩ ; lem-nat-0-BOXd⟨0·1423⟩ ; lem-nat-0-SBOXd⟨0·1·42·3⟩ ; lem-nat-0-SBOXd⟨1·0·42·3⟩ ; lem-nat-1-BOX⟨1·0432⟩ ; lem-nat-1-BOX⟨1·2043⟩ ; lem-nat-1-BOX⟨2·0431⟩ ; lem-nat-1-BOX⟨3·0142⟩ ; lem-nat-1-BOX⟨3·0241⟩ ; lem-nat-1-BOXd⟨1·0423⟩ ; lem-nat-1-SBOX⟨1·0·43·2⟩ ; lem-nat-1-SBOX⟨2·0·43·1⟩ ; lem-nat-1-SBOX⟨2·3·14·0⟩ ; lem-nat-1-SBOX⟨3·0·14·2⟩ ; lem-nat-1-SBOX⟨3·0·24·1⟩ ; lem-nat-1-SBOXd⟨1·0·24·3⟩ ; lem-nat-1-SBOXd⟨1·0·42·3⟩ ; lem-nat-1-SBOXd⟨2·0·14·3⟩ ; lem-nat-1-SBOXd⟨2·0·41·3⟩ ; lem-nat-2-BOX⟨1·0423⟩ ; lem-nat-2-BOX⟨2·0341⟩ ; lem-nat-2-BOX⟨3·0241⟩ ; lem-nat-2-SBOX⟨1·0·42·3⟩ ; lem-nat-2-SBOX⟨1·2·34·0⟩ ; lem-nat-2-SBOX⟨1·3·24·0⟩ ; lem-nat-2-SBOX⟨2·0·34·1⟩ ; lem-nat-2-SBOX⟨3·0·24·1⟩ ; lem-nat-2-SBOXd⟨1·0·24·3⟩ ; lem-nat-2-SBOXd⟨1·0·34·2⟩ ; lem-nat-2-SBOXd⟨1·0·42·3⟩ ; lem-nat-2-SBOXd⟨1·0·43·2⟩ ; lem-nat-3-BOX⟨0·1342⟩ ; lem-nat-3-BOX⟨2·0341⟩ ; lem-nat-3-BOXd⟨0·1324⟩ ; lem-nat-3-SBOX⟨2·0·34·1⟩ ; lem-nat-3-SBOXd⟨0·1·32·4⟩ ; lem-nat-3-SBOXd⟨0·1·42·3⟩ ; lem-nat-3-SBOXd⟨1·0·34·2⟩ ; lem-nat-3-SBOXd⟨1·0·43·2⟩)
-- auto BOX(0;1234) | CS40: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS40 : Ws → ⟪ (Bx0-1234 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS40 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ CS04 ∷ []) (CS04 ∷ Bx0-1234 ∷ [])
  b0 = at 1 1 (CS04 ∷ []) (wp0113 c4) ▸
       at 0 1 (Bx0-1243 ∷ []) (lem-sym34 c4) ▸
       at 0 1 (Bx0-1423 ∷ []) (lem-sym23-at3443 c4) ▸
       at 0 2 (CS04 ∷ Bx0-1423 ∷ []) (sym (lem-CS20-beta-c-at243243 c4)) ▸
       at 1 1 (Bx0-1243 ∷ []) (lem-sym23-at243243 c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym34-at3443 c4) ▸
       at 0 1 (CS04 ∷ []) (wp0113 c4) ▸ done


-- auto BOX(0;1234) | CSd40: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd40 : Ws → ⟪ (Bx0-1234 ∷ CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS04⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd40 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ Bx0-1234 ∷ [])
  b0 = at 1 1 (CS04⁻ ∷ []) (wp0114 c4) ▸
       at 0 1 (Bx0-1243 ∷ []) (lem-sym34 c4) ▸
       at 0 1 (Bx0-1423 ∷ []) (lem-sym23-at3443 c4) ▸
       at 0 2 (CS04⁻ ∷ Bx0-1423 ∷ []) (sym (lem-CS20-beta-ci-at243243 c4)) ▸
       at 1 1 (Bx0-1243 ∷ []) (lem-sym23-at243243 c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym34-at3443 c4) ▸
       at 0 1 (CS04⁻ ∷ []) (wp0114 c4) ▸ done


-- beta-T @011220: 8 steps
lem-beta-T-at011220 : Ws → ⟪ (Bx1-2034 ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ CCZ134 ∷ Toff102 ∷ CCZ134 ∷ []) ⟫ʷ
lem-beta-T-at011220 c4 = run b0
  where
  b0 : Chain (Bx1-2034 ∷ []) (Toff102 ∷ CCZ134 ∷ Toff102 ∷ CCZ134 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx0-2134 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·2034⟩ (lit c4)) ▸
       at 1 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-beta-T-at1221 c4) ▸
       at 0 2 (Toff102 ∷ Sw01 ∷ []) (wl0099 (lit c4)) ▸
       at 1 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 (lit c4)) ▸
       at 2 2 (Toff102 ∷ Sw01 ∷ []) (wl0099 (lit c4)) ▸
       at 3 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 (lit c4)) ▸
       at 4 2 [] (wl0002 (lit c4)) ▸ done


-- auto Sd0 | BOX(1;2034): 6 steps
lem-auto-Sd0-∣-BOX⟨1·2034⟩ : Ws → ⟪ (S0⁻ ∷ Bx1-2034 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2034 ∷ S0⁻ ∷ []) ⟫ʷ
lem-auto-Sd0-∣-BOX⟨1·2034⟩ c4 = run b0
  where
  b0 : Chain (S0⁻ ∷ Bx1-2034 ∷ []) (Bx1-2034 ∷ S0⁻ ∷ [])
  b0 = at 1 1 (Toff102 ∷ CCZ134 ∷ Toff102 ∷ CCZ134 ∷ []) (lem-beta-T-at011220 c4) ▸
       at 0 2 (Toff102 ∷ S0⁻ ∷ []) (wl0361 (lit c4)) ▸
       at 1 2 (CCZ134 ∷ S0⁻ ∷ []) (c₁ (S • S • S) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑)) ▸
       at 2 2 (Toff102 ∷ S0⁻ ∷ []) (wl0361 (lit c4)) ▸
       at 3 2 (CCZ134 ∷ S0⁻ ∷ []) (c₁ (S • S • S) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑)) ▸
       at 0 4 (Bx1-2034 ∷ []) (sym (lem-beta-T-at011220 c4)) ▸ done


-- auto Sd0 | SBOX(1;2;03;4): 11 steps
lem-auto-Sd0-∣-SBOX⟨1·2·03·4⟩ : Ws → ⟪ (S0⁻ ∷ Sb1-2-03-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-03-4 ∷ S0⁻ ∷ []) ⟫ʷ
lem-auto-Sd0-∣-SBOX⟨1·2·03·4⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (S0⁻ ∷ Sb1-2-03-4 ∷ []) (Bx1-2034 ∷ Toff403 ∷ Sb1-2-4-3 ∷ Toff403 ∷ S0⁻ ∷ CS24⁻ ∷ [])
  b0 = at 1 1 (Bx1-2034 ∷ Toff403 ∷ Sb1-2-4-3 ∷ Toff403 ∷ Sb⁻1-2-4-3 ∷ []) (refl) ▸
       at 0 2 (Bx1-2034 ∷ S0⁻ ∷ []) (lem-auto-Sd0-∣-BOX⟨1·2034⟩ c4) ▸
       at 1 2 (Toff403 ∷ S0⁻ ∷ []) (wp0123 c4) ▸
       at 3 1 (CS24 ∷ []) (refl) ▸
       at 2 2 (CS24 ∷ S0⁻ ∷ []) (sym (wl0362 (lit c4))) ▸
       at 2 1 (Sb1-2-4-3 ∷ []) (refl) ▸
       at 3 2 (Toff403 ∷ S0⁻ ∷ []) (wp0123 c4) ▸
       at 5 1 (CS24⁻ ∷ []) (refl) ▸ done

  b1 : Chain (Bx1-2034 ∷ Toff403 ∷ Sb1-2-4-3 ∷ Toff403 ∷ S0⁻ ∷ CS24⁻ ∷ []) (Sb1-2-03-4 ∷ S0⁻ ∷ [])
  b1 = at 4 2 (CS24⁻ ∷ S0⁻ ∷ []) (sym (wl0363 (lit c4))) ▸
       at 4 1 (Sb⁻1-2-4-3 ∷ []) (refl) ▸
       at 0 5 (Sb1-2-03-4 ∷ []) (refl) ▸ done


-- sym34 @0112233440: 5 steps
lem-sym34-at0112233440 : Ws → ⟪ (Bx1-2340 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2304 ∷ []) ⟫ʷ
lem-sym34-at0112233440 c4 = run b0
  where
  b0 : Chain (Bx1-2340 ∷ []) (Bx1-2304 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx0-2341 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·2340⟩ (lit c4)) ▸
       at 1 1 (Bx0-2314 ∷ []) (lem-sym34-at12233441 c4) ▸
       at 0 2 (Bx1-2304 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·2314⟩ (lit c4)) ▸
       at 1 2 [] (wl0002 (lit c4)) ▸ done


-- CS20-beta-ci @1221: 7 steps
lem-CS20-beta-ci-at1221 : Ws → ⟪ (CS01⁻ ∷ Bx0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ CS01⁻ ∷ []) ⟫ʷ
lem-CS20-beta-ci-at1221 c4 = run b0
  where
  b0 : Chain (CS01⁻ ∷ Bx0-2134 ∷ []) (Bx0-2134 ∷ CS01⁻ ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CS02⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd01 (lit c4)) ▸
       at 2 2 (Bx0-1234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2134⟩ (lit c4)) ▸
       at 1 2 (Bx0-1234 ∷ CS02⁻ ∷ []) (lem-CS20-beta-ci c4) ▸
       at 0 2 (Bx0-2134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1234⟩ (lit c4)) ▸
       at 1 2 (CS01⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd02 (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- CS20-beta-ci @011220: 7 steps
lem-CS20-beta-ci-at011220 : Ws → ⟪ (CS01⁻ ∷ Bx1-2034 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2034 ∷ CS01⁻ ∷ []) ⟫ʷ
lem-CS20-beta-ci-at011220 c4 = run b0
  where
  b0 : Chain (CS01⁻ ∷ Bx1-2034 ∷ []) (Bx1-2034 ∷ CS01⁻ ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (CS01⁻ ∷ Sw01 ∷ []) (sym (wl0133 (lit c4))) ▸
       at 2 2 (Bx0-2134 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·2034⟩ (lit c4)) ▸
       at 1 2 (Bx0-2134 ∷ CS01⁻ ∷ []) (lem-CS20-beta-ci-at1221 c4) ▸
       at 0 2 (Bx1-2034 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·2134⟩ (lit c4)) ▸
       at 1 2 (CS01⁻ ∷ Sw01 ∷ []) (sym (wl0133 (lit c4))) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- sym34 @01122330: 5 steps
lem-sym34-at01122330 : Ws → ⟪ (Bx1-2304 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2340 ∷ []) ⟫ʷ
lem-sym34-at01122330 c4 = run b0
  where
  b0 : Chain (Bx1-2304 ∷ []) (Bx1-2340 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx0-2314 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·2304⟩ (lit c4)) ▸
       at 1 1 (Bx0-2341 ∷ []) (lem-sym34-at122331 c4) ▸
       at 0 2 (Bx1-2340 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·2341⟩ (lit c4)) ▸
       at 1 2 [] (wl0002 (lit c4)) ▸ done


-- auto CSd01 | BOX(1;2340): 7 steps
lem-auto-CSd01-∣-BOX⟨1·2340⟩ : Ws → ⟪ (CS01⁻ ∷ Bx1-2340 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2340 ∷ CS01⁻ ∷ []) ⟫ʷ
lem-auto-CSd01-∣-BOX⟨1·2340⟩ c4 = run b0
  where
  b0 : Chain (CS01⁻ ∷ Bx1-2340 ∷ []) (Bx1-2340 ∷ CS01⁻ ∷ [])
  b0 = at 0 1 (CS01⁻ ∷ []) (wl0360 (lit c4)) ▸
       at 1 1 (Bx1-2304 ∷ []) (lem-sym34-at0112233440 c4) ▸
       at 1 1 (Bx1-2034 ∷ []) (lem-sym23-at01122330 c4) ▸
       at 0 2 (Bx1-2034 ∷ CS01⁻ ∷ []) (lem-CS20-beta-ci-at011220 c4) ▸
       at 0 1 (Bx1-2304 ∷ []) (lem-sym23-at011220 c4) ▸
       at 0 1 (Bx1-2340 ∷ []) (lem-sym34-at01122330 c4) ▸
       at 1 1 (CS01⁻ ∷ []) (wl0360 (lit c4)) ▸ done


-- CS20-beta-c @011220: 7 steps
lem-CS20-beta-c-at011220 : Ws → ⟪ (CS01 ∷ Bx1-2034 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2034 ∷ CS01 ∷ []) ⟫ʷ
lem-CS20-beta-c-at011220 c4 = run b0
  where
  b0 : Chain (CS01 ∷ Bx1-2034 ∷ []) (Bx1-2034 ∷ CS01 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (CS01 ∷ Sw01 ∷ []) (sym (wl0132 (lit c4))) ▸
       at 2 2 (Bx0-2134 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·2034⟩ (lit c4)) ▸
       at 1 2 (Bx0-2134 ∷ CS01 ∷ []) (lem-CS20-beta-c-at1221 c4) ▸
       at 0 2 (Bx1-2034 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·2134⟩ (lit c4)) ▸
       at 1 2 (CS01 ∷ Sw01 ∷ []) (sym (wl0132 (lit c4))) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto CS01 | BOX(1;2340): 7 steps
lem-auto-CS01-∣-BOX⟨1·2340⟩ : Ws → ⟪ (CS01 ∷ Bx1-2340 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2340 ∷ CS01 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨1·2340⟩ c4 = run b0
  where
  b0 : Chain (CS01 ∷ Bx1-2340 ∷ []) (Bx1-2340 ∷ CS01 ∷ [])
  b0 = at 0 1 (CS01 ∷ []) (wl0332 (lit c4)) ▸
       at 1 1 (Bx1-2304 ∷ []) (lem-sym34-at0112233440 c4) ▸
       at 1 1 (Bx1-2034 ∷ []) (lem-sym23-at01122330 c4) ▸
       at 0 2 (Bx1-2034 ∷ CS01 ∷ []) (lem-CS20-beta-c-at011220 c4) ▸
       at 0 1 (Bx1-2304 ∷ []) (lem-sym23-at011220 c4) ▸
       at 0 1 (Bx1-2340 ∷ []) (lem-sym34-at01122330 c4) ▸
       at 1 1 (CS01 ∷ []) (wl0332 (lit c4)) ▸ done


-- auto TOFF012 | BOX(0;1234): 1 steps
lem-auto-TOFF012-∣-BOX⟨0·1234⟩ : Ws → ⟪ (Toff012 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ Toff012 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-BOX⟨0·1234⟩ c4 = run b0
  where
  b0 : Chain (Toff012 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ Toff012 ∷ [])
  b0 = at 0 2 (Bx0-1234 ∷ Toff012 ∷ []) (lem-T-beta c4) ▸ done


-- auto TOFF012 | TOFF324: 5 steps
lem-auto-TOFF012-∣-TOFF324 : Ws → ⟪ (Toff012 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ Toff012 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-TOFF324 c4 = run b0
  where
  b0 : Chain (Toff012 ∷ Toff324 ∷ []) (Toff324 ∷ Toff012 ∷ [])
  b0 = at 1 1 (K3 ∷ CCZ234 ∷ K3⁻ ∷ []) (sym (wl0364 (lit c4))) ▸
       at 0 2 (K3 ∷ Toff012 ∷ []) (sym (wl0365 (lit c4))) ▸
       at 1 2 (CCZ234 ∷ Toff012 ∷ []) (lem-auto-TOFF012-∣-CCZ324 c4) ▸
       at 2 2 (K3⁻ ∷ Toff012 ∷ []) (sym (wl0366 (lit c4))) ▸
       at 0 3 (Toff324 ∷ []) (wl0364 (lit c4)) ▸ done


-- auto TOFF012 | TOFF324 @3443: 7 steps
lem-auto-TOFF012-∣-TOFF324-at3443 : Ws → ⟪ (Toff012 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ Toff012 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-TOFF324-at3443 c4 = run b0
  where
  b0 : Chain (Toff012 ∷ Toff423 ∷ []) (Toff423 ∷ Toff012 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Toff012 ∷ Sw34 ∷ []) (sym (c₃ (Toff) (Swap))) ▸
       at 2 2 (Toff324 ∷ Sw34 ∷ []) (wl0120 (lit c4)) ▸
       at 1 2 (Toff324 ∷ Toff012 ∷ []) (lem-auto-TOFF012-∣-TOFF324 c4) ▸
       at 0 2 (Toff423 ∷ Sw34 ∷ []) (wl0119 (lit c4)) ▸
       at 1 2 (Toff012 ∷ Sw34 ∷ []) (sym (c₃ (Toff) (Swap))) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto TOFF012 | SBOX(0;1;23;4): 11 steps
lem-auto-TOFF012-∣-SBOX⟨0·1·23·4⟩ : Ws → ⟪ (Toff012 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-23-4 ∷ Toff012 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-SBOX⟨0·1·23·4⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff012 ∷ Sb0-1-23-4 ∷ []) (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Toff012 ∷ CS14⁻ ∷ [])
  b0 = at 1 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 0 2 (Bx0-1234 ∷ Toff012 ∷ []) (lem-auto-TOFF012-∣-BOX⟨0·1234⟩ c4) ▸
       at 1 2 (Toff423 ∷ Toff012 ∷ []) (lem-auto-TOFF012-∣-TOFF324-at3443 c4) ▸
       at 3 1 (CS14 ∷ []) (refl) ▸
       at 2 2 (CS14 ∷ Toff012 ∷ []) (sym (wp0046 c4)) ▸
       at 2 1 (Sb0-1-4-3 ∷ []) (refl) ▸
       at 3 2 (Toff423 ∷ Toff012 ∷ []) (lem-auto-TOFF012-∣-TOFF324-at3443 c4) ▸
       at 5 1 (CS14⁻ ∷ []) (refl) ▸ done

  b1 : Chain (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Toff012 ∷ CS14⁻ ∷ []) (Sb0-1-23-4 ∷ Toff012 ∷ [])
  b1 = at 4 2 (CS14⁻ ∷ Toff012 ∷ []) (sym (wp0045 c4)) ▸
       at 4 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 0 5 (Sb0-1-23-4 ∷ []) (refl) ▸ done


-- F5 CS01 @1221: 8 steps
lem-F5-CS01-at1221 : Ws → ⟪ (X4 ∷ Sb1-0-42-3 ∷ X4 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ []) ⟫ʷ
lem-F5-CS01-at1221 c4 = run b0
  where
  b0 : Chain (X4 ∷ Sb1-0-42-3 ∷ X4 ∷ Sb1-0-42-3 ∷ []) (CS02 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (X4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (X ↑)) ▸
       at 2 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 3 2 (X4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (X ↑)) ▸
       at 4 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 1 4 (CS01 ∷ []) (lem-F5-CS01 c4) ▸
       at 0 2 (CS02 ∷ Sw12 ∷ []) (lem-nat-1-CS01 (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- F5 CS01 @132132: 8 steps
lem-F5-CS01-at132132 : Ws → ⟪ (X4 ∷ Sb1-0-43-2 ∷ X4 ∷ Sb1-0-43-2 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ []) ⟫ʷ
lem-F5-CS01-at132132 c4 = run b0
  where
  b0 : Chain (X4 ∷ Sb1-0-43-2 ∷ X4 ∷ Sb1-0-43-2 ∷ []) (CS03 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (X4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (X)) ▸
       at 2 2 (Sb1-0-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·43·2⟩ (lit c4)) ▸
       at 3 2 (X4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (X)) ▸
       at 4 2 (Sb1-0-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·43·2⟩ (lit c4)) ▸
       at 1 4 (CS02 ∷ []) (lem-F5-CS01-at1221 c4) ▸
       at 0 2 (CS03 ∷ Sw23 ∷ []) (lem-nat-2-CS02 (lit c4)) ▸
       at 1 2 [] (wl0006 (lit c4)) ▸ done


-- F5 CS01 @14213243: 8 steps
lem-F5-CS01-at14213243 : Ws → ⟪ (X3 ∷ Sb1-0-34-2 ∷ X3 ∷ Sb1-0-34-2 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ []) ⟫ʷ
lem-F5-CS01-at14213243 c4 = run b0
  where
  b0 : Chain (X3 ∷ Sb1-0-34-2 ∷ X3 ∷ Sb1-0-34-2 ∷ []) (CS04 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (X4 ∷ Sw34 ∷ []) (wl0367 (lit c4)) ▸
       at 2 2 (Sb1-0-43-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨1·0·34·2⟩ (lit c4)) ▸
       at 3 2 (X4 ∷ Sw34 ∷ []) (wl0367 (lit c4)) ▸
       at 4 2 (Sb1-0-43-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨1·0·34·2⟩ (lit c4)) ▸
       at 1 4 (CS03 ∷ []) (lem-F5-CS01-at132132 c4) ▸
       at 0 2 (CS04 ∷ Sw34 ∷ []) (lem-nat-3-CS03 (lit c4)) ▸
       at 1 2 [] (wl0007 (lit c4)) ▸ done


-- F5 CS01 @142142: 8 steps
lem-F5-CS01-at142142 : Ws → ⟪ (X2 ∷ Sb1-0-24-3 ∷ X2 ∷ Sb1-0-24-3 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ []) ⟫ʷ
lem-F5-CS01-at142142 c4 = run b0
  where
  b0 : Chain (X2 ∷ Sb1-0-24-3 ∷ X2 ∷ Sb1-0-24-3 ∷ []) (CS04 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (X3 ∷ Sw23 ∷ []) (wl0368 (lit c4)) ▸
       at 2 2 (Sb1-0-34-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·24·3⟩ (lit c4)) ▸
       at 3 2 (X3 ∷ Sw23 ∷ []) (wl0368 (lit c4)) ▸
       at 4 2 (Sb1-0-34-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·24·3⟩ (lit c4)) ▸
       at 1 4 (CS04 ∷ []) (lem-F5-CS01-at14213243 c4) ▸
       at 0 2 (CS04 ∷ Sw23 ∷ []) (lem-nat-2-CS04 (lit c4)) ▸
       at 1 2 [] (wl0006 (lit c4)) ▸ done


-- F5 CS01 @1441: 8 steps
lem-F5-CS01-at1441 : Ws → ⟪ (X1 ∷ Sb2-0-14-3 ∷ X1 ∷ Sb2-0-14-3 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ []) ⟫ʷ
lem-F5-CS01-at1441 c4 = run b0
  where
  b0 : Chain (X1 ∷ Sb2-0-14-3 ∷ X1 ∷ Sb2-0-14-3 ∷ []) (CS04 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (X2 ∷ Sw12 ∷ []) (wl0369 (lit c4)) ▸
       at 2 2 (Sb1-0-24-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·14·3⟩ (lit c4)) ▸
       at 3 2 (X2 ∷ Sw12 ∷ []) (wl0369 (lit c4)) ▸
       at 4 2 (Sb1-0-24-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·14·3⟩ (lit c4)) ▸
       at 1 4 (CS04 ∷ []) (lem-F5-CS01-at142142 c4) ▸
       at 0 2 (CS04 ∷ Sw12 ∷ []) (lem-nat-1-CS04 (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- SBsym @1221: 5 steps
lem-SBsym-at1221 : Ws → ⟪ (Sb1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-24-3 ∷ []) ⟫ʷ
lem-SBsym-at1221 c4 = run b0
  where
  b0 : Chain (Sb1-0-42-3 ∷ []) (Sb1-0-24-3 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 1 1 (Sb2-0-14-3 ∷ []) (lem-SBsym c4) ▸
       at 0 2 (Sb1-0-24-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·14·3⟩ (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- SBsym @132132: 5 steps
lem-SBsym-at132132 : Ws → ⟪ (Sb1-0-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-34-2 ∷ []) ⟫ʷ
lem-SBsym-at132132 c4 = run b0
  where
  b0 : Chain (Sb1-0-43-2 ∷ []) (Sb1-0-34-2 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·43·2⟩ (lit c4)) ▸
       at 1 1 (Sb1-0-24-3 ∷ []) (lem-SBsym-at1221 c4) ▸
       at 0 2 (Sb1-0-34-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·24·3⟩ (lit c4)) ▸
       at 1 2 [] (wl0006 (lit c4)) ▸ done


-- SBsym @14213243: 5 steps
lem-SBsym-at14213243 : Ws → ⟪ (Sb1-0-34-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-43-2 ∷ []) ⟫ʷ
lem-SBsym-at14213243 c4 = run b0
  where
  b0 : Chain (Sb1-0-34-2 ∷ []) (Sb1-0-43-2 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Sb1-0-43-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨1·0·34·2⟩ (lit c4)) ▸
       at 1 1 (Sb1-0-34-2 ∷ []) (lem-SBsym-at132132 c4) ▸
       at 0 2 (Sb1-0-43-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨1·0·34·2⟩ (lit c4)) ▸
       at 1 2 [] (wl0007 (lit c4)) ▸ done


-- SBsym @142142: 5 steps
lem-SBsym-at142142 : Ws → ⟪ (Sb1-0-24-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-42-3 ∷ []) ⟫ʷ
lem-SBsym-at142142 c4 = run b0
  where
  b0 : Chain (Sb1-0-24-3 ∷ []) (Sb1-0-42-3 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb1-0-34-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·24·3⟩ (lit c4)) ▸
       at 1 1 (Sb1-0-43-2 ∷ []) (lem-SBsym-at14213243 c4) ▸
       at 0 2 (Sb1-0-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·43·2⟩ (lit c4)) ▸
       at 1 2 [] (wl0006 (lit c4)) ▸ done


-- SBsym @1441: 5 steps
lem-SBsym-at1441 : Ws → ⟪ (Sb2-0-14-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ []) ⟫ʷ
lem-SBsym-at1441 c4 = run b0
  where
  b0 : Chain (Sb2-0-14-3 ∷ []) (Sb2-0-41-3 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Sb1-0-24-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·14·3⟩ (lit c4)) ▸
       at 1 1 (Sb1-0-42-3 ∷ []) (lem-SBsym-at142142 c4) ▸
       at 0 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- beta-T @3443: 8 steps
lem-beta-T-at3443 : Ws → ⟪ (Bx0-1243 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) ⟫ʷ
lem-beta-T-at3443 c4 = run b0
  where
  b0 : Chain (Bx0-1243 ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Bx0-1234 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1243⟩ (lit c4)) ▸
       at 1 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-beta-T c4) ▸
       at 0 2 (Toff012 ∷ Sw34 ∷ []) (sym (c₃ (Toff) (Swap))) ▸
       at 1 2 (CCZ034 ∷ Sw34 ∷ []) (lem-nat-3-CCZ034 (lit c4)) ▸
       at 2 2 (Toff012 ∷ Sw34 ∷ []) (sym (c₃ (Toff) (Swap))) ▸
       at 3 2 (CCZ034 ∷ Sw34 ∷ []) (lem-nat-3-CCZ034 (lit c4)) ▸
       at 4 2 [] (wl0007 (lit c4)) ▸ done


-- beta-T @01103443: 8 steps
lem-beta-T-at01103443 : Ws → ⟪ (Bx1-0243 ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ CCZ134 ∷ Toff102 ∷ CCZ134 ∷ []) ⟫ʷ
lem-beta-T-at01103443 c4 = run b0
  where
  b0 : Chain (Bx1-0243 ∷ []) (Toff102 ∷ CCZ134 ∷ Toff102 ∷ CCZ134 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx0-1243 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0243⟩ (lit c4)) ▸
       at 1 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-beta-T-at3443 c4) ▸
       at 0 2 (Toff102 ∷ Sw01 ∷ []) (wl0099 (lit c4)) ▸
       at 1 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 (lit c4)) ▸
       at 2 2 (Toff102 ∷ Sw01 ∷ []) (wl0099 (lit c4)) ▸
       at 3 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 (lit c4)) ▸
       at 4 2 [] (wl0002 (lit c4)) ▸ done


-- beta-T @0210213443: 8 steps
lem-beta-T-at0210213443 : Ws → ⟪ (Bx2-0143 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) ⟫ʷ
lem-beta-T-at0210213443 c4 = run b0
  where
  b0 : Chain (Bx2-0143 ∷ []) (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx1-0243 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0143⟩ (lit c4)) ▸
       at 1 1 (Toff102 ∷ CCZ134 ∷ Toff102 ∷ CCZ134 ∷ []) (lem-beta-T-at01103443 c4) ▸
       at 0 2 (Toff201 ∷ Sw12 ∷ []) (wl0047 (lit c4)) ▸
       at 1 2 (CCZ234 ∷ Sw12 ∷ []) (sym (wl0084 (lit c4))) ▸
       at 2 2 (Toff201 ∷ Sw12 ∷ []) (wl0047 (lit c4)) ▸
       at 3 2 (CCZ234 ∷ Sw12 ∷ []) (sym (wl0084 (lit c4))) ▸
       at 4 2 [] (wl0001 (lit c4)) ▸ done


-- auto SBOXd(0;1;2;3) | SBOX(0;1;43;2) @2332: 7 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩-at2332 : Ws → ⟪ (Sb⁻0-1-3-2 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ Sb⁻0-1-3-2 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩-at2332 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-3-2 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ Sb⁻0-1-3-2 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb⁻0-1-2-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·3·2⟩ (lit c4)) ▸
       at 2 2 (Sb0-1-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-43-2 ∷ Sb⁻0-1-2-3 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩ c4) ▸
       at 0 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 1 2 (Sb⁻0-1-3-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·2·3⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOXd(0;1;2;3) | SBOX(0;1;43;2) @01102332: 7 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩-at01102332 : Ws → ⟪ (Sb⁻1-0-3-2 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-42-3 ∷ Sb⁻1-0-3-2 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩-at01102332 c4 = run b0
  where
  b0 : Chain (Sb⁻1-0-3-2 ∷ Sb1-0-42-3 ∷ []) (Sb1-0-42-3 ∷ Sb⁻1-0-3-2 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Sb⁻0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·3·2⟩ (lit c4)) ▸
       at 2 2 (Sb0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sb⁻0-1-3-2 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩-at2332 c4) ▸
       at 0 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 1 2 (Sb⁻1-0-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨0·1·3·2⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto SBOXd(0;1;2;3) | SBOX(0;1;43;2) @02102331: 7 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩-at02102331 : Ws → ⟪ (Sb⁻2-0-3-1 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ Sb⁻2-0-3-1 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩-at02102331 c4 = run b0
  where
  b0 : Chain (Sb⁻2-0-3-1 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ Sb⁻2-0-3-1 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Sb⁻1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·3·1⟩ (lit c4)) ▸
       at 2 2 (Sb1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·41·3⟩ (lit c4)) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sb⁻1-0-3-2 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩-at01102332 c4) ▸
       at 0 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 1 2 (Sb⁻2-0-3-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·0·3·2⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto Kd0 | SBOX(1;2;34;0) @3443: 7 steps
lem-auto-Kd0-∣-SBOX⟨1·2·34·0⟩-at3443 : Ws → ⟪ (K0⁻ ∷ Sb1-2-43-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-43-0 ∷ K0⁻ ∷ []) ⟫ʷ
lem-auto-Kd0-∣-SBOX⟨1·2·34·0⟩-at3443 c4 = run b0
  where
  b0 : Chain (K0⁻ ∷ Sb1-2-43-0 ∷ []) (Sb1-2-43-0 ∷ K0⁻ ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (K0⁻ ∷ Sw34 ∷ []) (sym (c₁ (K • iI) (Swap ↑ ↑))) ▸
       at 2 2 (Sb1-2-34-0 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨1·2·43·0⟩ (lit c4)) ▸
       at 1 2 (Sb1-2-34-0 ∷ K0⁻ ∷ []) (lem-auto-Kd0-∣-SBOX⟨1·2·34·0⟩ c4) ▸
       at 0 2 (Sb1-2-43-0 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨1·2·34·0⟩ (lit c4)) ▸
       at 1 2 (K0⁻ ∷ Sw34 ∷ []) (sym (c₁ (K • iI) (Swap ↑ ↑))) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto Kd0 | SBOX(1;2;34;0) @01103443: 7 steps
lem-auto-Kd0-∣-SBOX⟨1·2·34·0⟩-at01103443 : Ws → ⟪ (K1⁻ ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ K1⁻ ∷ []) ⟫ʷ
lem-auto-Kd0-∣-SBOX⟨1·2·34·0⟩-at01103443 c4 = run b0
  where
  b0 : Chain (K1⁻ ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ K1⁻ ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (K0⁻ ∷ Sw01 ∷ []) (sym (wl0257 (lit c4))) ▸
       at 2 2 (Sb1-2-43-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·2·43·1⟩ (lit c4)) ▸
       at 1 2 (Sb1-2-43-0 ∷ K0⁻ ∷ []) (lem-auto-Kd0-∣-SBOX⟨1·2·34·0⟩-at3443 c4) ▸
       at 0 2 (Sb0-2-43-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·2·43·0⟩ (lit c4)) ▸
       at 1 2 (K1⁻ ∷ Sw01 ∷ []) (sym (wl0306 (lit c4))) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto Kd0 | SBOX(1;2;34;0) @0210213443: 7 steps
lem-auto-Kd0-∣-SBOX⟨1·2·34·0⟩-at0210213443 : Ws → ⟪ (K2⁻ ∷ Sb0-1-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-43-2 ∷ K2⁻ ∷ []) ⟫ʷ
lem-auto-Kd0-∣-SBOX⟨1·2·34·0⟩-at0210213443 c4 = run b0
  where
  b0 : Chain (K2⁻ ∷ Sb0-1-43-2 ∷ []) (Sb0-1-43-2 ∷ K2⁻ ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (K1⁻ ∷ Sw12 ∷ []) (sym (wl0307 (lit c4))) ▸
       at 2 2 (Sb0-2-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 1 2 (Sb0-2-43-1 ∷ K1⁻ ∷ []) (lem-auto-Kd0-∣-SBOX⟨1·2·34·0⟩-at01103443 c4) ▸
       at 0 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·43·1⟩ (lit c4)) ▸
       at 1 2 (K2⁻ ∷ Sw12 ∷ []) (sym (wl0308 (lit c4))) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto Kd0 | SBOX(1;2;34;0) @0310213442: 7 steps
lem-auto-Kd0-∣-SBOX⟨1·2·34·0⟩-at0310213442 : Ws → ⟪ (K3⁻ ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ K3⁻ ∷ []) ⟫ʷ
lem-auto-Kd0-∣-SBOX⟨1·2·34·0⟩-at0310213442 c4 = run b0
  where
  b0 : Chain (K3⁻ ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ K3⁻ ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (K2⁻ ∷ Sw23 ∷ []) (sym (wl0309 (lit c4))) ▸
       at 2 2 (Sb0-1-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-43-2 ∷ K2⁻ ∷ []) (lem-auto-Kd0-∣-SBOX⟨1·2·34·0⟩-at0210213443 c4) ▸
       at 0 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 1 2 (K3⁻ ∷ Sw23 ∷ []) (sym (wl0310 (lit c4))) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto Kd0 | SBOX(1;2;34;0) @03203442: 7 steps
lem-auto-Kd0-∣-SBOX⟨1·2·34·0⟩-at03203442 : Ws → ⟪ (K3⁻ ∷ Sb1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-42-3 ∷ K3⁻ ∷ []) ⟫ʷ
lem-auto-Kd0-∣-SBOX⟨1·2·34·0⟩-at03203442 c4 = run b0
  where
  b0 : Chain (K3⁻ ∷ Sb1-0-42-3 ∷ []) (Sb1-0-42-3 ∷ K3⁻ ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (K3⁻ ∷ Sw01 ∷ []) (c₂ (Swap) ((K • iI) ↑)) ▸
       at 2 2 (Sb0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-42-3 ∷ K3⁻ ∷ []) (lem-auto-Kd0-∣-SBOX⟨1·2·34·0⟩-at0310213442 c4) ▸
       at 0 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 1 2 (K3⁻ ∷ Sw01 ∷ []) (c₂ (Swap) ((K • iI) ↑)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto Kd0 | SBOX(1;2;34;0) @0312203441: 7 steps
lem-auto-Kd0-∣-SBOX⟨1·2·34·0⟩-at0312203441 : Ws → ⟪ (K3⁻ ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ K3⁻ ∷ []) ⟫ʷ
lem-auto-Kd0-∣-SBOX⟨1·2·34·0⟩-at0312203441 c4 = run b0
  where
  b0 : Chain (K3⁻ ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ K3⁻ ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (K3⁻ ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K • iI)) ▸
       at 2 2 (Sb1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·41·3⟩ (lit c4)) ▸
       at 1 2 (Sb1-0-42-3 ∷ K3⁻ ∷ []) (lem-auto-Kd0-∣-SBOX⟨1·2·34·0⟩-at03203442 c4) ▸
       at 0 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 1 2 (K3⁻ ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K • iI)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto CS01 | SBOX(2;3;04;1) @0110: 7 steps
lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at0110 : Ws → ⟪ (CS01 ∷ Sb2-3-14-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-3-14-0 ∷ CS01 ∷ []) ⟫ʷ
lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at0110 c4 = run b0
  where
  b0 : Chain (CS01 ∷ Sb2-3-14-0 ∷ []) (Sb2-3-14-0 ∷ CS01 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (CS01 ∷ Sw01 ∷ []) (sym (wl0132 (lit c4))) ▸
       at 2 2 (Sb2-3-04-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·3·14·0⟩ (lit c4)) ▸
       at 1 2 (Sb2-3-04-1 ∷ CS01 ∷ []) (lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩ c4) ▸
       at 0 2 (Sb2-3-14-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·3·04·1⟩ (lit c4)) ▸
       at 1 2 (CS01 ∷ Sw01 ∷ []) (sym (wl0132 (lit c4))) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto CS01 | SBOX(2;3;04;1) @021021: 7 steps
lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at021021 : Ws → ⟪ (CS02 ∷ Sb1-3-24-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-3-24-0 ∷ CS02 ∷ []) ⟫ʷ
lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at021021 c4 = run b0
  where
  b0 : Chain (CS02 ∷ Sb1-3-24-0 ∷ []) (Sb1-3-24-0 ∷ CS02 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CS01 ∷ Sw12 ∷ []) (lem-nat-1-CS02 (lit c4)) ▸
       at 2 2 (Sb2-3-14-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·3·24·0⟩ (lit c4)) ▸
       at 1 2 (Sb2-3-14-0 ∷ CS01 ∷ []) (lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at0110 c4) ▸
       at 0 2 (Sb1-3-24-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·3·14·0⟩ (lit c4)) ▸
       at 1 2 (CS02 ∷ Sw12 ∷ []) (lem-nat-1-CS01 (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto CS01 | SBOX(2;3;04;1) @03102132: 7 steps
lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at03102132 : Ws → ⟪ (CS03 ∷ Sb1-2-34-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-34-0 ∷ CS03 ∷ []) ⟫ʷ
lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at03102132 c4 = run b0
  where
  b0 : Chain (CS03 ∷ Sb1-2-34-0 ∷ []) (Sb1-2-34-0 ∷ CS03 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (CS02 ∷ Sw23 ∷ []) (lem-nat-2-CS03 (lit c4)) ▸
       at 2 2 (Sb1-3-24-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·2·34·0⟩ (lit c4)) ▸
       at 1 2 (Sb1-3-24-0 ∷ CS02 ∷ []) (lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at021021 c4) ▸
       at 0 2 (Sb1-2-34-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·3·24·0⟩ (lit c4)) ▸
       at 1 2 (CS03 ∷ Sw23 ∷ []) (lem-nat-2-CS02 (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto CS01 | SBOX(2;3;04;1) @0410213243: 7 steps
lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at0410213243 : Ws → ⟪ (CS04 ∷ Sb1-2-43-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-43-0 ∷ CS04 ∷ []) ⟫ʷ
lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at0410213243 c4 = run b0
  where
  b0 : Chain (CS04 ∷ Sb1-2-43-0 ∷ []) (Sb1-2-43-0 ∷ CS04 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (CS03 ∷ Sw34 ∷ []) (lem-nat-3-CS04 (lit c4)) ▸
       at 2 2 (Sb1-2-34-0 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨1·2·43·0⟩ (lit c4)) ▸
       at 1 2 (Sb1-2-34-0 ∷ CS03 ∷ []) (lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at03102132 c4) ▸
       at 0 2 (Sb1-2-43-0 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨1·2·34·0⟩ (lit c4)) ▸
       at 1 2 (CS04 ∷ Sw34 ∷ []) (lem-nat-3-CS03 (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto CS01 | SBOX(2;3;04;1) @04203243: 7 steps
lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at04203243 : Ws → ⟪ (CS14 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ CS14 ∷ []) ⟫ʷ
lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at04203243 c4 = run b0
  where
  b0 : Chain (CS14 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ CS14 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (CS04 ∷ Sw01 ∷ []) (lem-nat-0-CS14 (lit c4)) ▸
       at 2 2 (Sb1-2-43-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·2·43·1⟩ (lit c4)) ▸
       at 1 2 (Sb1-2-43-0 ∷ CS04 ∷ []) (lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at0410213243 c4) ▸
       at 0 2 (Sb0-2-43-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·2·43·0⟩ (lit c4)) ▸
       at 1 2 (CS14 ∷ Sw01 ∷ []) (lem-nat-0-CS04 (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto CS01 | SBOX(2;3;04;1) @0412203143: 7 steps
lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at0412203143 : Ws → ⟪ (CS24 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-43-2 ∷ CS24 ∷ []) ⟫ʷ
lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at0412203143 c4 = run b0
  where
  b0 : Chain (CS24 ∷ Sb0-1-43-2 ∷ []) (Sb0-1-43-2 ∷ CS24 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0017 (lit c4))) ▸
       at 2 2 (Sb0-2-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 1 2 (Sb0-2-43-1 ∷ CS14 ∷ []) (lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at04203243 c4) ▸
       at 0 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·43·1⟩ (lit c4)) ▸
       at 1 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0008 (lit c4))) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto CS01 | SBOX(2;3;04;1) @0413203142: 7 steps
lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at0413203142 : Ws → ⟪ (CS34 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ CS34 ∷ []) ⟫ʷ
lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at0413203142 c4 = run b0
  where
  b0 : Chain (CS34 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ CS34 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0015 (lit c4))) ▸
       at 2 2 (Sb0-1-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-43-2 ∷ CS24 ∷ []) (lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at0412203143 c4) ▸
       at 0 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 1 2 (CS34 ∷ Sw23 ∷ []) (sym (wl0011 (lit c4))) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto CS01 | SBOX(2;3;04;1) @0413213042: 7 steps
lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at0413213042 : Ws → ⟪ (CS34 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-42-3 ∷ CS34 ∷ []) ⟫ʷ
lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at0413213042 c4 = run b0
  where
  b0 : Chain (CS34 ∷ Sb1-0-42-3 ∷ []) (Sb1-0-42-3 ∷ CS34 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (CS34 ∷ Sw01 ∷ []) (c₂ (Swap) (CS ↑)) ▸
       at 2 2 (Sb0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-42-3 ∷ CS34 ∷ []) (lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at0413203142 c4) ▸
       at 0 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 1 2 (CS34 ∷ Sw01 ∷ []) (c₂ (Swap) (CS ↑)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto CS01 | SBOX(2;3;04;1) @04133041: 7 steps
lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at04133041 : Ws → ⟪ (CS34 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ CS34 ∷ []) ⟫ʷ
lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at04133041 c4 = run b0
  where
  b0 : Chain (CS34 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ CS34 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS)) ▸
       at 2 2 (Sb1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·41·3⟩ (lit c4)) ▸
       at 1 2 (Sb1-0-42-3 ∷ CS34 ∷ []) (lem-auto-CS01-∣-SBOX⟨2·3·04·1⟩-at0413213042 c4) ▸
       at 0 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 1 2 (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- sym34 @243243: 5 steps
lem-sym34-at243243 : Ws → ⟪ (Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1432 ∷ []) ⟫ʷ
lem-sym34-at243243 c4 = run b0
  where
  b0 : Chain (Bx0-1423 ∷ []) (Bx0-1432 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ (lit c4)) ▸
       at 1 1 (Bx0-1342 ∷ []) (lem-sym34-at2332 c4) ▸
       at 0 2 (Bx0-1432 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1342⟩ (lit c4)) ▸
       at 1 2 [] (wl0007 (lit c4)) ▸ done


-- sym34 @0110243243: 5 steps
lem-sym34-at0110243243 : Ws → ⟪ (Bx1-0423 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0432 ∷ []) ⟫ʷ
lem-sym34-at0110243243 c4 = run b0
  where
  b0 : Chain (Bx1-0423 ∷ []) (Bx1-0432 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4)) ▸
       at 1 1 (Bx0-1432 ∷ []) (lem-sym34-at243243 c4) ▸
       at 0 2 (Bx1-0432 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1432⟩ (lit c4)) ▸
       at 1 2 [] (wl0002 (lit c4)) ▸ done


-- sym34 @0210243143: 5 steps
lem-sym34-at0210243143 : Ws → ⟪ (Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0431 ∷ []) ⟫ʷ
lem-sym34-at0210243143 c4 = run b0
  where
  b0 : Chain (Bx2-0413 ∷ []) (Bx2-0431 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4)) ▸
       at 1 1 (Bx1-0432 ∷ []) (lem-sym34-at0110243243 c4) ▸
       at 0 2 (Bx2-0431 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0432⟩ (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- sym23 @2442: 5 steps
lem-sym23-at2442 : Ws → ⟪ (Bx0-1432 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1342 ∷ []) ⟫ʷ
lem-sym23-at2442 c4 = run b0
  where
  b0 : Chain (Bx0-1432 ∷ []) (Bx0-1342 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx0-1423 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1432⟩ (lit c4)) ▸
       at 1 1 (Bx0-1243 ∷ []) (lem-sym23-at243243 c4) ▸
       at 0 2 (Bx0-1342 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1243⟩ (lit c4)) ▸
       at 1 2 [] (wl0006 (lit c4)) ▸ done


-- sym23 @01102442: 5 steps
lem-sym23-at01102442 : Ws → ⟪ (Bx1-0432 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0342 ∷ []) ⟫ʷ
lem-sym23-at01102442 c4 = run b0
  where
  b0 : Chain (Bx1-0432 ∷ []) (Bx1-0342 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx0-1432 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0432⟩ (lit c4)) ▸
       at 1 1 (Bx0-1342 ∷ []) (lem-sym23-at2442 c4) ▸
       at 0 2 (Bx1-0342 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1342⟩ (lit c4)) ▸
       at 1 2 [] (wl0002 (lit c4)) ▸ done


-- sym23 @02102441: 5 steps
lem-sym23-at02102441 : Ws → ⟪ (Bx2-0431 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0341 ∷ []) ⟫ʷ
lem-sym23-at02102441 c4 = run b0
  where
  b0 : Chain (Bx2-0431 ∷ []) (Bx2-0341 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx1-0432 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0431⟩ (lit c4)) ▸
       at 1 1 (Bx1-0342 ∷ []) (lem-sym23-at01102442 c4) ▸
       at 0 2 (Bx2-0341 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0342⟩ (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- beta-T @233442: 8 steps
lem-beta-T-at233442 : Ws → ⟪ (Bx0-1342 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) ⟫ʷ
lem-beta-T-at233442 c4 = run b0
  where
  b0 : Chain (Bx0-1342 ∷ []) (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx0-1243 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1342⟩ (lit c4)) ▸
       at 1 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-beta-T-at3443 c4) ▸
       at 0 2 (Toff013 ∷ Sw23 ∷ []) (lem-nat-2-TOFF012 (lit c4)) ▸
       at 1 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 (lit c4)) ▸
       at 2 2 (Toff013 ∷ Sw23 ∷ []) (lem-nat-2-TOFF012 (lit c4)) ▸
       at 3 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 (lit c4)) ▸
       at 4 2 [] (wl0006 (lit c4)) ▸ done


-- beta-T @0110233442: 8 steps
lem-beta-T-at0110233442 : Ws → ⟪ (Bx1-0342 ∷ []) ⟫ʷ ≈ ⟪ (Toff103 ∷ CCZ124 ∷ Toff103 ∷ CCZ124 ∷ []) ⟫ʷ
lem-beta-T-at0110233442 c4 = run b0
  where
  b0 : Chain (Bx1-0342 ∷ []) (Toff103 ∷ CCZ124 ∷ Toff103 ∷ CCZ124 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx0-1342 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0342⟩ (lit c4)) ▸
       at 1 1 (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) (lem-beta-T-at233442 c4) ▸
       at 0 2 (Toff103 ∷ Sw01 ∷ []) (wl0101 (lit c4)) ▸
       at 1 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 (lit c4)) ▸
       at 2 2 (Toff103 ∷ Sw01 ∷ []) (wl0101 (lit c4)) ▸
       at 3 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 (lit c4)) ▸
       at 4 2 [] (wl0002 (lit c4)) ▸ done


-- beta-T @0210233441: 8 steps
lem-beta-T-at0210233441 : Ws → ⟪ (Bx2-0341 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ []) ⟫ʷ
lem-beta-T-at0210233441 c4 = run b0
  where
  b0 : Chain (Bx2-0341 ∷ []) (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx1-0342 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0341⟩ (lit c4)) ▸
       at 1 1 (Toff103 ∷ CCZ124 ∷ Toff103 ∷ CCZ124 ∷ []) (lem-beta-T-at0110233442 c4) ▸
       at 0 2 (Toff203 ∷ Sw12 ∷ []) (lem-nat-1-TOFF103 (lit c4)) ▸
       at 1 2 (CCZ124 ∷ Sw12 ∷ []) (sym (wl0078 (lit c4))) ▸
       at 2 2 (Toff203 ∷ Sw12 ∷ []) (lem-nat-1-TOFF103 (lit c4)) ▸
       at 3 2 (CCZ124 ∷ Sw12 ∷ []) (sym (wl0078 (lit c4))) ▸
       at 4 2 [] (wl0001 (lit c4)) ▸ done


-- sym23 @233442: 5 steps
lem-sym23-at233442 : Ws → ⟪ (Bx0-1342 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1432 ∷ []) ⟫ʷ
lem-sym23-at233442 c4 = run b0
  where
  b0 : Chain (Bx0-1342 ∷ []) (Bx0-1432 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx0-1243 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1342⟩ (lit c4)) ▸
       at 1 1 (Bx0-1423 ∷ []) (lem-sym23-at3443 c4) ▸
       at 0 2 (Bx0-1432 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1423⟩ (lit c4)) ▸
       at 1 2 [] (wl0006 (lit c4)) ▸ done


-- sym23 @0110233442: 5 steps
lem-sym23-at0110233442 : Ws → ⟪ (Bx1-0342 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0432 ∷ []) ⟫ʷ
lem-sym23-at0110233442 c4 = run b0
  where
  b0 : Chain (Bx1-0342 ∷ []) (Bx1-0432 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx0-1342 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0342⟩ (lit c4)) ▸
       at 1 1 (Bx0-1432 ∷ []) (lem-sym23-at233442 c4) ▸
       at 0 2 (Bx1-0432 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1432⟩ (lit c4)) ▸
       at 1 2 [] (wl0002 (lit c4)) ▸ done


-- sym23 @0210233441: 5 steps
lem-sym23-at0210233441 : Ws → ⟪ (Bx2-0341 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0431 ∷ []) ⟫ʷ
lem-sym23-at0210233441 c4 = run b0
  where
  b0 : Chain (Bx2-0341 ∷ []) (Bx2-0431 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx1-0342 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0341⟩ (lit c4)) ▸
       at 1 1 (Bx1-0432 ∷ []) (lem-sym23-at0110233442 c4) ▸
       at 0 2 (Bx2-0431 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0432⟩ (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- sym34 @2442: 5 steps
lem-sym34-at2442 : Ws → ⟪ (Bx0-1432 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ []) ⟫ʷ
lem-sym34-at2442 c4 = run b0
  where
  b0 : Chain (Bx0-1432 ∷ []) (Bx0-1423 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx0-1423 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1432⟩ (lit c4)) ▸
       at 1 1 (Bx0-1432 ∷ []) (lem-sym34-at243243 c4) ▸
       at 0 2 (Bx0-1423 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1432⟩ (lit c4)) ▸
       at 1 2 [] (wl0006 (lit c4)) ▸ done


-- sym34 @01102442: 5 steps
lem-sym34-at01102442 : Ws → ⟪ (Bx1-0432 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0423 ∷ []) ⟫ʷ
lem-sym34-at01102442 c4 = run b0
  where
  b0 : Chain (Bx1-0432 ∷ []) (Bx1-0423 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx0-1432 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0432⟩ (lit c4)) ▸
       at 1 1 (Bx0-1423 ∷ []) (lem-sym34-at2442 c4) ▸
       at 0 2 (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ (lit c4)) ▸
       at 1 2 [] (wl0002 (lit c4)) ▸ done


-- sym34 @02102441: 5 steps
lem-sym34-at02102441 : Ws → ⟪ (Bx2-0431 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ []) ⟫ʷ
lem-sym34-at02102441 c4 = run b0
  where
  b0 : Chain (Bx2-0431 ∷ []) (Bx2-0413 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx1-0432 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0431⟩ (lit c4)) ▸
       at 1 1 (Bx1-0423 ∷ []) (lem-sym34-at01102442 c4) ▸
       at 0 2 (Bx2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0423⟩ (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- auto K0 | SBOX(1;2;34;0) @3443: 7 steps
lem-auto-K0-∣-SBOX⟨1·2·34·0⟩-at3443 : Ws → ⟪ (K0 ∷ Sb1-2-43-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-43-0 ∷ K0 ∷ []) ⟫ʷ
lem-auto-K0-∣-SBOX⟨1·2·34·0⟩-at3443 c4 = run b0
  where
  b0 : Chain (K0 ∷ Sb1-2-43-0 ∷ []) (Sb1-2-43-0 ∷ K0 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 2 2 (Sb1-2-34-0 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨1·2·43·0⟩ (lit c4)) ▸
       at 1 2 (Sb1-2-34-0 ∷ K0 ∷ []) (lem-auto-K0-∣-SBOX⟨1·2·34·0⟩ c4) ▸
       at 0 2 (Sb1-2-43-0 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨1·2·34·0⟩ (lit c4)) ▸
       at 1 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto K0 | SBOX(1;2;34;0) @01103443: 7 steps
lem-auto-K0-∣-SBOX⟨1·2·34·0⟩-at01103443 : Ws → ⟪ (K1 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ K1 ∷ []) ⟫ʷ
lem-auto-K0-∣-SBOX⟨1·2·34·0⟩-at01103443 c4 = run b0
  where
  b0 : Chain (K1 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ K1 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (K0 ∷ Sw01 ∷ []) (sym (wl0031 (lit c4))) ▸
       at 2 2 (Sb1-2-43-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·2·43·1⟩ (lit c4)) ▸
       at 1 2 (Sb1-2-43-0 ∷ K0 ∷ []) (lem-auto-K0-∣-SBOX⟨1·2·34·0⟩-at3443 c4) ▸
       at 0 2 (Sb0-2-43-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·2·43·0⟩ (lit c4)) ▸
       at 1 2 (K1 ∷ Sw01 ∷ []) (sym (wl0076 (lit c4))) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto K0 | SBOX(1;2;34;0) @0210213443: 7 steps
lem-auto-K0-∣-SBOX⟨1·2·34·0⟩-at0210213443 : Ws → ⟪ (K2 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-43-2 ∷ K2 ∷ []) ⟫ʷ
lem-auto-K0-∣-SBOX⟨1·2·34·0⟩-at0210213443 c4 = run b0
  where
  b0 : Chain (K2 ∷ Sb0-1-43-2 ∷ []) (Sb0-1-43-2 ∷ K2 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (K1 ∷ Sw12 ∷ []) (sym (wl0062 (lit c4))) ▸
       at 2 2 (Sb0-2-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 1 2 (Sb0-2-43-1 ∷ K1 ∷ []) (lem-auto-K0-∣-SBOX⟨1·2·34·0⟩-at01103443 c4) ▸
       at 0 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·43·1⟩ (lit c4)) ▸
       at 1 2 (K2 ∷ Sw12 ∷ []) (sym (wl0056 (lit c4))) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto K0 | SBOX(1;2;34;0) @0310213442: 7 steps
lem-auto-K0-∣-SBOX⟨1·2·34·0⟩-at0310213442 : Ws → ⟪ (K3 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ K3 ∷ []) ⟫ʷ
lem-auto-K0-∣-SBOX⟨1·2·34·0⟩-at0310213442 c4 = run b0
  where
  b0 : Chain (K3 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ K3 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (K2 ∷ Sw23 ∷ []) (sym (wl0058 (lit c4))) ▸
       at 2 2 (Sb0-1-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-43-2 ∷ K2 ∷ []) (lem-auto-K0-∣-SBOX⟨1·2·34·0⟩-at0210213443 c4) ▸
       at 0 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 1 2 (K3 ∷ Sw23 ∷ []) (sym (wl0057 (lit c4))) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto K0 | SBOX(1;2;34;0) @03203442: 7 steps
lem-auto-K0-∣-SBOX⟨1·2·34·0⟩-at03203442 : Ws → ⟪ (K3 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-42-3 ∷ K3 ∷ []) ⟫ʷ
lem-auto-K0-∣-SBOX⟨1·2·34·0⟩-at03203442 c4 = run b0
  where
  b0 : Chain (K3 ∷ Sb1-0-42-3 ∷ []) (Sb1-0-42-3 ∷ K3 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (K3 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑)) ▸
       at 2 2 (Sb0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-42-3 ∷ K3 ∷ []) (lem-auto-K0-∣-SBOX⟨1·2·34·0⟩-at0310213442 c4) ▸
       at 0 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 1 2 (K3 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto K0 | SBOX(1;2;34;0) @0312203441: 7 steps
lem-auto-K0-∣-SBOX⟨1·2·34·0⟩-at0312203441 : Ws → ⟪ (K3 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ K3 ∷ []) ⟫ʷ
lem-auto-K0-∣-SBOX⟨1·2·34·0⟩-at0312203441 c4 = run b0
  where
  b0 : Chain (K3 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ K3 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (K3 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K)) ▸
       at 2 2 (Sb1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·41·3⟩ (lit c4)) ▸
       at 1 2 (Sb1-0-42-3 ∷ K3 ∷ []) (lem-auto-K0-∣-SBOX⟨1·2·34·0⟩-at03203442 c4) ▸
       at 0 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 1 2 (K3 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto SBOX(0;1;2;3) | SBOX(0;1;43;2) @2332: 7 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩-at2332 : Ws → ⟪ (Sb0-1-3-2 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ Sb0-1-3-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-3-2 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ Sb0-1-3-2 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb0-1-2-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·3·2⟩ (lit c4)) ▸
       at 2 2 (Sb0-1-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-43-2 ∷ Sb0-1-2-3 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩ c4) ▸
       at 0 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·43·2⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-3-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·2·3⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOX(0;1;2;3) | SBOX(0;1;43;2) @01102332: 7 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩-at01102332 : Ws → ⟪ (Sb1-0-3-2 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-42-3 ∷ Sb1-0-3-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩-at01102332 c4 = run b0
  where
  b0 : Chain (Sb1-0-3-2 ∷ Sb1-0-42-3 ∷ []) (Sb1-0-42-3 ∷ Sb1-0-3-2 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Sb0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·3·2⟩ (lit c4)) ▸
       at 2 2 (Sb0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sb0-1-3-2 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩-at2332 c4) ▸
       at 0 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 1 2 (Sb1-0-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·3·2⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto SBOX(0;1;2;3) | SBOX(0;1;43;2) @02102331: 7 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩-at02102331 : Ws → ⟪ (Sb2-0-3-1 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ Sb2-0-3-1 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩-at02102331 c4 = run b0
  where
  b0 : Chain (Sb2-0-3-1 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ Sb2-0-3-1 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Sb1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·3·1⟩ (lit c4)) ▸
       at 2 2 (Sb1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·41·3⟩ (lit c4)) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sb1-0-3-2 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩-at01102332 c4) ▸
       at 0 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 1 2 (Sb2-0-3-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·3·2⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- sym12 @01103443: 5 steps
lem-sym12-at01103443 : Ws → ⟪ (Bx1-0243 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2043 ∷ []) ⟫ʷ
lem-sym12-at01103443 c4 = run b0
  where
  b0 : Chain (Bx1-0243 ∷ []) (Bx1-2043 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx0-1243 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0243⟩ (lit c4)) ▸
       at 1 1 (Bx0-2143 ∷ []) (lem-sym12-at3443 c4) ▸
       at 0 2 (Bx1-2043 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·2143⟩ (lit c4)) ▸
       at 1 2 [] (wl0002 (lit c4)) ▸ done


-- sym12 @0210213443: 5 steps
lem-sym12-at0210213443 : Ws → ⟪ (Bx2-0143 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1043 ∷ []) ⟫ʷ
lem-sym12-at0210213443 c4 = run b0
  where
  b0 : Chain (Bx2-0143 ∷ []) (Bx2-1043 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx1-0243 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0143⟩ (lit c4)) ▸
       at 1 1 (Bx1-2043 ∷ []) (lem-sym12-at01103443 c4) ▸
       at 0 2 (Bx2-1043 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·2043⟩ (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- X1-beta @3443: 8 steps
lem-X1-beta-at3443 : Ws → ⟪ (X1 ∷ Bx0-1243 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Bx0-1243 ∷ []) ⟫ʷ
lem-X1-beta-at3443 c4 = run b0
  where
  b0 : Chain (X1 ∷ Bx0-1243 ∷ X1 ∷ []) (CCZ234 ∷ Bx0-1243 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (X1 ∷ Sw34 ∷ []) (sym (c₂ (X ↑) (Swap ↑))) ▸
       at 2 2 (Bx0-1234 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1243⟩ (lit c4)) ▸
       at 3 2 (X1 ∷ Sw34 ∷ []) (sym (c₂ (X ↑) (Swap ↑))) ▸
       at 1 3 (CCZ234 ∷ Bx0-1234 ∷ []) (lem-X1-beta c4) ▸
       at 0 2 (CCZ234 ∷ Sw34 ∷ []) (sym (wl0155 (lit c4))) ▸
       at 1 2 (Bx0-1243 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1234⟩ (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- X1-beta @01103443: 8 steps
lem-X1-beta-at01103443 : Ws → ⟪ (X0 ∷ Bx1-0243 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Bx1-0243 ∷ []) ⟫ʷ
lem-X1-beta-at01103443 c4 = run b0
  where
  b0 : Chain (X0 ∷ Bx1-0243 ∷ X0 ∷ []) (CCZ234 ∷ Bx1-0243 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (X1 ∷ Sw01 ∷ []) (wl0370 (lit c4)) ▸
       at 2 2 (Bx0-1243 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0243⟩ (lit c4)) ▸
       at 3 2 (X1 ∷ Sw01 ∷ []) (wl0370 (lit c4)) ▸
       at 1 3 (CCZ234 ∷ Bx0-1243 ∷ []) (lem-X1-beta-at3443 c4) ▸
       at 0 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 1 2 (Bx1-0243 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1243⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- X1-beta @0210213443: 8 steps
lem-X1-beta-at0210213443 : Ws → ⟪ (X0 ∷ Bx2-0143 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Bx2-0143 ∷ []) ⟫ʷ
lem-X1-beta-at0210213443 c4 = run b0
  where
  b0 : Chain (X0 ∷ Bx2-0143 ∷ X0 ∷ []) (CCZ134 ∷ Bx2-0143 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (X0 ∷ Sw12 ∷ []) (sym (c₁ (X) (Swap))) ▸
       at 2 2 (Bx1-0243 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0143⟩ (lit c4)) ▸
       at 3 2 (X0 ∷ Sw12 ∷ []) (sym (c₁ (X) (Swap))) ▸
       at 1 3 (CCZ234 ∷ Bx1-0243 ∷ []) (lem-X1-beta-at01103443 c4) ▸
       at 0 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0034 (lit c4))) ▸
       at 1 2 (Bx2-0143 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0243⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- X1-beta @02203443: 8 steps
lem-X1-beta-at02203443 : Ws → ⟪ (X1 ∷ Bx2-1043 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Bx2-1043 ∷ []) ⟫ʷ
lem-X1-beta-at02203443 c4 = run b0
  where
  b0 : Chain (X1 ∷ Bx2-1043 ∷ X1 ∷ []) (CCZ034 ∷ Bx2-1043 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (X0 ∷ Sw01 ∷ []) (wl0371 (lit c4)) ▸
       at 2 2 (Bx2-0143 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·1043⟩ (lit c4)) ▸
       at 3 2 (X0 ∷ Sw01 ∷ []) (wl0371 (lit c4)) ▸
       at 1 3 (CCZ134 ∷ Bx2-0143 ∷ []) (lem-X1-beta-at0210213443 c4) ▸
       at 0 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 (lit c4)) ▸
       at 1 2 (Bx2-1043 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·0143⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- sym12 @02203443: 5 steps
lem-sym12-at02203443 : Ws → ⟪ (Bx2-1043 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0143 ∷ []) ⟫ʷ
lem-sym12-at02203443 c4 = run b0
  where
  b0 : Chain (Bx2-1043 ∷ []) (Bx2-0143 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx2-0143 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·1043⟩ (lit c4)) ▸
       at 1 1 (Bx2-1043 ∷ []) (lem-sym12-at0210213443 c4) ▸
       at 0 2 (Bx2-0143 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·1043⟩ (lit c4)) ▸
       at 1 2 [] (wl0002 (lit c4)) ▸ done


-- auto BOX(0;1234) | SBOX(0;1;23;4) @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·1·23·4⟩-at2332 : Ws → ⟪ (Bx0-1324 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-32-4 ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·1·23·4⟩-at2332 c4 = run b0
  where
  b0 : Chain (Bx0-1324 ∷ Sb0-1-32-4 ∷ []) (Sb0-1-32-4 ∷ Bx0-1324 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ (lit c4)) ▸
       at 2 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-23-4 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·1·23·4⟩ c4) ▸
       at 0 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ (lit c4)) ▸
       at 1 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto BOX(0;1234) | SBOX(0;1;23;4) @243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·1·23·4⟩-at243243 : Ws → ⟪ (Bx0-1423 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ Bx0-1423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·1·23·4⟩-at243243 c4 = run b0
  where
  b0 : Chain (Bx0-1423 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ Bx0-1423 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ (lit c4)) ▸
       at 2 2 (Sb0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-32-4 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·1·23·4⟩-at2332 c4) ▸
       at 0 2 (Sb0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·32·4⟩ (lit c4)) ▸
       at 1 2 (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto BOX(0;1234) | SBOX(0;1;23;4) @0110243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·1·23·4⟩-at0110243243 : Ws → ⟪ (Bx1-0423 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-42-3 ∷ Bx1-0423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·1·23·4⟩-at0110243243 c4 = run b0
  where
  b0 : Chain (Bx1-0423 ∷ Sb1-0-42-3 ∷ []) (Sb1-0-42-3 ∷ Bx1-0423 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4)) ▸
       at 2 2 (Sb0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-42-3 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·1·23·4⟩-at243243 c4) ▸
       at 0 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 1 2 (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto BOX(0;1234) | SBOX(0;1;23;4) @0210243143: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·1·23·4⟩-at0210243143 : Ws → ⟪ (Bx2-0413 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ Bx2-0413 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·1·23·4⟩-at0210243143 c4 = run b0
  where
  b0 : Chain (Bx2-0413 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ Bx2-0413 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4)) ▸
       at 2 2 (Sb1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·41·3⟩ (lit c4)) ▸
       at 1 2 (Sb1-0-42-3 ∷ Bx1-0423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·1·23·4⟩-at0110243243 c4) ▸
       at 0 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 1 2 (Bx2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0423⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | CCZ124 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ124-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ124-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ CCZ134 ∷ []) (CCZ134 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 (lit c4)) ▸
       at 1 2 (CCZ124 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ124 c4) ▸
       at 0 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 (lit c4)) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | CCZ124 @243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ124-at243243 : Ws → ⟪ (Sb0-1-42-3 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ124-at243243 c4 = run b0
  where
  b0 : Chain (Sb0-1-42-3 ∷ CCZ134 ∷ []) (CCZ134 ∷ Sb0-1-42-3 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 2 2 (CCZ134 ∷ Sw34 ∷ []) (sym (wl0154 (lit c4))) ▸
       at 1 2 (CCZ134 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ124-at2332 c4) ▸
       at 0 2 (CCZ134 ∷ Sw34 ∷ []) (sym (wl0154 (lit c4))) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | CCZ124 @0110243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ124-at0110243243 : Ws → ⟪ (Sb1-0-42-3 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ124-at0110243243 c4 = run b0
  where
  b0 : Chain (Sb1-0-42-3 ∷ CCZ034 ∷ []) (CCZ034 ∷ Sb1-0-42-3 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 2 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 (lit c4)) ▸
       at 1 2 (CCZ134 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ124-at243243 c4) ▸
       at 0 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 (lit c4)) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | CCZ124 @0210243143: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ124-at0210243143 : Ws → ⟪ (Sb2-0-41-3 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ124-at0210243143 c4 = run b0
  where
  b0 : Chain (Sb2-0-41-3 ∷ CCZ034 ∷ []) (CCZ034 ∷ Sb2-0-41-3 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·41·3⟩ (lit c4)) ▸
       at 2 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 (lit c4)) ▸
       at 1 2 (CCZ034 ∷ Sb1-0-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ124-at0110243243 c4) ▸
       at 0 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 (lit c4)) ▸
       at 1 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- F5d CS01 @1221: 8 steps
lem-F5d-CS01-at1221 : Ws → ⟪ (CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-42-3 ∷ X4 ∷ Sb⁻1-0-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-F5d-CS01-at1221 c4 = run b0
  where
  b0 : Chain (CS02⁻ ∷ []) (Sb⁻1-0-42-3 ∷ X4 ∷ Sb⁻1-0-42-3 ∷ X4 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CS01⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd02 (lit c4)) ▸
       at 1 1 (Sb⁻2-0-41-3 ∷ X4 ∷ Sb⁻2-0-41-3 ∷ X4 ∷ []) (lem-F5d-CS01 c4) ▸
       at 0 2 (Sb⁻1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·41·3⟩ (lit c4)) ▸
       at 1 2 (X4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (X ↑)) ▸
       at 2 2 (Sb⁻1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·41·3⟩ (lit c4)) ▸
       at 3 2 (X4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (X ↑)) ▸
       at 4 2 [] (wl0001 (lit c4)) ▸ done


-- F5d CS01 @132132: 8 steps
lem-F5d-CS01-at132132 : Ws → ⟪ (CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-43-2 ∷ X4 ∷ Sb⁻1-0-43-2 ∷ X4 ∷ []) ⟫ʷ
lem-F5d-CS01-at132132 c4 = run b0
  where
  b0 : Chain (CS03⁻ ∷ []) (Sb⁻1-0-43-2 ∷ X4 ∷ Sb⁻1-0-43-2 ∷ X4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (CS02⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd03 (lit c4)) ▸
       at 1 1 (Sb⁻1-0-42-3 ∷ X4 ∷ Sb⁻1-0-42-3 ∷ X4 ∷ []) (lem-F5d-CS01-at1221 c4) ▸
       at 0 2 (Sb⁻1-0-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·0·42·3⟩ (lit c4)) ▸
       at 1 2 (X4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (X)) ▸
       at 2 2 (Sb⁻1-0-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·0·42·3⟩ (lit c4)) ▸
       at 3 2 (X4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (X)) ▸
       at 4 2 [] (wl0006 (lit c4)) ▸ done


-- F5d CS01 @14213243: 8 steps
lem-F5d-CS01-at14213243 : Ws → ⟪ (CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-34-2 ∷ X3 ∷ Sb⁻1-0-34-2 ∷ X3 ∷ []) ⟫ʷ
lem-F5d-CS01-at14213243 c4 = run b0
  where
  b0 : Chain (CS04⁻ ∷ []) (Sb⁻1-0-34-2 ∷ X3 ∷ Sb⁻1-0-34-2 ∷ X3 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (CS03⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd04 (lit c4)) ▸
       at 1 1 (Sb⁻1-0-43-2 ∷ X4 ∷ Sb⁻1-0-43-2 ∷ X4 ∷ []) (lem-F5d-CS01-at132132 c4) ▸
       at 0 2 (Sb⁻1-0-34-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨1·0·43·2⟩ (lit c4)) ▸
       at 1 2 (X3 ∷ Sw34 ∷ []) (wl0282 (lit c4)) ▸
       at 2 2 (Sb⁻1-0-34-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨1·0·43·2⟩ (lit c4)) ▸
       at 3 2 (X3 ∷ Sw34 ∷ []) (wl0282 (lit c4)) ▸
       at 4 2 [] (wl0007 (lit c4)) ▸ done


-- F5d CS01 @142142: 8 steps
lem-F5d-CS01-at142142 : Ws → ⟪ (CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-24-3 ∷ X2 ∷ Sb⁻1-0-24-3 ∷ X2 ∷ []) ⟫ʷ
lem-F5d-CS01-at142142 c4 = run b0
  where
  b0 : Chain (CS04⁻ ∷ []) (Sb⁻1-0-24-3 ∷ X2 ∷ Sb⁻1-0-24-3 ∷ X2 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (CS04⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd04 (lit c4)) ▸
       at 1 1 (Sb⁻1-0-34-2 ∷ X3 ∷ Sb⁻1-0-34-2 ∷ X3 ∷ []) (lem-F5d-CS01-at14213243 c4) ▸
       at 0 2 (Sb⁻1-0-24-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·0·34·2⟩ (lit c4)) ▸
       at 1 2 (X2 ∷ Sw23 ∷ []) (wl0281 (lit c4)) ▸
       at 2 2 (Sb⁻1-0-24-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·0·34·2⟩ (lit c4)) ▸
       at 3 2 (X2 ∷ Sw23 ∷ []) (wl0281 (lit c4)) ▸
       at 4 2 [] (wl0006 (lit c4)) ▸ done


-- F5d CS01 @1441: 8 steps
lem-F5d-CS01-at1441 : Ws → ⟪ (CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-0-14-3 ∷ X1 ∷ Sb⁻2-0-14-3 ∷ X1 ∷ []) ⟫ʷ
lem-F5d-CS01-at1441 c4 = run b0
  where
  b0 : Chain (CS04⁻ ∷ []) (Sb⁻2-0-14-3 ∷ X1 ∷ Sb⁻2-0-14-3 ∷ X1 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CS04⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd04 (lit c4)) ▸
       at 1 1 (Sb⁻1-0-24-3 ∷ X2 ∷ Sb⁻1-0-24-3 ∷ X2 ∷ []) (lem-F5d-CS01-at142142 c4) ▸
       at 0 2 (Sb⁻2-0-14-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·0·24·3⟩ (lit c4)) ▸
       at 1 2 (X1 ∷ Sw12 ∷ []) (wl0280 (lit c4)) ▸
       at 2 2 (Sb⁻2-0-14-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·0·24·3⟩ (lit c4)) ▸
       at 3 2 (X1 ∷ Sw12 ∷ []) (wl0280 (lit c4)) ▸
       at 4 2 [] (wl0001 (lit c4)) ▸ done


-- SBsymd @1221: 5 steps
lem-SBsymd-at1221 : Ws → ⟪ (Sb⁻1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-24-3 ∷ []) ⟫ʷ
lem-SBsymd-at1221 c4 = run b0
  where
  b0 : Chain (Sb⁻1-0-42-3 ∷ []) (Sb⁻1-0-24-3 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Sb⁻2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·0·42·3⟩ (lit c4)) ▸
       at 1 1 (Sb⁻2-0-14-3 ∷ []) (lem-SBsymd c4) ▸
       at 0 2 (Sb⁻1-0-24-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·14·3⟩ (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- SBsymd @132132: 5 steps
lem-SBsymd-at132132 : Ws → ⟪ (Sb⁻1-0-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-34-2 ∷ []) ⟫ʷ
lem-SBsymd-at132132 c4 = run b0
  where
  b0 : Chain (Sb⁻1-0-43-2 ∷ []) (Sb⁻1-0-34-2 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb⁻1-0-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·0·43·2⟩ (lit c4)) ▸
       at 1 1 (Sb⁻1-0-24-3 ∷ []) (lem-SBsymd-at1221 c4) ▸
       at 0 2 (Sb⁻1-0-34-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·0·24·3⟩ (lit c4)) ▸
       at 1 2 [] (wl0006 (lit c4)) ▸ done


-- SBsymd @14213243: 5 steps
lem-SBsymd-at14213243 : Ws → ⟪ (Sb⁻1-0-34-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-43-2 ∷ []) ⟫ʷ
lem-SBsymd-at14213243 c4 = run b0
  where
  b0 : Chain (Sb⁻1-0-34-2 ∷ []) (Sb⁻1-0-43-2 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Sb⁻1-0-43-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨1·0·34·2⟩ (lit c4)) ▸
       at 1 1 (Sb⁻1-0-34-2 ∷ []) (lem-SBsymd-at132132 c4) ▸
       at 0 2 (Sb⁻1-0-43-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨1·0·34·2⟩ (lit c4)) ▸
       at 1 2 [] (wl0007 (lit c4)) ▸ done


-- SBsymd @142142: 5 steps
lem-SBsymd-at142142 : Ws → ⟪ (Sb⁻1-0-24-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-42-3 ∷ []) ⟫ʷ
lem-SBsymd-at142142 c4 = run b0
  where
  b0 : Chain (Sb⁻1-0-24-3 ∷ []) (Sb⁻1-0-42-3 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb⁻1-0-34-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·0·24·3⟩ (lit c4)) ▸
       at 1 1 (Sb⁻1-0-43-2 ∷ []) (lem-SBsymd-at14213243 c4) ▸
       at 0 2 (Sb⁻1-0-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·0·43·2⟩ (lit c4)) ▸
       at 1 2 [] (wl0006 (lit c4)) ▸ done


-- SBsymd @1441: 5 steps
lem-SBsymd-at1441 : Ws → ⟪ (Sb⁻2-0-14-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-0-41-3 ∷ []) ⟫ʷ
lem-SBsymd-at1441 c4 = run b0
  where
  b0 : Chain (Sb⁻2-0-14-3 ∷ []) (Sb⁻2-0-41-3 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Sb⁻1-0-24-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·14·3⟩ (lit c4)) ▸
       at 1 1 (Sb⁻1-0-42-3 ∷ []) (lem-SBsymd-at142142 c4) ▸
       at 0 2 (Sb⁻2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·0·42·3⟩ (lit c4)) ▸
       at 1 2 [] (wl0001 (lit c4)) ▸ done


-- auto SBOXd(0;1;23;4) | SBOX(0;1;4;3) @2332: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨0·1·4·3⟩-at2332 : Ws → ⟪ (Sb⁻0-1-32-4 ∷ Sb0-1-4-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-4-2 ∷ Sb⁻0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨0·1·4·3⟩-at2332 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-32-4 ∷ Sb0-1-4-2 ∷ []) (Sb0-1-4-2 ∷ Sb⁻0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb⁻0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 (Sb0-1-4-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·4·2⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-4-3 ∷ Sb⁻0-1-23-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨0·1·4·3⟩ c4) ▸
       at 0 2 (Sb0-1-4-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·4·3⟩ (lit c4)) ▸
       at 1 2 (Sb⁻0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·23·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOXd(0;1;23;4) | SBOX(0;1;4;3) @243243: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨0·1·4·3⟩-at243243 : Ws → ⟪ (Sb⁻0-1-42-3 ∷ Sb0-1-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-3-2 ∷ Sb⁻0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨0·1·4·3⟩-at243243 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-42-3 ∷ Sb0-1-3-2 ∷ []) (Sb0-1-3-2 ∷ Sb⁻0-1-42-3 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Sb⁻0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·42·3⟩ (lit c4)) ▸
       at 2 2 (Sb0-1-4-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·3·2⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-4-2 ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨0·1·4·3⟩-at2332 c4) ▸
       at 0 2 (Sb0-1-3-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·4·2⟩ (lit c4)) ▸
       at 1 2 (Sb⁻0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto SBOXd(0;1;23;4) | SBOX(0;1;4;3) @0110243243: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨0·1·4·3⟩-at0110243243 : Ws → ⟪ (Sb⁻1-0-42-3 ∷ Sb1-0-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-3-2 ∷ Sb⁻1-0-42-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨0·1·4·3⟩-at0110243243 c4 = run b0
  where
  b0 : Chain (Sb⁻1-0-42-3 ∷ Sb1-0-3-2 ∷ []) (Sb1-0-3-2 ∷ Sb⁻1-0-42-3 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Sb⁻0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·42·3⟩ (lit c4)) ▸
       at 2 2 (Sb0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·3·2⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-3-2 ∷ Sb⁻0-1-42-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨0·1·4·3⟩-at243243 c4) ▸
       at 0 2 (Sb1-0-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·3·2⟩ (lit c4)) ▸
       at 1 2 (Sb⁻1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨0·1·42·3⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto SBOXd(0;1;23;4) | SBOX(0;1;4;3) @0210243143: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨0·1·4·3⟩-at0210243143 : Ws → ⟪ (Sb⁻2-0-41-3 ∷ Sb2-0-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-3-1 ∷ Sb⁻2-0-41-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨0·1·4·3⟩-at0210243143 c4 = run b0
  where
  b0 : Chain (Sb⁻2-0-41-3 ∷ Sb2-0-3-1 ∷ []) (Sb2-0-3-1 ∷ Sb⁻2-0-41-3 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Sb⁻1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·41·3⟩ (lit c4)) ▸
       at 2 2 (Sb1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·3·1⟩ (lit c4)) ▸
       at 1 2 (Sb1-0-3-2 ∷ Sb⁻1-0-42-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨0·1·4·3⟩-at0110243243 c4) ▸
       at 0 2 (Sb2-0-3-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·3·2⟩ (lit c4)) ▸
       at 1 2 (Sb⁻2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·0·42·3⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto SBOXd(0;1;23;4) | K4 @2332: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-K4-at2332 : Ws → ⟪ (Sb⁻0-1-32-4 ∷ K4 ∷ []) ⟫ʷ ≈ ⟪ (K4 ∷ Sb⁻0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-K4-at2332 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-32-4 ∷ K4 ∷ []) (K4 ∷ Sb⁻0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb⁻0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 (K4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K)) ▸
       at 1 2 (K4 ∷ Sb⁻0-1-23-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-K4 c4) ▸
       at 0 2 (K4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K)) ▸
       at 1 2 (Sb⁻0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·23·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOXd(0;1;23;4) | K4 @243243: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-K4-at243243 : Ws → ⟪ (Sb⁻0-1-42-3 ∷ K3 ∷ []) ⟫ʷ ≈ ⟪ (K3 ∷ Sb⁻0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-K4-at243243 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-42-3 ∷ K3 ∷ []) (K3 ∷ Sb⁻0-1-42-3 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Sb⁻0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·42·3⟩ (lit c4)) ▸
       at 2 2 (K4 ∷ Sw34 ∷ []) (sym (wl0067 (lit c4))) ▸
       at 1 2 (K4 ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-K4-at2332 c4) ▸
       at 0 2 (K3 ∷ Sw34 ∷ []) (sym (wl0068 (lit c4))) ▸
       at 1 2 (Sb⁻0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto SBOXd(0;1;23;4) | K4 @0110243243: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-K4-at0110243243 : Ws → ⟪ (Sb⁻1-0-42-3 ∷ K3 ∷ []) ⟫ʷ ≈ ⟪ (K3 ∷ Sb⁻1-0-42-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-K4-at0110243243 c4 = run b0
  where
  b0 : Chain (Sb⁻1-0-42-3 ∷ K3 ∷ []) (K3 ∷ Sb⁻1-0-42-3 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Sb⁻0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·42·3⟩ (lit c4)) ▸
       at 2 2 (K3 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑)) ▸
       at 1 2 (K3 ∷ Sb⁻0-1-42-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-K4-at243243 c4) ▸
       at 0 2 (K3 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑)) ▸
       at 1 2 (Sb⁻1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨0·1·42·3⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto SBOXd(0;1;23;4) | K4 @0210243143: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-K4-at0210243143 : Ws → ⟪ (Sb⁻2-0-41-3 ∷ K3 ∷ []) ⟫ʷ ≈ ⟪ (K3 ∷ Sb⁻2-0-41-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-K4-at0210243143 c4 = run b0
  where
  b0 : Chain (Sb⁻2-0-41-3 ∷ K3 ∷ []) (K3 ∷ Sb⁻2-0-41-3 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Sb⁻1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·41·3⟩ (lit c4)) ▸
       at 2 2 (K3 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K)) ▸
       at 1 2 (K3 ∷ Sb⁻1-0-42-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-K4-at0110243243 c4) ▸
       at 0 2 (K3 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K)) ▸
       at 1 2 (Sb⁻2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·0·42·3⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto SBOXd(0;1;23;4) | CS24 @2332: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS24-at2332 : Ws → ⟪ (Sb⁻0-1-32-4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ Sb⁻0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS24-at2332 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-32-4 ∷ CS34 ∷ []) (CS34 ∷ Sb⁻0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb⁻0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0015 (lit c4))) ▸
       at 1 2 (CS24 ∷ Sb⁻0-1-23-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS24 c4) ▸
       at 0 2 (CS34 ∷ Sw23 ∷ []) (sym (wl0011 (lit c4))) ▸
       at 1 2 (Sb⁻0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·23·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOXd(0;1;23;4) | CS24 @243243: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS24-at243243 : Ws → ⟪ (Sb⁻0-1-42-3 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ Sb⁻0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS24-at243243 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-42-3 ∷ CS34 ∷ []) (CS34 ∷ Sb⁻0-1-42-3 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Sb⁻0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·42·3⟩ (lit c4)) ▸
       at 2 2 (CS34 ∷ Sw34 ∷ []) (sym (wl0039 (lit c4))) ▸
       at 1 2 (CS34 ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS24-at2332 c4) ▸
       at 0 2 (CS34 ∷ Sw34 ∷ []) (sym (wl0039 (lit c4))) ▸
       at 1 2 (Sb⁻0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto SBOXd(0;1;23;4) | CS24 @0110243243: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS24-at0110243243 : Ws → ⟪ (Sb⁻1-0-42-3 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ Sb⁻1-0-42-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS24-at0110243243 c4 = run b0
  where
  b0 : Chain (Sb⁻1-0-42-3 ∷ CS34 ∷ []) (CS34 ∷ Sb⁻1-0-42-3 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Sb⁻0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·42·3⟩ (lit c4)) ▸
       at 2 2 (CS34 ∷ Sw01 ∷ []) (c₂ (Swap) (CS ↑)) ▸
       at 1 2 (CS34 ∷ Sb⁻0-1-42-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS24-at243243 c4) ▸
       at 0 2 (CS34 ∷ Sw01 ∷ []) (c₂ (Swap) (CS ↑)) ▸
       at 1 2 (Sb⁻1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨0·1·42·3⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto SBOXd(0;1;23;4) | CS24 @0210243143: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS24-at0210243143 : Ws → ⟪ (Sb⁻2-0-41-3 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ Sb⁻2-0-41-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS24-at0210243143 c4 = run b0
  where
  b0 : Chain (Sb⁻2-0-41-3 ∷ CS34 ∷ []) (CS34 ∷ Sb⁻2-0-41-3 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Sb⁻1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·41·3⟩ (lit c4)) ▸
       at 2 2 (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS)) ▸
       at 1 2 (CS34 ∷ Sb⁻1-0-42-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS24-at0110243243 c4) ▸
       at 0 2 (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS)) ▸
       at 1 2 (Sb⁻2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·0·42·3⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto SBOXd(0;1;23;4) | Kd4 @2332: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-Kd4-at2332 : Ws → ⟪ (Sb⁻0-1-32-4 ∷ K4⁻ ∷ []) ⟫ʷ ≈ ⟪ (K4⁻ ∷ Sb⁻0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-Kd4-at2332 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-32-4 ∷ K4⁻ ∷ []) (K4⁻ ∷ Sb⁻0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb⁻0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 (K4⁻ ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K • iI)) ▸
       at 1 2 (K4⁻ ∷ Sb⁻0-1-23-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-Kd4 c4) ▸
       at 0 2 (K4⁻ ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K • iI)) ▸
       at 1 2 (Sb⁻0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·23·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOXd(0;1;23;4) | Kd4 @243243: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-Kd4-at243243 : Ws → ⟪ (Sb⁻0-1-42-3 ∷ K3⁻ ∷ []) ⟫ʷ ≈ ⟪ (K3⁻ ∷ Sb⁻0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-Kd4-at243243 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-42-3 ∷ K3⁻ ∷ []) (K3⁻ ∷ Sb⁻0-1-42-3 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Sb⁻0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·42·3⟩ (lit c4)) ▸
       at 2 2 (K4⁻ ∷ Sw34 ∷ []) (sym (wl0312 (lit c4))) ▸
       at 1 2 (K4⁻ ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-Kd4-at2332 c4) ▸
       at 0 2 (K3⁻ ∷ Sw34 ∷ []) (sym (wl0311 (lit c4))) ▸
       at 1 2 (Sb⁻0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto SBOXd(0;1;23;4) | Kd4 @0110243243: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-Kd4-at0110243243 : Ws → ⟪ (Sb⁻1-0-42-3 ∷ K3⁻ ∷ []) ⟫ʷ ≈ ⟪ (K3⁻ ∷ Sb⁻1-0-42-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-Kd4-at0110243243 c4 = run b0
  where
  b0 : Chain (Sb⁻1-0-42-3 ∷ K3⁻ ∷ []) (K3⁻ ∷ Sb⁻1-0-42-3 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Sb⁻0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·42·3⟩ (lit c4)) ▸
       at 2 2 (K3⁻ ∷ Sw01 ∷ []) (c₂ (Swap) ((K • iI) ↑)) ▸
       at 1 2 (K3⁻ ∷ Sb⁻0-1-42-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-Kd4-at243243 c4) ▸
       at 0 2 (K3⁻ ∷ Sw01 ∷ []) (c₂ (Swap) ((K • iI) ↑)) ▸
       at 1 2 (Sb⁻1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨0·1·42·3⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto SBOXd(0;1;23;4) | Kd4 @0210243143: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-Kd4-at0210243143 : Ws → ⟪ (Sb⁻2-0-41-3 ∷ K3⁻ ∷ []) ⟫ʷ ≈ ⟪ (K3⁻ ∷ Sb⁻2-0-41-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-Kd4-at0210243143 c4 = run b0
  where
  b0 : Chain (Sb⁻2-0-41-3 ∷ K3⁻ ∷ []) (K3⁻ ∷ Sb⁻2-0-41-3 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Sb⁻1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·41·3⟩ (lit c4)) ▸
       at 2 2 (K3⁻ ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K • iI)) ▸
       at 1 2 (K3⁻ ∷ Sb⁻1-0-42-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-Kd4-at0110243243 c4) ▸
       at 0 2 (K3⁻ ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K • iI)) ▸
       at 1 2 (Sb⁻2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·0·42·3⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto SBOXd(0;1;23;4) | SBOXd(0;1;4;3) @2332: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨0·1·4·3⟩-at2332 : Ws → ⟪ (Sb⁻0-1-32-4 ∷ Sb⁻0-1-4-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-4-2 ∷ Sb⁻0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨0·1·4·3⟩-at2332 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-32-4 ∷ Sb⁻0-1-4-2 ∷ []) (Sb⁻0-1-4-2 ∷ Sb⁻0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb⁻0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 (Sb⁻0-1-4-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·4·2⟩ (lit c4)) ▸
       at 1 2 (Sb⁻0-1-4-3 ∷ Sb⁻0-1-23-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨0·1·4·3⟩ c4) ▸
       at 0 2 (Sb⁻0-1-4-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·4·3⟩ (lit c4)) ▸
       at 1 2 (Sb⁻0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·23·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOXd(0;1;23;4) | SBOXd(0;1;4;3) @243243: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨0·1·4·3⟩-at243243 : Ws → ⟪ (Sb⁻0-1-42-3 ∷ Sb⁻0-1-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-3-2 ∷ Sb⁻0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨0·1·4·3⟩-at243243 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-42-3 ∷ Sb⁻0-1-3-2 ∷ []) (Sb⁻0-1-3-2 ∷ Sb⁻0-1-42-3 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Sb⁻0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·42·3⟩ (lit c4)) ▸
       at 2 2 (Sb⁻0-1-4-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·3·2⟩ (lit c4)) ▸
       at 1 2 (Sb⁻0-1-4-2 ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨0·1·4·3⟩-at2332 c4) ▸
       at 0 2 (Sb⁻0-1-3-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·4·2⟩ (lit c4)) ▸
       at 1 2 (Sb⁻0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto SBOXd(0;1;23;4) | SBOXd(0;1;4;3) @0110243243: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨0·1·4·3⟩-at0110243243 : Ws → ⟪ (Sb⁻1-0-42-3 ∷ Sb⁻1-0-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-3-2 ∷ Sb⁻1-0-42-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨0·1·4·3⟩-at0110243243 c4 = run b0
  where
  b0 : Chain (Sb⁻1-0-42-3 ∷ Sb⁻1-0-3-2 ∷ []) (Sb⁻1-0-3-2 ∷ Sb⁻1-0-42-3 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Sb⁻0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·42·3⟩ (lit c4)) ▸
       at 2 2 (Sb⁻0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·3·2⟩ (lit c4)) ▸
       at 1 2 (Sb⁻0-1-3-2 ∷ Sb⁻0-1-42-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨0·1·4·3⟩-at243243 c4) ▸
       at 0 2 (Sb⁻1-0-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨0·1·3·2⟩ (lit c4)) ▸
       at 1 2 (Sb⁻1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨0·1·42·3⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto SBOXd(0;1;23;4) | SBOXd(0;1;4;3) @0210243143: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨0·1·4·3⟩-at0210243143 : Ws → ⟪ (Sb⁻2-0-41-3 ∷ Sb⁻2-0-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-0-3-1 ∷ Sb⁻2-0-41-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨0·1·4·3⟩-at0210243143 c4 = run b0
  where
  b0 : Chain (Sb⁻2-0-41-3 ∷ Sb⁻2-0-3-1 ∷ []) (Sb⁻2-0-3-1 ∷ Sb⁻2-0-41-3 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Sb⁻1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·41·3⟩ (lit c4)) ▸
       at 2 2 (Sb⁻1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·3·1⟩ (lit c4)) ▸
       at 1 2 (Sb⁻1-0-3-2 ∷ Sb⁻1-0-42-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨0·1·4·3⟩-at0110243243 c4) ▸
       at 0 2 (Sb⁻2-0-3-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·0·3·2⟩ (lit c4)) ▸
       at 1 2 (Sb⁻2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·0·42·3⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto SBOXd(0;1;23;4) | TOFF012 @2332: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF012-at2332 : Ws → ⟪ (Sb⁻0-1-32-4 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ Sb⁻0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF012-at2332 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-32-4 ∷ Toff013 ∷ []) (Toff013 ∷ Sb⁻0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb⁻0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 (Toff012 ∷ Sw23 ∷ []) (lem-nat-2-TOFF013 (lit c4)) ▸
       at 1 2 (Toff012 ∷ Sb⁻0-1-23-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF012 c4) ▸
       at 0 2 (Toff013 ∷ Sw23 ∷ []) (lem-nat-2-TOFF012 (lit c4)) ▸
       at 1 2 (Sb⁻0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·23·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOXd(0;1;23;4) | TOFF012 @243243: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF012-at243243 : Ws → ⟪ (Sb⁻0-1-42-3 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ Sb⁻0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF012-at243243 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-42-3 ∷ Toff014 ∷ []) (Toff014 ∷ Sb⁻0-1-42-3 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Sb⁻0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·42·3⟩ (lit c4)) ▸
       at 2 2 (Toff013 ∷ Sw34 ∷ []) (lem-nat-3-TOFF014 (lit c4)) ▸
       at 1 2 (Toff013 ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF012-at2332 c4) ▸
       at 0 2 (Toff014 ∷ Sw34 ∷ []) (lem-nat-3-TOFF013 (lit c4)) ▸
       at 1 2 (Sb⁻0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto SBOXd(0;1;23;4) | TOFF012 @0110243243: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF012-at0110243243 : Ws → ⟪ (Sb⁻1-0-42-3 ∷ Toff104 ∷ []) ⟫ʷ ≈ ⟪ (Toff104 ∷ Sb⁻1-0-42-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF012-at0110243243 c4 = run b0
  where
  b0 : Chain (Sb⁻1-0-42-3 ∷ Toff104 ∷ []) (Toff104 ∷ Sb⁻1-0-42-3 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Sb⁻0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·42·3⟩ (lit c4)) ▸
       at 2 2 (Toff014 ∷ Sw01 ∷ []) (lem-nat-0-TOFF104 (lit c4)) ▸
       at 1 2 (Toff014 ∷ Sb⁻0-1-42-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF012-at243243 c4) ▸
       at 0 2 (Toff104 ∷ Sw01 ∷ []) (lem-nat-0-TOFF014 (lit c4)) ▸
       at 1 2 (Sb⁻1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨0·1·42·3⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto SBOXd(0;1;23;4) | TOFF012 @0210243143: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF012-at0210243143 : Ws → ⟪ (Sb⁻2-0-41-3 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ Sb⁻2-0-41-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF012-at0210243143 c4 = run b0
  where
  b0 : Chain (Sb⁻2-0-41-3 ∷ Toff204 ∷ []) (Toff204 ∷ Sb⁻2-0-41-3 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Sb⁻1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·41·3⟩ (lit c4)) ▸
       at 2 2 (Toff104 ∷ Sw12 ∷ []) (lem-nat-1-TOFF204 (lit c4)) ▸
       at 1 2 (Toff104 ∷ Sb⁻1-0-42-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF012-at0110243243 c4) ▸
       at 0 2 (Toff204 ∷ Sw12 ∷ []) (lem-nat-1-TOFF104 (lit c4)) ▸
       at 1 2 (Sb⁻2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·0·42·3⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto BOXd(0;1234) | CS40 @2332: 7 steps
lem-auto-BOXd⟨0·1234⟩-∣-CS40-at2332 : Ws → ⟪ (Bx⁻0-1324 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ Bx⁻0-1324 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-CS40-at2332 c4 = run b0
  where
  b0 : Chain (Bx⁻0-1324 ∷ CS04 ∷ []) (CS04 ∷ Bx⁻0-1324 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx⁻0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·1324⟩ (lit c4)) ▸
       at 2 2 (CS04 ∷ Sw23 ∷ []) (lem-nat-2-CS04 (lit c4)) ▸
       at 1 2 (CS04 ∷ Bx⁻0-1234 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-CS40 c4) ▸
       at 0 2 (CS04 ∷ Sw23 ∷ []) (lem-nat-2-CS04 (lit c4)) ▸
       at 1 2 (Bx⁻0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·1234⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto BOXd(0;1234) | CS40 @243243: 7 steps
lem-auto-BOXd⟨0·1234⟩-∣-CS40-at243243 : Ws → ⟪ (Bx⁻0-1423 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Bx⁻0-1423 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-CS40-at243243 c4 = run b0
  where
  b0 : Chain (Bx⁻0-1423 ∷ CS03 ∷ []) (CS03 ∷ Bx⁻0-1423 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Bx⁻0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨0·1423⟩ (lit c4)) ▸
       at 2 2 (CS04 ∷ Sw34 ∷ []) (lem-nat-3-CS03 (lit c4)) ▸
       at 1 2 (CS04 ∷ Bx⁻0-1324 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-CS40-at2332 c4) ▸
       at 0 2 (CS03 ∷ Sw34 ∷ []) (lem-nat-3-CS04 (lit c4)) ▸
       at 1 2 (Bx⁻0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨0·1324⟩ (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto BOXd(0;1234) | CS40 @0110243243: 7 steps
lem-auto-BOXd⟨0·1234⟩-∣-CS40-at0110243243 : Ws → ⟪ (Bx⁻1-0423 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Bx⁻1-0423 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-CS40-at0110243243 c4 = run b0
  where
  b0 : Chain (Bx⁻1-0423 ∷ CS13 ∷ []) (CS13 ∷ Bx⁻1-0423 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx⁻0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨1·0423⟩ (lit c4)) ▸
       at 2 2 (CS03 ∷ Sw01 ∷ []) (sym (wl0019 (lit c4))) ▸
       at 1 2 (CS03 ∷ Bx⁻0-1423 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-CS40-at243243 c4) ▸
       at 0 2 (CS13 ∷ Sw01 ∷ []) (sym (wl0061 (lit c4))) ▸
       at 1 2 (Bx⁻1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨0·1423⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto BOXd(0;1234) | CS40 @0210243143: 7 steps
lem-auto-BOXd⟨0·1234⟩-∣-CS40-at0210243143 : Ws → ⟪ (Bx⁻2-0413 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ Bx⁻2-0413 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-CS40-at0210243143 c4 = run b0
  where
  b0 : Chain (Bx⁻2-0413 ∷ CS23 ∷ []) (CS23 ∷ Bx⁻2-0413 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx⁻1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨2·0413⟩ (lit c4)) ▸
       at 2 2 (CS13 ∷ Sw12 ∷ []) (sym (wl0024 (lit c4))) ▸
       at 1 2 (CS13 ∷ Bx⁻1-0423 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-CS40-at0110243243 c4) ▸
       at 0 2 (CS23 ∷ Sw12 ∷ []) (sym (wl0025 (lit c4))) ▸
       at 1 2 (Bx⁻2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨1·0423⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- beta-T @01102332: 8 steps
lem-beta-T-at01102332 : Ws → ⟪ (Bx1-0324 ∷ []) ⟫ʷ ≈ ⟪ (Toff103 ∷ CCZ124 ∷ Toff103 ∷ CCZ124 ∷ []) ⟫ʷ
lem-beta-T-at01102332 c4 = run b0
  where
  b0 : Chain (Bx1-0324 ∷ []) (Toff103 ∷ CCZ124 ∷ Toff103 ∷ CCZ124 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx0-1324 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0324⟩ (lit c4)) ▸
       at 1 1 (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) (lem-beta-T-at2332 c4) ▸
       at 0 2 (Toff103 ∷ Sw01 ∷ []) (wl0101 (lit c4)) ▸
       at 1 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 (lit c4)) ▸
       at 2 2 (Toff103 ∷ Sw01 ∷ []) (wl0101 (lit c4)) ▸
       at 3 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 (lit c4)) ▸
       at 4 2 [] (wl0002 (lit c4)) ▸ done


-- beta-T @02102331: 8 steps
lem-beta-T-at02102331 : Ws → ⟪ (Bx2-0314 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ []) ⟫ʷ
lem-beta-T-at02102331 c4 = run b0
  where
  b0 : Chain (Bx2-0314 ∷ []) (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx1-0324 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0314⟩ (lit c4)) ▸
       at 1 1 (Toff103 ∷ CCZ124 ∷ Toff103 ∷ CCZ124 ∷ []) (lem-beta-T-at01102332 c4) ▸
       at 0 2 (Toff203 ∷ Sw12 ∷ []) (lem-nat-1-TOFF103 (lit c4)) ▸
       at 1 2 (CCZ124 ∷ Sw12 ∷ []) (sym (wl0078 (lit c4))) ▸
       at 2 2 (Toff203 ∷ Sw12 ∷ []) (lem-nat-1-TOFF103 (lit c4)) ▸
       at 3 2 (CCZ124 ∷ Sw12 ∷ []) (sym (wl0078 (lit c4))) ▸
       at 4 2 [] (wl0001 (lit c4)) ▸ done


-- beta-T @022330: 8 steps
lem-beta-T-at022330 : Ws → ⟪ (Bx2-1304 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ []) ⟫ʷ
lem-beta-T-at022330 c4 = run b0
  where
  b0 : Chain (Bx2-1304 ∷ []) (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx2-0314 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·1304⟩ (lit c4)) ▸
       at 1 1 (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ []) (lem-beta-T-at02102331 c4) ▸
       at 0 2 (Toff213 ∷ Sw01 ∷ []) (wl0104 (lit c4)) ▸
       at 1 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 (lit c4)) ▸
       at 2 2 (Toff213 ∷ Sw01 ∷ []) (wl0104 (lit c4)) ▸
       at 3 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 (lit c4)) ▸
       at 4 2 [] (wl0002 (lit c4)) ▸ done


-- sym34 @0220: 5 steps
lem-sym34-at0220 : Ws → ⟪ (Bx2-1034 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1043 ∷ []) ⟫ʷ
lem-sym34-at0220 c4 = run b0
  where
  b0 : Chain (Bx2-1034 ∷ []) (Bx2-1043 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx2-0134 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·1034⟩ (lit c4)) ▸
       at 1 1 (Bx2-0143 ∷ []) (lem-sym34-at021021 c4) ▸
       at 0 2 (Bx2-1043 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·0143⟩ (lit c4)) ▸
       at 1 2 [] (wl0002 (lit c4)) ▸ done


-- auto BOXd(0;1234) | CSd40 @2332: 7 steps
lem-auto-BOXd⟨0·1234⟩-∣-CSd40-at2332 : Ws → ⟪ (Bx⁻0-1324 ∷ CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS04⁻ ∷ Bx⁻0-1324 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-CSd40-at2332 c4 = run b0
  where
  b0 : Chain (Bx⁻0-1324 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ Bx⁻0-1324 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Bx⁻0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·1324⟩ (lit c4)) ▸
       at 2 2 (CS04⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd04 (lit c4)) ▸
       at 1 2 (CS04⁻ ∷ Bx⁻0-1234 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-CSd40 c4) ▸
       at 0 2 (CS04⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd04 (lit c4)) ▸
       at 1 2 (Bx⁻0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·1234⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto BOXd(0;1234) | CSd40 @243243: 7 steps
lem-auto-BOXd⟨0·1234⟩-∣-CSd40-at243243 : Ws → ⟪ (Bx⁻0-1423 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ Bx⁻0-1423 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-CSd40-at243243 c4 = run b0
  where
  b0 : Chain (Bx⁻0-1423 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ Bx⁻0-1423 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Bx⁻0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨0·1423⟩ (lit c4)) ▸
       at 2 2 (CS04⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd03 (lit c4)) ▸
       at 1 2 (CS04⁻ ∷ Bx⁻0-1324 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-CSd40-at2332 c4) ▸
       at 0 2 (CS03⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd04 (lit c4)) ▸
       at 1 2 (Bx⁻0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨0·1324⟩ (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto BOXd(0;1234) | CSd40 @0110243243: 7 steps
lem-auto-BOXd⟨0·1234⟩-∣-CSd40-at0110243243 : Ws → ⟪ (Bx⁻1-0423 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ Bx⁻1-0423 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-CSd40-at0110243243 c4 = run b0
  where
  b0 : Chain (Bx⁻1-0423 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ Bx⁻1-0423 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Bx⁻0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨1·0423⟩ (lit c4)) ▸
       at 2 2 (CS03⁻ ∷ Sw01 ∷ []) (sym (wl0022 (lit c4))) ▸
       at 1 2 (CS03⁻ ∷ Bx⁻0-1423 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-CSd40-at243243 c4) ▸
       at 0 2 (CS13⁻ ∷ Sw01 ∷ []) (sym (wl0121 (lit c4))) ▸
       at 1 2 (Bx⁻1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨0·1423⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto BOXd(0;1234) | CSd40 @0210243143: 7 steps
lem-auto-BOXd⟨0·1234⟩-∣-CSd40-at0210243143 : Ws → ⟪ (Bx⁻2-0413 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ Bx⁻2-0413 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-CSd40-at0210243143 c4 = run b0
  where
  b0 : Chain (Bx⁻2-0413 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Bx⁻2-0413 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Bx⁻1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨2·0413⟩ (lit c4)) ▸
       at 2 2 (CS13⁻ ∷ Sw12 ∷ []) (sym (wl0043 (lit c4))) ▸
       at 1 2 (CS13⁻ ∷ Bx⁻1-0423 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-CSd40-at0110243243 c4) ▸
       at 0 2 (CS23⁻ ∷ Sw12 ∷ []) (sym (wl0046 (lit c4))) ▸
       at 1 2 (Bx⁻2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨1·0423⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto CCZ012 | BOX(3;0142) @1221: 7 steps
lem-auto-CCZ012-∣-BOX⟨3·0142⟩-at1221 : Ws → ⟪ (CCZ012 ∷ Bx3-0241 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0241 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·0142⟩-at1221 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Bx3-0241 ∷ []) (Bx3-0241 ∷ CCZ012 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CCZ012 ∷ Sw12 ∷ []) (sym (wl0037 (lit c4))) ▸
       at 2 2 (Bx3-0142 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0241⟩ (lit c4)) ▸
       at 1 2 (Bx3-0142 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0142⟩ c4) ▸
       at 0 2 (Bx3-0241 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0142⟩ (lit c4)) ▸
       at 1 2 (CCZ012 ∷ Sw12 ∷ []) (sym (wl0037 (lit c4))) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto CCZ012 | BOX(3;0142) @132132: 7 steps
lem-auto-CCZ012-∣-BOX⟨3·0142⟩-at132132 : Ws → ⟪ (CCZ013 ∷ Bx2-0341 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0341 ∷ CCZ013 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·0142⟩-at132132 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ Bx2-0341 ∷ []) (Bx2-0341 ∷ CCZ013 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 (lit c4)) ▸
       at 2 2 (Bx3-0241 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0341⟩ (lit c4)) ▸
       at 1 2 (Bx3-0241 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0142⟩-at1221 c4) ▸
       at 0 2 (Bx2-0341 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0241⟩ (lit c4)) ▸
       at 1 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto CCZ012 | BOX(3;0142) @14213243: 7 steps
lem-auto-CCZ012-∣-BOX⟨3·0142⟩-at14213243 : Ws → ⟪ (CCZ014 ∷ Bx2-0431 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0431 ∷ CCZ014 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·0142⟩-at14213243 c4 = run b0
  where
  b0 : Chain (CCZ014 ∷ Bx2-0431 ∷ []) (Bx2-0431 ∷ CCZ014 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 (lit c4)) ▸
       at 2 2 (Bx2-0341 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·0431⟩ (lit c4)) ▸
       at 1 2 (Bx2-0341 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0142⟩-at132132 c4) ▸
       at 0 2 (Bx2-0431 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·0341⟩ (lit c4)) ▸
       at 1 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto CCZ012 | BOX(3;0142) @143143: 7 steps
lem-auto-CCZ012-∣-BOX⟨3·0142⟩-at143143 : Ws → ⟪ (CCZ024 ∷ Bx1-0432 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0432 ∷ CCZ024 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·0142⟩-at143143 c4 = run b0
  where
  b0 : Chain (CCZ024 ∷ Bx1-0432 ∷ []) (Bx1-0432 ∷ CCZ024 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 (lit c4)) ▸
       at 2 2 (Bx2-0431 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0432⟩ (lit c4)) ▸
       at 1 2 (Bx2-0431 ∷ CCZ014 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0142⟩-at14213243 c4) ▸
       at 0 2 (Bx1-0432 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0431⟩ (lit c4)) ▸
       at 1 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto CCZ012 | BOX(3;0142) @14233142: 7 steps
lem-auto-CCZ012-∣-BOX⟨3·0142⟩-at14233142 : Ws → ⟪ (CCZ034 ∷ Bx1-0423 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0423 ∷ CCZ034 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·0142⟩-at14233142 c4 = run b0
  where
  b0 : Chain (CCZ034 ∷ Bx1-0423 ∷ []) (Bx1-0423 ∷ CCZ034 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 (lit c4)) ▸
       at 2 2 (Bx1-0432 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·0423⟩ (lit c4)) ▸
       at 1 2 (Bx1-0432 ∷ CCZ024 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0142⟩-at143143 c4) ▸
       at 0 2 (Bx1-0423 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·0432⟩ (lit c4)) ▸
       at 1 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto CCZ012 | BOX(3;0142) @14233241: 7 steps
lem-auto-CCZ012-∣-BOX⟨3·0142⟩-at14233241 : Ws → ⟪ (CCZ034 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ CCZ034 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·0142⟩-at14233241 c4 = run b0
  where
  b0 : Chain (CCZ034 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ CCZ034 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 (lit c4)) ▸
       at 2 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4)) ▸
       at 1 2 (Bx1-0423 ∷ CCZ034 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0142⟩-at14233142 c4) ▸
       at 0 2 (Bx2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0423⟩ (lit c4)) ▸
       at 1 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | BOX(0;1234) @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·1234⟩-at2332 : Ws → ⟪ (Sb0-1-32-4 ∷ Bx0-1324 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·1234⟩-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ Bx0-1324 ∷ []) (Bx0-1324 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ (lit c4)) ▸
       at 1 2 (Bx0-1234 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·1234⟩ c4) ▸
       at 0 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | BOX(0;1234) @243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·1234⟩-at243243 : Ws → ⟪ (Sb0-1-42-3 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·1234⟩-at243243 c4 = run b0
  where
  b0 : Chain (Sb0-1-42-3 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ Sb0-1-42-3 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 2 2 (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ (lit c4)) ▸
       at 1 2 (Bx0-1324 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·1234⟩-at2332 c4) ▸
       at 0 2 (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ (lit c4)) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | BOX(0;1234) @0110243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·1234⟩-at0110243243 : Ws → ⟪ (Sb1-0-42-3 ∷ Bx1-0423 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0423 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·1234⟩-at0110243243 c4 = run b0
  where
  b0 : Chain (Sb1-0-42-3 ∷ Bx1-0423 ∷ []) (Bx1-0423 ∷ Sb1-0-42-3 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 2 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ (lit c4)) ▸
       at 1 2 (Bx0-1423 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·1234⟩-at243243 c4) ▸
       at 0 2 (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ (lit c4)) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | BOX(0;1234) @0210243143: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·1234⟩-at0210243143 : Ws → ⟪ (Sb2-0-41-3 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·1234⟩-at0210243143 c4 = run b0
  where
  b0 : Chain (Sb2-0-41-3 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ Sb2-0-41-3 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·41·3⟩ (lit c4)) ▸
       at 2 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ (lit c4)) ▸
       at 1 2 (Bx1-0423 ∷ Sb1-0-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨0·1234⟩-at0110243243 c4) ▸
       at 0 2 (Bx2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0423⟩ (lit c4)) ▸
       at 1 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto CCZ012 | SBOX(3;0;14;2) @1221: 7 steps
lem-auto-CCZ012-∣-SBOX⟨3·0·14·2⟩-at1221 : Ws → ⟪ (CCZ012 ∷ Sb3-0-24-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-24-1 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨3·0·14·2⟩-at1221 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Sb3-0-24-1 ∷ []) (Sb3-0-24-1 ∷ CCZ012 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CCZ012 ∷ Sw12 ∷ []) (sym (wl0037 (lit c4))) ▸
       at 2 2 (Sb3-0-14-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·24·1⟩ (lit c4)) ▸
       at 1 2 (Sb3-0-14-2 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨3·0·14·2⟩ c4) ▸
       at 0 2 (Sb3-0-24-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·14·2⟩ (lit c4)) ▸
       at 1 2 (CCZ012 ∷ Sw12 ∷ []) (sym (wl0037 (lit c4))) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto CCZ012 | SBOX(3;0;14;2) @132132: 7 steps
lem-auto-CCZ012-∣-SBOX⟨3·0·14·2⟩-at132132 : Ws → ⟪ (CCZ013 ∷ Sb2-0-34-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-34-1 ∷ CCZ013 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨3·0·14·2⟩-at132132 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ Sb2-0-34-1 ∷ []) (Sb2-0-34-1 ∷ CCZ013 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 (lit c4)) ▸
       at 2 2 (Sb3-0-24-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨2·0·34·1⟩ (lit c4)) ▸
       at 1 2 (Sb3-0-24-1 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨3·0·14·2⟩-at1221 c4) ▸
       at 0 2 (Sb2-0-34-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·0·24·1⟩ (lit c4)) ▸
       at 1 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto CCZ012 | SBOX(3;0;14;2) @14213243: 7 steps
lem-auto-CCZ012-∣-SBOX⟨3·0·14·2⟩-at14213243 : Ws → ⟪ (CCZ014 ∷ Sb2-0-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-43-1 ∷ CCZ014 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨3·0·14·2⟩-at14213243 c4 = run b0
  where
  b0 : Chain (CCZ014 ∷ Sb2-0-43-1 ∷ []) (Sb2-0-43-1 ∷ CCZ014 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 (lit c4)) ▸
       at 2 2 (Sb2-0-34-1 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨2·0·43·1⟩ (lit c4)) ▸
       at 1 2 (Sb2-0-34-1 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨3·0·14·2⟩-at132132 c4) ▸
       at 0 2 (Sb2-0-43-1 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨2·0·34·1⟩ (lit c4)) ▸
       at 1 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto CCZ012 | SBOX(3;0;14;2) @143143: 7 steps
lem-auto-CCZ012-∣-SBOX⟨3·0·14·2⟩-at143143 : Ws → ⟪ (CCZ024 ∷ Sb1-0-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-43-2 ∷ CCZ024 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨3·0·14·2⟩-at143143 c4 = run b0
  where
  b0 : Chain (CCZ024 ∷ Sb1-0-43-2 ∷ []) (Sb1-0-43-2 ∷ CCZ024 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 (lit c4)) ▸
       at 2 2 (Sb2-0-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·43·2⟩ (lit c4)) ▸
       at 1 2 (Sb2-0-43-1 ∷ CCZ014 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨3·0·14·2⟩-at14213243 c4) ▸
       at 0 2 (Sb1-0-43-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·43·1⟩ (lit c4)) ▸
       at 1 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto CCZ012 | SBOX(3;0;14;2) @14233142: 7 steps
lem-auto-CCZ012-∣-SBOX⟨3·0·14·2⟩-at14233142 : Ws → ⟪ (CCZ034 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-42-3 ∷ CCZ034 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨3·0·14·2⟩-at14233142 c4 = run b0
  where
  b0 : Chain (CCZ034 ∷ Sb1-0-42-3 ∷ []) (Sb1-0-42-3 ∷ CCZ034 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 1 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 (lit c4)) ▸
       at 2 2 (Sb1-0-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 1 2 (Sb1-0-43-2 ∷ CCZ024 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨3·0·14·2⟩-at143143 c4) ▸
       at 0 2 (Sb1-0-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·43·2⟩ (lit c4)) ▸
       at 1 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 (lit c4)) ▸
       at 2 2 [] (wl0006 (lit c4)) ▸ done


-- auto CCZ012 | SBOX(3;0;14;2) @14233241: 7 steps
lem-auto-CCZ012-∣-SBOX⟨3·0·14·2⟩-at14233241 : Ws → ⟪ (CCZ034 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ CCZ034 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨3·0·14·2⟩-at14233241 c4 = run b0
  where
  b0 : Chain (CCZ034 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ CCZ034 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 (lit c4)) ▸
       at 2 2 (Sb1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·41·3⟩ (lit c4)) ▸
       at 1 2 (Sb1-0-42-3 ∷ CCZ034 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨3·0·14·2⟩-at14233142 c4) ▸
       at 0 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 1 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | K4 @243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at243243 : Ws → ⟪ (Sb0-1-42-3 ∷ K3 ∷ []) ⟫ʷ ≈ ⟪ (K3 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at243243 c4 = run b0
  where
  b0 : Chain (Sb0-1-42-3 ∷ K3 ∷ []) (K3 ∷ Sb0-1-42-3 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 2 2 (K4 ∷ Sw34 ∷ []) (sym (wl0067 (lit c4))) ▸
       at 1 2 (K4 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at2332 c4) ▸
       at 0 2 (K3 ∷ Sw34 ∷ []) (sym (wl0068 (lit c4))) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | K4 @0110243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at0110243243 : Ws → ⟪ (Sb1-0-42-3 ∷ K3 ∷ []) ⟫ʷ ≈ ⟪ (K3 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at0110243243 c4 = run b0
  where
  b0 : Chain (Sb1-0-42-3 ∷ K3 ∷ []) (K3 ∷ Sb1-0-42-3 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 2 2 (K3 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑)) ▸
       at 1 2 (K3 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at243243 c4) ▸
       at 0 2 (K3 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑)) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | K4 @0210243143: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at0210243143 : Ws → ⟪ (Sb2-0-41-3 ∷ K3 ∷ []) ⟫ʷ ≈ ⟪ (K3 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at0210243143 c4 = run b0
  where
  b0 : Chain (Sb2-0-41-3 ∷ K3 ∷ []) (K3 ∷ Sb2-0-41-3 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·41·3⟩ (lit c4)) ▸
       at 2 2 (K3 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K)) ▸
       at 1 2 (K3 ∷ Sb1-0-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at0110243243 c4) ▸
       at 0 2 (K3 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K)) ▸
       at 1 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | CS24 @243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS24-at243243 : Ws → ⟪ (Sb0-1-42-3 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS24-at243243 c4 = run b0
  where
  b0 : Chain (Sb0-1-42-3 ∷ CS34 ∷ []) (CS34 ∷ Sb0-1-42-3 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 2 2 (CS34 ∷ Sw34 ∷ []) (sym (wl0039 (lit c4))) ▸
       at 1 2 (CS34 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS24-at2332 c4) ▸
       at 0 2 (CS34 ∷ Sw34 ∷ []) (sym (wl0039 (lit c4))) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | CS24 @0110243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS24-at0110243243 : Ws → ⟪ (Sb1-0-42-3 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS24-at0110243243 c4 = run b0
  where
  b0 : Chain (Sb1-0-42-3 ∷ CS34 ∷ []) (CS34 ∷ Sb1-0-42-3 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 2 2 (CS34 ∷ Sw01 ∷ []) (c₂ (Swap) (CS ↑)) ▸
       at 1 2 (CS34 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS24-at243243 c4) ▸
       at 0 2 (CS34 ∷ Sw01 ∷ []) (c₂ (Swap) (CS ↑)) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | CS24 @0210243143: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS24-at0210243143 : Ws → ⟪ (Sb2-0-41-3 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS24-at0210243143 c4 = run b0
  where
  b0 : Chain (Sb2-0-41-3 ∷ CS34 ∷ []) (CS34 ∷ Sb2-0-41-3 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 (lit c4))) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·41·3⟩ (lit c4)) ▸
       at 2 2 (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS)) ▸
       at 1 2 (CS34 ∷ Sb1-0-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS24-at0110243243 c4) ▸
       at 0 2 (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS)) ▸
       at 1 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 2 2 [] (wl0001 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | Kd4 @243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd4-at243243 : Ws → ⟪ (Sb0-1-42-3 ∷ K3⁻ ∷ []) ⟫ʷ ≈ ⟪ (K3⁻ ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd4-at243243 c4 = run b0
  where
  b0 : Chain (Sb0-1-42-3 ∷ K3⁻ ∷ []) (K3⁻ ∷ Sb0-1-42-3 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 (lit c4))) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 2 2 (K4⁻ ∷ Sw34 ∷ []) (sym (wl0312 (lit c4))) ▸
       at 1 2 (K4⁻ ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd4-at2332 c4) ▸
       at 0 2 (K3⁻ ∷ Sw34 ∷ []) (sym (wl0311 (lit c4))) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·32·4⟩ (lit c4)) ▸
       at 2 2 [] (wl0007 (lit c4)) ▸ done


-- auto SBOX(0;1;23;4) | Kd4 @0110243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd4-at0110243243 : Ws → ⟪ (Sb1-0-42-3 ∷ K3⁻ ∷ []) ⟫ʷ ≈ ⟪ (K3⁻ ∷ Sb1-0-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd4-at0110243243 c4 = run b0
  where
  b0 : Chain (Sb1-0-42-3 ∷ K3⁻ ∷ []) (K3⁻ ∷ Sb1-0-42-3 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 (lit c4))) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·42·3⟩ (lit c4)) ▸
       at 2 2 (K3⁻ ∷ Sw01 ∷ []) (c₂ (Swap) ((K • iI) ↑)) ▸
       at 1 2 (K3⁻ ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-Kd4-at243243 c4) ▸
       at 0 2 (K3⁻ ∷ Sw01 ∷ []) (c₂ (Swap) ((K • iI) ↑)) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ (lit c4)) ▸
       at 2 2 [] (wl0002 (lit c4)) ▸ done

