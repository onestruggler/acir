{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D153 where

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
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-beta-T-at13243142 ; lem-sym12 ; lem-sym23)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-sym12-at1221 ; lem-sym12-at132132 ; lem-sym23-at1221 ; lem-sym34-at132132)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-auto-BOX⟨0·1234⟩-∣-CCZ342 ; lem-sym12-at233442 ; lem-sym23-at122331 ; lem-sym23-at13213442 ; lem-sym23-at13243142 ; lem-sym23-at2332 ; lem-sym34-at13213442 ; lem-sym34-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-CS20-beta-c-at1221 ; lem-sym12-at2332 ; lem-sym34-at233442)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-CX23-beta-at243243 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-CS21-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D006 using (lem-sym12-at0113203442)
open import Examples.Groups.Clifford+CS.Five.D.D007 using (lem-SBsym-at0113203442 ; lem-T312-beta-at3443 ; lem-sym12-at0110233442)
open import Examples.Groups.Clifford+CS.Five.D.D008 using (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS41-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D010 using (lem-CS20-beta-ci-at1221)
open import Examples.Groups.Clifford+CS.Five.D.D011 using (lem-sym23-at233442 ; lem-sym23-at2442 ; lem-sym34-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D080 using (lem-sym23-at0113203442 ; lem-sym23-at0113243042)
open import Examples.Groups.Clifford+CS.Five.D.D135 using (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS12-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D136 using (lem-auto-BOX⟨0·1234⟩-∣-CSd12-at2332 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-CS42-at2332 ; lem-beta-T-at0410233142 ; lem-beta-T-at0412233041)
open import Examples.Groups.Clifford+CS.Five.D.D137 using (lem-auto-CCZ012-∣-CCZ342-at0110)
open import Examples.Groups.Clifford+CS.Five.D.D139 using (lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D142 using (lem-auto-BOX⟨0·1234⟩-∣-CCZ102)
open import Examples.Groups.Clifford+CS.Five.D.D150 using (lem-T312-beta-at13243142 ; lem-sym23-at13243241 ; lem-sym23-at133441)
open import Examples.Groups.Clifford+CS.Five.D.D152 using (lem-CX23-beta-at2442 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ143 ; lem-auto-BOX⟨0·1234⟩-∣-CSd21-at2332)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-1-BOX⟨0·2413⟩ ; lem-nat-1-CCZ023 ; lem-nat-2-BOX⟨0·1234⟩ ; lem-nat-2-BOX⟨0·1324⟩ ; lem-nat-2-BOX⟨0·3412⟩ ; lem-nat-2-CCZ012 ; lem-nat-2-CCZ013 ; lem-nat-3-BOX⟨0·1243⟩)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-1-BOX⟨0·1423⟩ ; lem-nat-1-CCZ013 ; lem-nat-2-BOX⟨0·2413⟩)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-2-CCZ124 ; lem-nat-2-CCZ134)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-2-TOFF413)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-0-TOFF403 ; lem-nat-1-BOX⟨0·1243⟩)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-2-BOX⟨0·2143⟩)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-0-TOFF401 ; lem-nat-0-TOFF413 ; lem-nat-1-BOX⟨0·1324⟩ ; lem-nat-1-TOFF401 ; lem-nat-2-TOFF402 ; lem-nat-3-TOFF301)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-nat-0-BOX⟨0·1243⟩ ; lem-nat-0-BOX⟨1·0243⟩ ; lem-nat-3-BOX⟨0·1234⟩)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-nat-1-BOX⟨0·2143⟩ ; lem-nat-1-BOX⟨0·2314⟩ ; lem-nat-2-BOX⟨0·3142⟩ ; lem-nat-3-BOX⟨0·2134⟩)
open import Examples.Groups.Clifford+CS.Five.D.R012 using (lem-nat-1-CS01 ; lem-nat-1-CS02)
open import Examples.Groups.Clifford+CS.Five.D.R013 using (lem-nat-0-BOX⟨0·1324⟩ ; lem-nat-2-TOFF403)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-nat-1-CSd02 ; lem-nat-2-SBOX⟨0·1·4·2⟩ ; lem-nat-2-SBOX⟨0·1·4·3⟩ ; lem-nat-2-SBOXd⟨0·1·4·2⟩ ; lem-nat-2-SBOXd⟨0·1·4·3⟩ ; lem-nat-3-SBOX⟨0·1·3·2⟩ ; lem-nat-3-SBOX⟨0·1·4·2⟩ ; lem-nat-3-SBOXd⟨0·1·3·2⟩ ; lem-nat-3-SBOXd⟨0·1·4·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R015 using (lem-nat-1-CSd01)
open import Examples.Groups.Clifford+CS.Five.D.R016 using (lem-nat-0-BOX⟨1·0324⟩ ; lem-nat-0-TOFF034 ; lem-nat-1-TOFF403)
open import Examples.Groups.Clifford+CS.Five.D.R017 using (lem-nat-1-TOFF402 ; lem-nat-2-BOX⟨1·0234⟩ ; lem-nat-3-TOFF401)
open import Examples.Groups.Clifford+CS.Five.D.R019 using (lem-nat-2-SBOX⟨0·1·2·3⟩ ; lem-nat-2-SBOX⟨0·1·3·2⟩ ; lem-nat-2-SBOXd⟨0·1·2·3⟩ ; lem-nat-2-SBOXd⟨0·1·3·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R020 using (lem-nat-2-BOX⟨1·0243⟩)
open import Examples.Groups.Clifford+CS.Five.D.R021 using (lem-nat-1-BOX⟨0·1432⟩)
open import Examples.Groups.Clifford+CS.Five.D.R024 using (lem-nat-0-SBOXd⟨0·2·4·3⟩ ; lem-nat-0-SBOXd⟨1·2·4·3⟩ ; lem-nat-1-SBOXd⟨0·1·4·3⟩ ; lem-nat-1-SBOXd⟨0·2·4·3⟩)
open import Examples.Groups.Clifford+CS.Five.D.R025 using (lem-nat-0-BOX⟨0·3412⟩ ; lem-nat-0-BOX⟨1·3402⟩ ; lem-nat-3-BOX⟨1·0243⟩)
open import Examples.Groups.Clifford+CS.Five.D.R026 using (lem-nat-2-BOX⟨1·0342⟩ ; lem-nat-3-BOX⟨1·0234⟩)
open import Examples.Groups.Clifford+CS.Five.D.R028 using (lem-nat-2-BOX⟨1·0324⟩)
open import Examples.Groups.Clifford+CS.Five.D.R029 using (lem-nat-1-BOX⟨4·0321⟩)
open import Examples.Groups.Clifford+CS.Five.D.R030 using (lem-comm-SBOXd⟨0·1·2·3⟩-TOFF403)
open import Examples.Groups.Clifford+CS.Five.D.R031 using (lem-nat-0-BOX⟨0·3241⟩ ; lem-nat-0-BOX⟨1·3240⟩ ; lem-nat-1-BOX⟨0·3142⟩ ; lem-nat-1-BOX⟨0·3241⟩)
open import Examples.Groups.Clifford+CS.Five.D.R033 using (lem-nat-0-BOX⟨0·3421⟩ ; lem-nat-0-BOX⟨1·3420⟩ ; lem-nat-1-BOX⟨0·3421⟩)
open import Examples.Groups.Clifford+CS.Five.D.R034 using (lem-nat-0-SBOXd⟨2·3·4·0⟩ ; lem-nat-0-SBOXd⟨2·3·4·1⟩ ; lem-nat-1-SBOXd⟨1·3·4·2⟩ ; lem-nat-1-SBOXd⟨2·3·4·1⟩ ; lem-nat-2-BOX⟨0·2431⟩ ; lem-nat-2-SBOXd⟨1·2·4·3⟩ ; lem-nat-2-SBOXd⟨1·3·4·2⟩ ; lem-nat-3-SBOXd⟨2·3·4·0⟩ ; lem-nat-3-SBOXd⟨2·4·3·0⟩)
open import Examples.Groups.Clifford+CS.Five.D.R035 using (lem-comm-CCZ023-SBOX⟨0·1·4·3⟩ ; lem-comm-CCZ023-SBOXd⟨0·1·4·3⟩ ; lem-nat-3-BOX⟨0·2143⟩)
-- auto BOX(0;1234) | CCZ143 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ143-at2332 : Complete 4 → ⟪ (Bx0-1324 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ143-at2332 c4 = run b0
  where
  b0 : Chain (Bx0-1324 ∷ CCZ124 ∷ []) (CCZ124 ∷ Bx0-1324 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ c4) ▸
       at 2 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 1 2 (CCZ134 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ143 c4) ▸
       at 0 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 1 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CCZ143: 32 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ143 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ143 c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (Sb0-1-23-4 ∷ CCZ134 ∷ []) (CS13 ∷ Bx0-1324 ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ CX43 ∷ CS13⁻ ∷ CX43 ∷ Sb⁻0-1-4-2 ∷ CS14 ∷ [])
  b0 = at 1 1 (CS13 ∷ CX43 ∷ CS13⁻ ∷ CX43 ∷ CS14 ∷ []) (lw0 c4 (CCZ134 ∷ []) (CS13 ∷ CX43 ∷ CS13⁻ ∷ CX43 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (CS13 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS21-at2332 c4) ▸
       at 1 1 (Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ []) (refl) ▸
       at 5 1 (CS14⁻ ∷ []) (refl) ▸
       at 5 4 (CX43 ∷ CS13⁻ ∷ CX43 ∷ CS14⁻ ∷ []) (lw0 c4 (CS14⁻ ∷ CX43 ∷ CS13⁻ ∷ CX43 ∷ []) (CX43 ∷ CS13⁻ ∷ CX43 ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 8 1 (Sb⁻0-1-4-2 ∷ []) (refl) ▸
       at 3 1 (CS14 ∷ []) (refl) ▸ done

  b1 : Chain (CS13 ∷ Bx0-1324 ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ CX43 ∷ CS13⁻ ∷ CX43 ∷ Sb⁻0-1-4-2 ∷ CS14 ∷ []) (CS13 ∷ CX43 ∷ Bx0-1324 ∷ CCZ124 ∷ CS13⁻ ∷ CX43 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS14 ∷ [])
  b1 = at 2 6 (CX43 ∷ CS13⁻ ∷ CX43 ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ []) (lw0 c4 (Toff423 ∷ CS14 ∷ Toff423 ∷ CX43 ∷ CS13⁻ ∷ CX43 ∷ []) (CX43 ∷ CS13⁻ ∷ CX43 ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Sb0-1-4-2 ∷ []) (refl) ▸
       at 1 0 (CX43 ∷ CX43 ∷ []) (lw0 c4 [] (CX43 ∷ CX43 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Bx0-1342 ∷ []) (lem-sym34-at2332 c4) ▸
       at 3 1 (Bx0-1432 ∷ []) (lem-sym23-at233442 c4) ▸
       at 2 3 (Bx0-1432 ∷ CCZ124 ∷ []) (lem-CX23-beta-at2442 c4) ▸
       at 2 1 (Bx0-1342 ∷ []) (lem-sym23-at2442 c4) ▸
       at 2 1 (Bx0-1324 ∷ []) (lem-sym34-at233442 c4) ▸ done

  b2 : Chain (CS13 ∷ CX43 ∷ Bx0-1324 ∷ CCZ124 ∷ CS13⁻ ∷ CX43 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS14 ∷ []) (CS13 ∷ CX43 ∷ CCZ124 ∷ CS13⁻ ∷ CX43 ∷ Bx0-1324 ∷ CCZ124 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS14 ∷ [])
  b2 = at 2 2 (CCZ124 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ143-at2332 c4) ▸
       at 3 2 (CS13⁻ ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd21-at2332 c4) ▸
       at 4 0 (CX43 ∷ CX43 ∷ []) (lw0 c4 [] (CX43 ∷ CX43 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Bx0-1342 ∷ []) (lem-sym34-at2332 c4) ▸
       at 6 1 (Bx0-1432 ∷ []) (lem-sym23-at233442 c4) ▸
       at 5 3 (Bx0-1432 ∷ CCZ124 ∷ []) (lem-CX23-beta-at2442 c4) ▸
       at 5 1 (Bx0-1342 ∷ []) (lem-sym23-at2442 c4) ▸
       at 5 1 (Bx0-1324 ∷ []) (lem-sym34-at233442 c4) ▸ done

  b3 : Chain (CS13 ∷ CX43 ∷ CCZ124 ∷ CS13⁻ ∷ CX43 ∷ Bx0-1324 ∷ CCZ124 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS14 ∷ []) (CCZ134 ∷ Sb0-1-23-4 ∷ [])
  b3 = at 5 2 (CCZ124 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ143-at2332 c4) ▸
       at 1 2 (CCZ124 ∷ CX43 ∷ []) (lw0 c4 (CX43 ∷ CCZ124 ∷ []) (CCZ124 ∷ CX43 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (CCZ124 ∷ CX43 ∷ CS13⁻ ∷ CX43 ∷ []) (lw0 c4 (CX43 ∷ CS13⁻ ∷ CX43 ∷ CCZ124 ∷ []) (CCZ124 ∷ CX43 ∷ CS13⁻ ∷ CX43 ∷ []) tt tt Eq.refl) ▸
       at 1 2 [] (lw0 c4 (CCZ124 ∷ CCZ124 ∷ []) [] tt tt Eq.refl) ▸
       at 4 5 (Sb0-1-32-4 ∷ []) (refl) ▸
       at 4 2 (CS14 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS41-at2332 c4) ▸
       at 5 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 0 5 (CCZ134 ∷ []) (lw0 c4 (CS13 ∷ CX43 ∷ CS13⁻ ∷ CX43 ∷ CS14 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl) ▸ done


-- auto CSd01 | BOX(0;2314): 3 steps
lem-auto-CSd01-∣-BOX⟨0·2314⟩ : Complete 4 → ⟪ (CS01⁻ ∷ Bx0-2314 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2314 ∷ CS01⁻ ∷ []) ⟫ʷ
lem-auto-CSd01-∣-BOX⟨0·2314⟩ c4 = run b0
  where
  b0 : Chain (CS01⁻ ∷ Bx0-2314 ∷ []) (Bx0-2314 ∷ CS01⁻ ∷ [])
  b0 = at 1 1 (Bx0-2134 ∷ []) (lem-sym23-at122331 c4) ▸
       at 0 2 (Bx0-2134 ∷ CS01⁻ ∷ []) (lem-CS20-beta-ci-at1221 c4) ▸
       at 0 1 (Bx0-2314 ∷ []) (lem-sym23-at1221 c4) ▸ done


-- auto CSd01 | BOX(0;2314) @1221: 7 steps
lem-auto-CSd01-∣-BOX⟨0·2314⟩-at1221 : Complete 4 → ⟪ (CS02⁻ ∷ Bx0-1324 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ CS02⁻ ∷ []) ⟫ʷ
lem-auto-CSd01-∣-BOX⟨0·2314⟩-at1221 c4 = run b0
  where
  b0 : Chain (CS02⁻ ∷ Bx0-1324 ∷ []) (Bx0-1324 ∷ CS02⁻ ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS01⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd02 c4) ▸
       at 2 2 (Bx0-2314 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1324⟩ c4) ▸
       at 1 2 (Bx0-2314 ∷ CS01⁻ ∷ []) (lem-auto-CSd01-∣-BOX⟨0·2314⟩ c4) ▸
       at 0 2 (Bx0-1324 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2314⟩ c4) ▸
       at 1 2 (CS02⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd01 c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CSd01 | BOX(0;2314) @011220: 7 steps
lem-auto-CSd01-∣-BOX⟨0·2314⟩-at011220 : Complete 4 → ⟪ (CS12⁻ ∷ Bx1-0324 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0324 ∷ CS12⁻ ∷ []) ⟫ʷ
lem-auto-CSd01-∣-BOX⟨0·2314⟩-at011220 c4 = run b0
  where
  b0 : Chain (CS12⁻ ∷ Bx1-0324 ∷ []) (Bx1-0324 ∷ CS12⁻ ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS02⁻ ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS12⁻ ∷ []) (CS02⁻ ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-1324 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0324⟩ c4) ▸
       at 1 2 (Bx0-1324 ∷ CS02⁻ ∷ []) (lem-auto-CSd01-∣-BOX⟨0·2314⟩-at1221 c4) ▸
       at 0 2 (Bx1-0324 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1324⟩ c4) ▸
       at 1 2 (CS12⁻ ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS02⁻ ∷ []) (CS12⁻ ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;2;3) | BOX(1;0324): 3 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨1·0324⟩ : Complete 4 → ⟪ (Sb⁻0-1-2-3 ∷ Bx1-0324 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0324 ∷ Sb⁻0-1-2-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨1·0324⟩ c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-2-3 ∷ Bx1-0324 ∷ []) (Bx1-0324 ∷ Sb⁻0-1-2-3 ∷ [])
  b0 = at 0 1 (CS12⁻ ∷ []) (refl) ▸
       at 0 2 (Bx1-0324 ∷ CS12⁻ ∷ []) (lem-auto-CSd01-∣-BOX⟨0·2314⟩-at011220 c4) ▸
       at 1 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸ done


-- auto CS01 | BOX(0;2314): 3 steps
lem-auto-CS01-∣-BOX⟨0·2314⟩ : Complete 4 → ⟪ (CS01 ∷ Bx0-2314 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2314 ∷ CS01 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨0·2314⟩ c4 = run b0
  where
  b0 : Chain (CS01 ∷ Bx0-2314 ∷ []) (Bx0-2314 ∷ CS01 ∷ [])
  b0 = at 1 1 (Bx0-2134 ∷ []) (lem-sym23-at122331 c4) ▸
       at 0 2 (Bx0-2134 ∷ CS01 ∷ []) (lem-CS20-beta-c-at1221 c4) ▸
       at 0 1 (Bx0-2314 ∷ []) (lem-sym23-at1221 c4) ▸ done


-- auto CS01 | BOX(0;2314) @1221: 7 steps
lem-auto-CS01-∣-BOX⟨0·2314⟩-at1221 : Complete 4 → ⟪ (CS02 ∷ Bx0-1324 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ CS02 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨0·2314⟩-at1221 c4 = run b0
  where
  b0 : Chain (CS02 ∷ Bx0-1324 ∷ []) (Bx0-1324 ∷ CS02 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS01 ∷ Sw12 ∷ []) (lem-nat-1-CS02 c4) ▸
       at 2 2 (Bx0-2314 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1324⟩ c4) ▸
       at 1 2 (Bx0-2314 ∷ CS01 ∷ []) (lem-auto-CS01-∣-BOX⟨0·2314⟩ c4) ▸
       at 0 2 (Bx0-1324 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2314⟩ c4) ▸
       at 1 2 (CS02 ∷ Sw12 ∷ []) (lem-nat-1-CS01 c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CS01 | BOX(0;2314) @011220: 7 steps
lem-auto-CS01-∣-BOX⟨0·2314⟩-at011220 : Complete 4 → ⟪ (CS12 ∷ Bx1-0324 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0324 ∷ CS12 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨0·2314⟩-at011220 c4 = run b0
  where
  b0 : Chain (CS12 ∷ Bx1-0324 ∷ []) (Bx1-0324 ∷ CS12 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS02 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-1324 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0324⟩ c4) ▸
       at 1 2 (Bx0-1324 ∷ CS02 ∷ []) (lem-auto-CS01-∣-BOX⟨0·2314⟩-at1221 c4) ▸
       at 0 2 (Bx1-0324 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1324⟩ c4) ▸
       at 1 2 (CS12 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS02 ∷ []) (CS12 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;2;3) | BOX(1;0324): 3 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨1·0324⟩ : Complete 4 → ⟪ (Sb0-1-2-3 ∷ Bx1-0324 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0324 ∷ Sb0-1-2-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨1·0324⟩ c4 = run b0
  where
  b0 : Chain (Sb0-1-2-3 ∷ Bx1-0324 ∷ []) (Bx1-0324 ∷ Sb0-1-2-3 ∷ [])
  b0 = at 0 1 (CS12 ∷ []) (refl) ▸
       at 0 2 (Bx1-0324 ∷ CS12 ∷ []) (lem-auto-CS01-∣-BOX⟨0·2314⟩-at011220 c4) ▸
       at 1 1 (Sb0-1-2-3 ∷ []) (refl) ▸ done


-- beta-T @0113243042: 8 steps
lem-beta-T-at0113243042 : Complete 4 → ⟪ (Bx1-3402 ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ CCZ012 ∷ Toff134 ∷ CCZ012 ∷ []) ⟫ʷ
lem-beta-T-at0113243042 c4 = run b0
  where
  b0 : Chain (Bx1-3402 ∷ []) (Toff134 ∷ CCZ012 ∷ Toff134 ∷ CCZ012 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-3412 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·3402⟩ c4) ▸
       at 1 1 (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ []) (lem-beta-T-at13243142 c4) ▸
       at 0 2 (Toff134 ∷ Sw01 ∷ []) (lem-nat-0-TOFF034 c4) ▸
       at 1 2 (CCZ012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff134 ∷ Sw01 ∷ []) (lem-nat-0-TOFF034 c4) ▸
       at 3 2 (CCZ012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | BOX(1;0342): 35 steps
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0342⟩ : Complete 4 → ⟪ (Bx0-1234 ∷ Bx1-0342 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0342 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0342⟩ c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (run b4))))
  where
  b0 : Chain (Bx0-1234 ∷ Bx1-0342 ∷ []) (Toff134 ∷ Toff134 ∷ Bx0-3412 ∷ Toff134 ∷ CCZ012 ∷ Toff134 ∷ CCZ012 ∷ [])
  b0 = at 1 1 (Bx1-3042 ∷ []) (lem-sym12-at0110233442 c4) ▸
       at 1 1 (Bx1-3402 ∷ []) (lem-sym23-at0113203442 c4) ▸
       at 1 1 (Toff134 ∷ CCZ012 ∷ Toff134 ∷ CCZ012 ∷ []) (lem-beta-T-at0113243042 c4) ▸
       at 0 0 (Toff134 ∷ Toff134 ∷ []) (lw0 c4 [] (Toff134 ∷ Toff134 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Bx0-1324 ∷ []) (lem-sym23 c4) ▸
       at 2 1 (Bx0-1342 ∷ []) (lem-sym34-at2332 c4) ▸
       at 2 1 (Bx0-3142 ∷ []) (lem-sym12-at233442 c4) ▸
       at 2 1 (Bx0-3412 ∷ []) (lem-sym23-at13213442 c4) ▸ done

  b1 : Chain (Toff134 ∷ Toff134 ∷ Bx0-3412 ∷ Toff134 ∷ CCZ012 ∷ Toff134 ∷ CCZ012 ∷ []) (Toff134 ∷ CCZ234 ∷ CCZ012 ∷ Toff134 ∷ Toff134 ∷ Bx0-1234 ∷ Toff134 ∷ CCZ012 ∷ [])
  b1 = at 1 3 (Bx0-3412 ∷ CCZ234 ∷ []) (lem-T312-beta-at13243142 c4) ▸
       at 1 1 (Bx0-3142 ∷ []) (lem-sym23-at13243142 c4) ▸
       at 1 1 (Bx0-3124 ∷ []) (lem-sym34-at13213442 c4) ▸
       at 1 1 (Bx0-1324 ∷ []) (lem-sym12-at132132 c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym23-at2332 c4) ▸
       at 1 2 (CCZ234 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ342 c4) ▸
       at 2 2 (CCZ012 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ102 c4) ▸
       at 3 0 (Toff134 ∷ Toff134 ∷ []) (lw0 c4 [] (Toff134 ∷ Toff134 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Toff134 ∷ CCZ234 ∷ CCZ012 ∷ Toff134 ∷ Toff134 ∷ Bx0-1234 ∷ Toff134 ∷ CCZ012 ∷ []) (Toff134 ∷ CCZ234 ∷ CCZ012 ∷ Toff134 ∷ Bx0-1324 ∷ CCZ234 ∷ CCZ012 ∷ [])
  b2 = at 5 1 (Bx0-1324 ∷ []) (lem-sym23 c4) ▸
       at 5 1 (Bx0-1342 ∷ []) (lem-sym34-at2332 c4) ▸
       at 5 1 (Bx0-3142 ∷ []) (lem-sym12-at233442 c4) ▸
       at 5 1 (Bx0-3412 ∷ []) (lem-sym23-at13213442 c4) ▸
       at 4 3 (Bx0-3412 ∷ CCZ234 ∷ []) (lem-T312-beta-at13243142 c4) ▸
       at 4 1 (Bx0-3142 ∷ []) (lem-sym23-at13243142 c4) ▸
       at 4 1 (Bx0-3124 ∷ []) (lem-sym34-at13213442 c4) ▸
       at 4 1 (Bx0-1324 ∷ []) (lem-sym12-at132132 c4) ▸ done

  b3 : Chain (Toff134 ∷ CCZ234 ∷ CCZ012 ∷ Toff134 ∷ Bx0-1324 ∷ CCZ234 ∷ CCZ012 ∷ []) (Toff134 ∷ CCZ012 ∷ Toff134 ∷ CCZ012 ∷ Bx0-1234 ∷ [])
  b3 = at 4 1 (Bx0-1234 ∷ []) (lem-sym23-at2332 c4) ▸
       at 4 2 (CCZ234 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ342 c4) ▸
       at 5 2 (CCZ012 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ102 c4) ▸
       at 0 2 (CCZ234 ∷ Toff134 ∷ []) (lw0 c4 (Toff134 ∷ CCZ234 ∷ []) (CCZ234 ∷ Toff134 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ234 ∷ Toff134 ∷ []) (lw0 c4 (Toff134 ∷ CCZ234 ∷ []) (CCZ234 ∷ Toff134 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ234 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-CCZ342-at0110 c4) ▸
       at 1 2 (CCZ234 ∷ Toff134 ∷ []) (lw0 c4 (Toff134 ∷ CCZ234 ∷ []) (CCZ234 ∷ Toff134 ∷ []) tt tt Eq.refl) ▸
       at 0 2 [] (lw0 c4 (CCZ234 ∷ CCZ234 ∷ []) [] tt tt Eq.refl) ▸ done

  b4 : Chain (Toff134 ∷ CCZ012 ∷ Toff134 ∷ CCZ012 ∷ Bx0-1234 ∷ []) (Bx1-0342 ∷ Bx0-1234 ∷ [])
  b4 = at 0 4 (Bx1-3402 ∷ []) (sym (lem-beta-T-at0113243042 c4)) ▸
       at 0 1 (Bx1-3042 ∷ []) (lem-sym23-at0113243042 c4) ▸
       at 0 1 (Bx1-0342 ∷ []) (lem-sym12-at0113203442 c4) ▸ done


-- auto CCZ012 | TOFF310 SBOXd(2;4;3;0): 2 steps
lem-auto-CCZ012-∣-TOFF310-SBOXd⟨2·4·3·0⟩ : Complete 4 → ⟪ (CCZ012 ∷ Toff301 ∷ Sb⁻2-4-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ Sb⁻2-4-3-0 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-TOFF310-SBOXd⟨2·4·3·0⟩ c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Toff301 ∷ Sb⁻2-4-3-0 ∷ []) (Toff301 ∷ Sb⁻2-4-3-0 ∷ CCZ012 ∷ [])
  b0 = at 0 2 (Toff301 ∷ CCZ012 ∷ []) (lw4 c4 (CCZ012 ∷ Toff301 ∷ []) (Toff301 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻2-4-3-0 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CS • CS • CS)) ▸ done


-- auto SBOXd(0;1;2;3) | BOX(1;0324) @2332: 7 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨1·0324⟩-at2332 : Complete 4 → ⟪ (Sb⁻0-1-3-2 ∷ Bx1-0234 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0234 ∷ Sb⁻0-1-3-2 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨1·0324⟩-at2332 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-3-2 ∷ Bx1-0234 ∷ []) (Bx1-0234 ∷ Sb⁻0-1-3-2 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-2-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·3·2⟩ c4) ▸
       at 2 2 (Bx1-0324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·0234⟩ c4) ▸
       at 1 2 (Bx1-0324 ∷ Sb⁻0-1-2-3 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨1·0324⟩ c4) ▸
       at 0 2 (Bx1-0234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·0324⟩ c4) ▸
       at 1 2 (Sb⁻0-1-3-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·2·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;2;3) | BOX(1;0324) @243243: 7 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨1·0324⟩-at243243 : Complete 4 → ⟪ (Sb⁻0-1-4-2 ∷ Bx1-0243 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0243 ∷ Sb⁻0-1-4-2 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨1·0324⟩-at243243 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-4-2 ∷ Bx1-0243 ∷ []) (Bx1-0243 ∷ Sb⁻0-1-4-2 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-3-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·4·2⟩ c4) ▸
       at 2 2 (Bx1-0234 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·0243⟩ c4) ▸
       at 1 2 (Bx1-0234 ∷ Sb⁻0-1-3-2 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨1·0324⟩-at2332 c4) ▸
       at 0 2 (Bx1-0243 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·0234⟩ c4) ▸
       at 1 2 (Sb⁻0-1-4-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·3·2⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;2;3) | BOX(1;0324) @2442: 7 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨1·0324⟩-at2442 : Complete 4 → ⟪ (Sb⁻0-1-4-3 ∷ Bx1-0342 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0342 ∷ Sb⁻0-1-4-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨1·0324⟩-at2442 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-4-3 ∷ Bx1-0342 ∷ []) (Bx1-0342 ∷ Sb⁻0-1-4-3 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-4-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·4·3⟩ c4) ▸
       at 2 2 (Bx1-0243 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·0342⟩ c4) ▸
       at 1 2 (Bx1-0243 ∷ Sb⁻0-1-4-2 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨1·0324⟩-at243243 c4) ▸
       at 0 2 (Bx1-0342 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·0243⟩ c4) ▸
       at 1 2 (Sb⁻0-1-4-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·4·2⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym34 @12243143: 5 steps
lem-sym34-at12243143 : Complete 4 → ⟪ (Bx0-2413 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ []) ⟫ʷ
lem-sym34-at12243143 c4 = run b0
  where
  b0 : Chain (Bx0-2413 ∷ []) (Bx0-2431 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2413⟩ c4) ▸
       at 1 1 (Bx0-1432 ∷ []) (lem-sym34-at243243 c4) ▸
       at 0 2 (Bx0-2431 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1432⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym34 @13243142: 5 steps
lem-sym34-at13243142 : Complete 4 → ⟪ (Bx0-3412 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3421 ∷ []) ⟫ʷ
lem-sym34-at13243142 c4 = run b0
  where
  b0 : Chain (Bx0-3412 ∷ []) (Bx0-3421 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-2413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3412⟩ c4) ▸
       at 1 1 (Bx0-2431 ∷ []) (lem-sym34-at12243143 c4) ▸
       at 0 2 (Bx0-3421 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·2431⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym34 @0113243042: 5 steps
lem-sym34-at0113243042 : Complete 4 → ⟪ (Bx1-3402 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3420 ∷ []) ⟫ʷ
lem-sym34-at0113243042 c4 = run b0
  where
  b0 : Chain (Bx1-3402 ∷ []) (Bx1-3420 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-3412 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·3402⟩ c4) ▸
       at 1 1 (Bx0-3421 ∷ []) (lem-sym34-at13243142 c4) ▸
       at 0 2 (Bx1-3420 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·3421⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym23 @0113243240: 5 steps
lem-sym23-at0113243240 : Complete 4 → ⟪ (Bx1-3420 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3240 ∷ []) ⟫ʷ
lem-sym23-at0113243240 c4 = run b0
  where
  b0 : Chain (Bx1-3420 ∷ []) (Bx1-3240 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-3421 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·3420⟩ c4) ▸
       at 1 1 (Bx0-3241 ∷ []) (lem-sym23-at13243241 c4) ▸
       at 0 2 (Bx1-3240 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·3241⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- T312-beta @12213443: 8 steps
lem-T312-beta-at12213443 : Complete 4 → ⟪ (Toff412 ∷ Bx0-2143 ∷ Toff412 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2143 ∷ CCZ123 ∷ []) ⟫ʷ
lem-T312-beta-at12213443 c4 = run b0
  where
  b0 : Chain (Toff412 ∷ Bx0-2143 ∷ Toff412 ∷ []) (Bx0-2143 ∷ CCZ123 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff412 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff412 ∷ []) (Toff412 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-1243 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2143⟩ c4) ▸
       at 3 2 (Toff412 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff412 ∷ []) (Toff412 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Bx0-1243 ∷ CCZ123 ∷ []) (lem-T312-beta-at3443 c4) ▸
       at 0 2 (Bx0-2143 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1243⟩ c4) ▸
       at 1 2 (CCZ123 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- T312-beta @13213442: 8 steps
lem-T312-beta-at13213442 : Complete 4 → ⟪ (Toff413 ∷ Bx0-3142 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3142 ∷ CCZ123 ∷ []) ⟫ʷ
lem-T312-beta-at13213442 c4 = run b0
  where
  b0 : Chain (Toff413 ∷ Bx0-3142 ∷ Toff413 ∷ []) (Bx0-3142 ∷ CCZ123 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff412 ∷ Sw23 ∷ []) (lem-nat-2-TOFF413 c4) ▸
       at 2 2 (Bx0-2143 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3142⟩ c4) ▸
       at 3 2 (Toff412 ∷ Sw23 ∷ []) (lem-nat-2-TOFF413 c4) ▸
       at 1 3 (Bx0-2143 ∷ CCZ123 ∷ []) (lem-T312-beta-at12213443 c4) ▸
       at 0 2 (Bx0-3142 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·2143⟩ c4) ▸
       at 1 2 (CCZ123 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- T312-beta @133441: 8 steps
lem-T312-beta-at133441 : Complete 4 → ⟪ (Toff423 ∷ Bx0-3241 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3241 ∷ CCZ123 ∷ []) ⟫ʷ
lem-T312-beta-at133441 c4 = run b0
  where
  b0 : Chain (Toff423 ∷ Bx0-3241 ∷ Toff423 ∷ []) (Bx0-3241 ∷ CCZ123 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff413 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff423 ∷ []) (Toff413 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-3142 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·3241⟩ c4) ▸
       at 3 2 (Toff413 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff423 ∷ []) (Toff413 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Bx0-3142 ∷ CCZ123 ∷ []) (lem-T312-beta-at13213442 c4) ▸
       at 0 2 (Bx0-3241 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·3142⟩ c4) ▸
       at 1 2 (CCZ123 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- T312-beta @01133440: 8 steps
lem-T312-beta-at01133440 : Complete 4 → ⟪ (Toff423 ∷ Bx1-3240 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3240 ∷ CCZ023 ∷ []) ⟫ʷ
lem-T312-beta-at01133440 c4 = run b0
  where
  b0 : Chain (Toff423 ∷ Bx1-3240 ∷ Toff423 ∷ []) (Bx1-3240 ∷ CCZ023 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff423 ∷ Sw01 ∷ []) (c₂ (Swap) (Toffᵗ)) ▸
       at 2 2 (Bx0-3241 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·3240⟩ c4) ▸
       at 3 2 (Toff423 ∷ Sw01 ∷ []) (c₂ (Swap) (Toffᵗ)) ▸
       at 1 3 (Bx0-3241 ∷ CCZ123 ∷ []) (lem-T312-beta-at133441 c4) ▸
       at 0 2 (Bx1-3240 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·3241⟩ c4) ▸
       at 1 2 (CCZ023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ123 ∷ []) (CCZ023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym23 @01133440: 5 steps
lem-sym23-at01133440 : Complete 4 → ⟪ (Bx1-3240 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3420 ∷ []) ⟫ʷ
lem-sym23-at01133440 c4 = run b0
  where
  b0 : Chain (Bx1-3240 ∷ []) (Bx1-3420 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-3241 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·3240⟩ c4) ▸
       at 1 1 (Bx0-3421 ∷ []) (lem-sym23-at133441 c4) ▸
       at 0 2 (Bx1-3420 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·3421⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym34 @13243241: 5 steps
lem-sym34-at13243241 : Complete 4 → ⟪ (Bx0-3421 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3412 ∷ []) ⟫ʷ
lem-sym34-at13243241 c4 = run b0
  where
  b0 : Chain (Bx0-3421 ∷ []) (Bx0-3412 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-3412 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·3421⟩ c4) ▸
       at 1 1 (Bx0-3421 ∷ []) (lem-sym34-at13243142 c4) ▸
       at 0 2 (Bx0-3412 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·3421⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym34 @0113243240: 5 steps
lem-sym34-at0113243240 : Complete 4 → ⟪ (Bx1-3420 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3402 ∷ []) ⟫ʷ
lem-sym34-at0113243240 c4 = run b0
  where
  b0 : Chain (Bx1-3420 ∷ []) (Bx1-3402 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-3421 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·3420⟩ c4) ▸
       at 1 1 (Bx0-3412 ∷ []) (lem-sym34-at13243241 c4) ▸
       at 0 2 (Bx1-3402 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·3412⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;2;3) | BOX(1;0324) @2332: 7 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨1·0324⟩-at2332 : Complete 4 → ⟪ (Sb0-1-3-2 ∷ Bx1-0234 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0234 ∷ Sb0-1-3-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨1·0324⟩-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-3-2 ∷ Bx1-0234 ∷ []) (Bx1-0234 ∷ Sb0-1-3-2 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-2-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·3·2⟩ c4) ▸
       at 2 2 (Bx1-0324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·0234⟩ c4) ▸
       at 1 2 (Bx1-0324 ∷ Sb0-1-2-3 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨1·0324⟩ c4) ▸
       at 0 2 (Bx1-0234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·0324⟩ c4) ▸
       at 1 2 (Sb0-1-3-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·2·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;2;3) | BOX(1;0324) @243243: 7 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨1·0324⟩-at243243 : Complete 4 → ⟪ (Sb0-1-4-2 ∷ Bx1-0243 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0243 ∷ Sb0-1-4-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨1·0324⟩-at243243 c4 = run b0
  where
  b0 : Chain (Sb0-1-4-2 ∷ Bx1-0243 ∷ []) (Bx1-0243 ∷ Sb0-1-4-2 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-3-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·4·2⟩ c4) ▸
       at 2 2 (Bx1-0234 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·0243⟩ c4) ▸
       at 1 2 (Bx1-0234 ∷ Sb0-1-3-2 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨1·0324⟩-at2332 c4) ▸
       at 0 2 (Bx1-0243 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·0234⟩ c4) ▸
       at 1 2 (Sb0-1-4-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·3·2⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;2;3) | BOX(1;0324) @2442: 7 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨1·0324⟩-at2442 : Complete 4 → ⟪ (Sb0-1-4-3 ∷ Bx1-0342 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0342 ∷ Sb0-1-4-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨1·0324⟩-at2442 c4 = run b0
  where
  b0 : Chain (Sb0-1-4-3 ∷ Bx1-0342 ∷ []) (Bx1-0342 ∷ Sb0-1-4-3 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-4-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·4·3⟩ c4) ▸
       at 2 2 (Bx1-0243 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·0342⟩ c4) ▸
       at 1 2 (Bx1-0243 ∷ Sb0-1-4-2 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨1·0324⟩-at243243 c4) ▸
       at 0 2 (Bx1-0342 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·0243⟩ c4) ▸
       at 1 2 (Sb0-1-4-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·4·2⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | TOFF310 SBOXd(2;4;3;0) @3443: 9 steps
lem-auto-CCZ012-∣-TOFF310-SBOXd⟨2·4·3·0⟩-at3443 : Complete 4 → ⟪ (CCZ012 ∷ Toff401 ∷ Sb⁻2-3-4-0 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ Sb⁻2-3-4-0 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-TOFF310-SBOXd⟨2·4·3·0⟩-at3443 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ012 ∷ Toff401 ∷ Sb⁻2-3-4-0 ∷ []) (Toff401 ∷ Sb⁻2-3-4-0 ∷ CCZ012 ∷ Sw34 ∷ Sw34 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 2 2 (Toff301 ∷ Sw34 ∷ []) (lem-nat-3-TOFF401 c4) ▸
       at 3 2 (Sb⁻2-4-3-0 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨2·3·4·0⟩ c4) ▸
       at 1 3 (Toff301 ∷ Sb⁻2-4-3-0 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-TOFF310-SBOXd⟨2·4·3·0⟩ c4) ▸
       at 0 2 (Toff401 ∷ Sw34 ∷ []) (lem-nat-3-TOFF301 c4) ▸
       at 1 2 (Sb⁻2-3-4-0 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨2·4·3·0⟩ c4) ▸
       at 2 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸ done

  b1 : Chain (Toff401 ∷ Sb⁻2-3-4-0 ∷ CCZ012 ∷ Sw34 ∷ Sw34 ∷ []) (Toff401 ∷ Sb⁻2-3-4-0 ∷ CCZ012 ∷ [])
  b1 = at 3 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | TOFF310 SBOXd(2;4;3;0) @01103443: 9 steps
lem-auto-CCZ012-∣-TOFF310-SBOXd⟨2·4·3·0⟩-at01103443 : Complete 4 → ⟪ (CCZ012 ∷ Toff401 ∷ Sb⁻2-3-4-1 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ Sb⁻2-3-4-1 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-TOFF310-SBOXd⟨2·4·3·0⟩-at01103443 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ012 ∷ Toff401 ∷ Sb⁻2-3-4-1 ∷ []) (Toff401 ∷ Sb⁻2-3-4-1 ∷ CCZ012 ∷ Sw01 ∷ Sw01 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff401 ∷ Sw01 ∷ []) (lem-nat-0-TOFF401 c4) ▸
       at 3 2 (Sb⁻2-3-4-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨2·3·4·1⟩ c4) ▸
       at 1 3 (Toff401 ∷ Sb⁻2-3-4-0 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-TOFF310-SBOXd⟨2·4·3·0⟩-at3443 c4) ▸
       at 0 2 (Toff401 ∷ Sw01 ∷ []) (lem-nat-0-TOFF401 c4) ▸
       at 1 2 (Sb⁻2-3-4-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨2·3·4·0⟩ c4) ▸
       at 2 2 (CCZ012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Toff401 ∷ Sb⁻2-3-4-1 ∷ CCZ012 ∷ Sw01 ∷ Sw01 ∷ []) (Toff401 ∷ Sb⁻2-3-4-1 ∷ CCZ012 ∷ [])
  b1 = at 3 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | TOFF310 SBOXd(2;4;3;0) @0210213443: 9 steps
lem-auto-CCZ012-∣-TOFF310-SBOXd⟨2·4·3·0⟩-at0210213443 : Complete 4 → ⟪ (CCZ012 ∷ Toff402 ∷ Sb⁻1-3-4-2 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ Sb⁻1-3-4-2 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-TOFF310-SBOXd⟨2·4·3·0⟩-at0210213443 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ012 ∷ Toff402 ∷ Sb⁻1-3-4-2 ∷ []) (Toff402 ∷ Sb⁻1-3-4-2 ∷ CCZ012 ∷ Sw12 ∷ Sw12 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff401 ∷ Sw12 ∷ []) (lem-nat-1-TOFF402 c4) ▸
       at 3 2 (Sb⁻2-3-4-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·3·4·2⟩ c4) ▸
       at 1 3 (Toff401 ∷ Sb⁻2-3-4-1 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-TOFF310-SBOXd⟨2·4·3·0⟩-at01103443 c4) ▸
       at 0 2 (Toff402 ∷ Sw12 ∷ []) (lem-nat-1-TOFF401 c4) ▸
       at 1 2 (Sb⁻1-3-4-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·3·4·1⟩ c4) ▸
       at 2 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Toff402 ∷ Sb⁻1-3-4-2 ∷ CCZ012 ∷ Sw12 ∷ Sw12 ∷ []) (Toff402 ∷ Sb⁻1-3-4-2 ∷ CCZ012 ∷ [])
  b1 = at 3 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | TOFF310 SBOXd(2;4;3;0) @0310213442: 9 steps
lem-auto-CCZ012-∣-TOFF310-SBOXd⟨2·4·3·0⟩-at0310213442 : Complete 4 → ⟪ (CCZ013 ∷ Toff403 ∷ Sb⁻1-2-4-3 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ Sb⁻1-2-4-3 ∷ CCZ013 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-TOFF310-SBOXd⟨2·4·3·0⟩-at0310213442 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ013 ∷ Toff403 ∷ Sb⁻1-2-4-3 ∷ []) (Toff403 ∷ Sb⁻1-2-4-3 ∷ CCZ013 ∷ Sw23 ∷ Sw23 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 2 2 (Toff402 ∷ Sw23 ∷ []) (lem-nat-2-TOFF403 c4) ▸
       at 3 2 (Sb⁻1-3-4-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·2·4·3⟩ c4) ▸
       at 1 3 (Toff402 ∷ Sb⁻1-3-4-2 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-TOFF310-SBOXd⟨2·4·3·0⟩-at0210213443 c4) ▸
       at 0 2 (Toff403 ∷ Sw23 ∷ []) (lem-nat-2-TOFF402 c4) ▸
       at 1 2 (Sb⁻1-2-4-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·3·4·2⟩ c4) ▸
       at 2 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸ done

  b1 : Chain (Toff403 ∷ Sb⁻1-2-4-3 ∷ CCZ013 ∷ Sw23 ∷ Sw23 ∷ []) (Toff403 ∷ Sb⁻1-2-4-3 ∷ CCZ013 ∷ [])
  b1 = at 3 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | TOFF310 SBOXd(2;4;3;0) @03203442: 9 steps
lem-auto-CCZ012-∣-TOFF310-SBOXd⟨2·4·3·0⟩-at03203442 : Complete 4 → ⟪ (CCZ013 ∷ Toff413 ∷ Sb⁻0-2-4-3 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ Sb⁻0-2-4-3 ∷ CCZ013 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-TOFF310-SBOXd⟨2·4·3·0⟩-at03203442 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ013 ∷ Toff413 ∷ Sb⁻0-2-4-3 ∷ []) (Toff413 ∷ Sb⁻0-2-4-3 ∷ CCZ013 ∷ Sw01 ∷ Sw01 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff403 ∷ Sw01 ∷ []) (lem-nat-0-TOFF413 c4) ▸
       at 3 2 (Sb⁻1-2-4-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨0·2·4·3⟩ c4) ▸
       at 1 3 (Toff403 ∷ Sb⁻1-2-4-3 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-TOFF310-SBOXd⟨2·4·3·0⟩-at0310213442 c4) ▸
       at 0 2 (Toff413 ∷ Sw01 ∷ []) (lem-nat-0-TOFF403 c4) ▸
       at 1 2 (Sb⁻0-2-4-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·2·4·3⟩ c4) ▸
       at 2 2 (CCZ013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Toff413 ∷ Sb⁻0-2-4-3 ∷ CCZ013 ∷ Sw01 ∷ Sw01 ∷ []) (Toff413 ∷ Sb⁻0-2-4-3 ∷ CCZ013 ∷ [])
  b1 = at 3 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | TOFF310 SBOXd(2;4;3;0) @0312203441: 9 steps
lem-auto-CCZ012-∣-TOFF310-SBOXd⟨2·4·3·0⟩-at0312203441 : Complete 4 → ⟪ (CCZ023 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ Sb⁻0-1-4-3 ∷ CCZ023 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-TOFF310-SBOXd⟨2·4·3·0⟩-at0312203441 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ023 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (Toff423 ∷ Sb⁻0-1-4-3 ∷ CCZ023 ∷ Sw12 ∷ Sw12 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 2 2 (Toff413 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff423 ∷ []) (Toff413 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Sb⁻0-2-4-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨0·1·4·3⟩ c4) ▸
       at 1 3 (Toff413 ∷ Sb⁻0-2-4-3 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-TOFF310-SBOXd⟨2·4·3·0⟩-at03203442 c4) ▸
       at 0 2 (Toff423 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff413 ∷ []) (Toff423 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-4-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨0·2·4·3⟩ c4) ▸
       at 2 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸ done

  b1 : Chain (Toff423 ∷ Sb⁻0-1-4-3 ∷ CCZ023 ∷ Sw12 ∷ Sw12 ∷ []) (Toff423 ∷ Sb⁻0-1-4-3 ∷ CCZ023 ∷ [])
  b1 = at 3 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | BOX(1;0342): 35 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨1·0342⟩ : Complete 4 → ⟪ (Sb0-1-23-4 ∷ Bx1-0342 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0342 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨1·0342⟩ c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (run b4))))
  where
  b0 : Chain (Sb0-1-23-4 ∷ Bx1-0342 ∷ []) (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Bx1-3420 ∷ Toff423 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 4 2 (Bx1-0342 ∷ Sb⁻0-1-4-3 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨1·0324⟩-at2442 c4) ▸
       at 5 0 (Toff423 ∷ Toff423 ∷ []) (lw0 c4 [] (Toff423 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Toff423 ∷ []) (lw0 c4 (Toff423 ∷ []) (Toff423 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Toff423 ∷ []) (lw0 c4 (Toff423 ∷ []) (Toff423 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Bx1-3042 ∷ []) (lem-sym12-at0110233442 c4) ▸
       at 4 1 (Bx1-3402 ∷ []) (lem-sym23-at0113203442 c4) ▸
       at 4 1 (Bx1-3420 ∷ []) (lem-sym34-at0113243042 c4) ▸ done

  b1 : Chain (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Bx1-3420 ∷ Toff423 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (Bx0-1234 ∷ Toff423 ∷ Bx1-0342 ∷ Toff423 ∷ Toff423 ∷ Sb0-1-4-3 ∷ CCZ023 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ [])
  b1 = at 4 1 (Bx1-3240 ∷ []) (lem-sym23-at0113243240 c4) ▸
       at 3 3 (Bx1-3240 ∷ CCZ023 ∷ []) (lem-T312-beta-at01133440 c4) ▸
       at 3 1 (Bx1-3420 ∷ []) (lem-sym23-at01133440 c4) ▸
       at 3 1 (Bx1-3402 ∷ []) (lem-sym34-at0113243240 c4) ▸
       at 3 1 (Bx1-3042 ∷ []) (lem-sym23-at0113243042 c4) ▸
       at 3 1 (Bx1-0342 ∷ []) (lem-sym12-at0113203442 c4) ▸
       at 2 2 (Bx1-0342 ∷ Sb0-1-4-3 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨1·0324⟩-at2442 c4) ▸
       at 3 0 (Toff423 ∷ Toff423 ∷ []) (lw0 c4 [] (Toff423 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Bx0-1234 ∷ Toff423 ∷ Bx1-0342 ∷ Toff423 ∷ Toff423 ∷ Sb0-1-4-3 ∷ CCZ023 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (Bx0-1234 ∷ Bx1-3420 ∷ CCZ023 ∷ Toff423 ∷ Sb0-1-4-3 ∷ CCZ023 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ [])
  b2 = at 1 1 (Toff423 ∷ []) (lw0 c4 (Toff423 ∷ []) (Toff423 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Toff423 ∷ []) (lw0 c4 (Toff423 ∷ []) (Toff423 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Bx1-3042 ∷ []) (lem-sym12-at0110233442 c4) ▸
       at 2 1 (Bx1-3402 ∷ []) (lem-sym23-at0113203442 c4) ▸
       at 2 1 (Bx1-3420 ∷ []) (lem-sym34-at0113243042 c4) ▸
       at 2 1 (Bx1-3240 ∷ []) (lem-sym23-at0113243240 c4) ▸
       at 1 3 (Bx1-3240 ∷ CCZ023 ∷ []) (lem-T312-beta-at01133440 c4) ▸
       at 1 1 (Bx1-3420 ∷ []) (lem-sym23-at01133440 c4) ▸ done

  b3 : Chain (Bx0-1234 ∷ Bx1-3420 ∷ CCZ023 ∷ Toff423 ∷ Sb0-1-4-3 ∷ CCZ023 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (Bx1-0342 ∷ Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ CCZ023 ∷ Sb⁻0-1-4-3 ∷ CCZ023 ∷ [])
  b3 = at 1 1 (Bx1-3402 ∷ []) (lem-sym34-at0113243240 c4) ▸
       at 1 1 (Bx1-3042 ∷ []) (lem-sym23-at0113243042 c4) ▸
       at 1 1 (Bx1-0342 ∷ []) (lem-sym12-at0113203442 c4) ▸
       at 0 2 (Bx1-0342 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0342⟩ c4) ▸
       at 5 3 (Toff423 ∷ Sb⁻0-1-4-3 ∷ CCZ023 ∷ []) (lem-auto-CCZ012-∣-TOFF310-SBOXd⟨2·4·3·0⟩-at0312203441 c4) ▸
       at 2 2 (Toff423 ∷ CCZ023 ∷ []) (pw1 c4 (CCZ023 ∷ Toff423 ∷ []) (Toff423 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Sb0-1-4-3 ∷ CCZ023 ∷ []) (lem-comm-CCZ023-SBOX⟨0·1·4·3⟩ c4) ▸
       at 4 2 (Toff423 ∷ CCZ023 ∷ []) (pw1 c4 (CCZ023 ∷ Toff423 ∷ []) (Toff423 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸ done

  b4 : Chain (Bx1-0342 ∷ Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ CCZ023 ∷ Sb⁻0-1-4-3 ∷ CCZ023 ∷ []) (Bx1-0342 ∷ Sb0-1-23-4 ∷ [])
  b4 = at 5 2 (Sb⁻0-1-4-3 ∷ CCZ023 ∷ []) (lem-comm-CCZ023-SBOXd⟨0·1·4·3⟩ c4) ▸
       at 6 2 [] (lw4 c4 (CCZ023 ∷ CCZ023 ∷ []) [] tt tt Eq.refl) ▸
       at 1 5 (Sb0-1-23-4 ∷ []) (refl) ▸ done


-- CX23-beta @12243143: 8 steps
lem-CX23-beta-at12243143 : Complete 4 → ⟪ (CX41 ∷ Bx0-2413 ∷ CX41 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2413 ∷ CCZ234 ∷ []) ⟫ʷ
lem-CX23-beta-at12243143 c4 = run b0
  where
  b0 : Chain (CX41 ∷ Bx0-2413 ∷ CX41 ∷ []) (Bx0-2413 ∷ CCZ234 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CX42 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CX41 ∷ []) (CX42 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-1423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2413⟩ c4) ▸
       at 3 2 (CX42 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CX41 ∷ []) (CX42 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Bx0-1423 ∷ CCZ134 ∷ []) (lem-CX23-beta-at243243 c4) ▸
       at 0 2 (Bx0-2413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1423⟩ c4) ▸
       at 1 2 (CCZ234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ134 ∷ []) (CCZ234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- CX23-beta @13243142: 8 steps
lem-CX23-beta-at13243142 : Complete 4 → ⟪ (CX41 ∷ Bx0-3412 ∷ CX41 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3412 ∷ CCZ234 ∷ []) ⟫ʷ
lem-CX23-beta-at13243142 c4 = run b0
  where
  b0 : Chain (CX41 ∷ Bx0-3412 ∷ CX41 ∷ []) (Bx0-3412 ∷ CCZ234 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CX41 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CX41 ∷ []) (CX41 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-2413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3412⟩ c4) ▸
       at 3 2 (CX41 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CX41 ∷ []) (CX41 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Bx0-2413 ∷ CCZ234 ∷ []) (lem-CX23-beta-at12243143 c4) ▸
       at 0 2 (Bx0-3412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·2413⟩ c4) ▸
       at 1 2 (CCZ234 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CCZ341: 36 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ341 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ341 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (run b4))))
  where
  b0 : Chain (Sb0-1-23-4 ∷ CCZ134 ∷ []) (CS13 ∷ Bx0-1324 ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ Sb⁻0-1-4-2 ∷ CS34 ∷ [])
  b0 = at 1 1 (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ []) (lw0 c4 (CCZ134 ∷ []) (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (CS13 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS12-at2332 c4) ▸
       at 1 1 (Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ []) (refl) ▸
       at 5 1 (CS14⁻ ∷ []) (refl) ▸
       at 5 4 (CX41 ∷ CS13⁻ ∷ CX41 ∷ CS14⁻ ∷ []) (lw0 c4 (CS14⁻ ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ []) (CX41 ∷ CS13⁻ ∷ CX41 ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 8 1 (Sb⁻0-1-4-2 ∷ []) (refl) ▸
       at 3 1 (CS14 ∷ []) (refl) ▸ done

  b1 : Chain (CS13 ∷ Bx0-1324 ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ Sb⁻0-1-4-2 ∷ CS34 ∷ []) (CS13 ∷ CX41 ∷ Bx0-3142 ∷ CCZ234 ∷ CS13⁻ ∷ CX41 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS34 ∷ [])
  b1 = at 2 6 (CX41 ∷ CS13⁻ ∷ CX41 ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ []) (lw0 c4 (Toff423 ∷ CS14 ∷ Toff423 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ []) (CX41 ∷ CS13⁻ ∷ CX41 ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Sb0-1-4-2 ∷ []) (refl) ▸
       at 1 0 (CX41 ∷ CX41 ∷ []) (lw0 c4 [] (CX41 ∷ CX41 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Bx0-3124 ∷ []) (lem-sym12-at2332 c4) ▸
       at 3 1 (Bx0-3142 ∷ []) (lem-sym34-at132132 c4) ▸
       at 3 1 (Bx0-3412 ∷ []) (lem-sym23-at13213442 c4) ▸
       at 2 3 (Bx0-3412 ∷ CCZ234 ∷ []) (lem-CX23-beta-at13243142 c4) ▸
       at 2 1 (Bx0-3142 ∷ []) (lem-sym23-at13243142 c4) ▸ done

  b2 : Chain (CS13 ∷ CX41 ∷ Bx0-3142 ∷ CCZ234 ∷ CS13⁻ ∷ CX41 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS34 ∷ []) (CS13 ∷ CX41 ∷ CCZ234 ∷ CS13⁻ ∷ CX41 ∷ CX41 ∷ Bx0-3412 ∷ CX41 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS34 ∷ [])
  b2 = at 2 1 (Bx0-3124 ∷ []) (lem-sym34-at13213442 c4) ▸
       at 2 1 (Bx0-1324 ∷ []) (lem-sym12-at132132 c4) ▸
       at 2 2 (CCZ234 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at2332 c4) ▸
       at 3 2 (CS13⁻ ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd12-at2332 c4) ▸
       at 4 0 (CX41 ∷ CX41 ∷ []) (lw0 c4 [] (CX41 ∷ CX41 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Bx0-3124 ∷ []) (lem-sym12-at2332 c4) ▸
       at 6 1 (Bx0-3142 ∷ []) (lem-sym34-at132132 c4) ▸
       at 6 1 (Bx0-3412 ∷ []) (lem-sym23-at13213442 c4) ▸ done

  b3 : Chain (CS13 ∷ CX41 ∷ CCZ234 ∷ CS13⁻ ∷ CX41 ∷ CX41 ∷ Bx0-3412 ∷ CX41 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS34 ∷ []) (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS34 ∷ [])
  b3 = at 5 3 (Bx0-3412 ∷ CCZ234 ∷ []) (lem-CX23-beta-at13243142 c4) ▸
       at 5 1 (Bx0-3142 ∷ []) (lem-sym23-at13243142 c4) ▸
       at 5 1 (Bx0-3124 ∷ []) (lem-sym34-at13213442 c4) ▸
       at 5 1 (Bx0-1324 ∷ []) (lem-sym12-at132132 c4) ▸
       at 5 2 (CCZ234 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at2332 c4) ▸
       at 1 2 (CCZ234 ∷ CX41 ∷ []) (lw0 c4 (CX41 ∷ CCZ234 ∷ []) (CCZ234 ∷ CX41 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (CCZ234 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ []) (lw0 c4 (CX41 ∷ CS13⁻ ∷ CX41 ∷ CCZ234 ∷ []) (CCZ234 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ []) tt tt Eq.refl) ▸
       at 1 2 [] (lw0 c4 (CCZ234 ∷ CCZ234 ∷ []) [] tt tt Eq.refl) ▸ done

  b4 : Chain (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS34 ∷ []) (CCZ134 ∷ Sb0-1-23-4 ∷ [])
  b4 = at 4 5 (Sb0-1-32-4 ∷ []) (refl) ▸
       at 4 2 (CS34 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS42-at2332 c4) ▸
       at 5 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 0 5 (CCZ134 ∷ []) (lw0 c4 (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl) ▸ done


-- beta-T @0410233241: 8 steps
lem-beta-T-at0410233241 : Complete 4 → ⟪ (Bx4-0321 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ []) ⟫ʷ
lem-beta-T-at0410233241 c4 = run b0
  where
  b0 : Chain (Bx4-0321 ∷ []) (Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-0312 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·0321⟩ c4) ▸
       at 1 1 (Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ []) (lem-beta-T-at0410233142 c4) ▸
       at 0 2 (Toff403 ∷ Sw12 ∷ []) (lem-nat-1-TOFF403 c4) ▸
       at 1 2 (CCZ124 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff403 ∷ Sw12 ∷ []) (lem-nat-1-TOFF403 c4) ▸
       at 3 2 (CCZ124 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;2;3) | BOX(4;0321): 10 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨4·0321⟩ : Complete 4 → ⟪ (Sb⁻0-1-2-3 ∷ Bx4-0321 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0321 ∷ Sb⁻0-1-2-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨4·0321⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb⁻0-1-2-3 ∷ Bx4-0321 ∷ []) (Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ CS12⁻ ∷ [])
  b0 = at 1 1 (Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ []) (lem-beta-T-at0410233241 c4) ▸
       at 0 2 (Toff403 ∷ Sb⁻0-1-2-3 ∷ []) (lem-comm-SBOXd⟨0·1·2·3⟩-TOFF403 c4) ▸
       at 1 1 (CS12⁻ ∷ []) (refl) ▸
       at 1 2 (CCZ124 ∷ CS12⁻ ∷ []) (lw0 c4 (CS12⁻ ∷ CCZ124 ∷ []) (CCZ124 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 2 2 (Toff403 ∷ Sb⁻0-1-2-3 ∷ []) (lem-comm-SBOXd⟨0·1·2·3⟩-TOFF403 c4) ▸
       at 3 1 (CS12⁻ ∷ []) (refl) ▸
       at 3 2 (CCZ124 ∷ CS12⁻ ∷ []) (lw0 c4 (CS12⁻ ∷ CCZ124 ∷ []) (CCZ124 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ CS12⁻ ∷ []) (Bx4-0321 ∷ Sb⁻0-1-2-3 ∷ [])
  b1 = at 4 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 0 4 (Bx4-0321 ∷ []) (sym (lem-beta-T-at0410233241 c4)) ▸ done


-- auto SBOXd(0;1;2;3) | BOX(4;2301): 14 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨4·2301⟩ : Complete 4 → ⟪ (Sb⁻0-1-2-3 ∷ Bx4-2301 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2301 ∷ Sb⁻0-1-2-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨4·2301⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb⁻0-1-2-3 ∷ Bx4-2301 ∷ []) (Toff423 ∷ CCZ014 ∷ CS12⁻ ∷ Toff423 ∷ CCZ014 ∷ [])
  b0 = at 1 1 (Toff423 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ []) (lem-beta-T-at0412233041 c4) ▸
       at 0 1 (CS12⁻ ∷ []) (refl) ▸
       at 0 2 (Toff423 ∷ CS12⁻ ∷ []) (lw0 c4 (CS12⁻ ∷ Toff423 ∷ []) (Toff423 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 1 1 (CS12⁻ ∷ []) (refl) ▸
       at 1 2 (CCZ014 ∷ CS12⁻ ∷ []) (pw3 c4 (CS12⁻ ∷ CCZ014 ∷ []) (CCZ014 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 2 1 (CS12⁻ ∷ []) (refl) ▸ done

  b1 : Chain (Toff423 ∷ CCZ014 ∷ CS12⁻ ∷ Toff423 ∷ CCZ014 ∷ []) (Bx4-2301 ∷ Sb⁻0-1-2-3 ∷ [])
  b1 = at 2 2 (Toff423 ∷ CS12⁻ ∷ []) (lw0 c4 (CS12⁻ ∷ Toff423 ∷ []) (Toff423 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 3 1 (CS12⁻ ∷ []) (refl) ▸
       at 3 2 (CCZ014 ∷ CS12⁻ ∷ []) (pw3 c4 (CS12⁻ ∷ CCZ014 ∷ []) (CCZ014 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 0 4 (Bx4-2301 ∷ []) (sym (lem-beta-T-at0412233041 c4)) ▸ done


-- auto CSd01 | BOX(0;2134): 1 steps
lem-auto-CSd01-∣-BOX⟨0·2134⟩ : Complete 4 → ⟪ (CS01⁻ ∷ Bx0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ CS01⁻ ∷ []) ⟫ʷ
lem-auto-CSd01-∣-BOX⟨0·2134⟩ c4 = run b0
  where
  b0 : Chain (CS01⁻ ∷ Bx0-2134 ∷ []) (Bx0-2134 ∷ CS01⁻ ∷ [])
  b0 = at 0 2 (Bx0-2134 ∷ CS01⁻ ∷ []) (lem-CS20-beta-ci-at1221 c4) ▸ done


-- auto CSd01 | BOX(0;2134) @3443: 7 steps
lem-auto-CSd01-∣-BOX⟨0·2134⟩-at3443 : Complete 4 → ⟪ (CS01⁻ ∷ Bx0-2143 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2143 ∷ CS01⁻ ∷ []) ⟫ʷ
lem-auto-CSd01-∣-BOX⟨0·2134⟩-at3443 c4 = run b0
  where
  b0 : Chain (CS01⁻ ∷ Bx0-2143 ∷ []) (Bx0-2143 ∷ CS01⁻ ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS01⁻ ∷ Sw34 ∷ []) (sym (c₂ (CS • CS • CS) (Swap ↑))) ▸
       at 2 2 (Bx0-2134 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·2143⟩ c4) ▸
       at 1 2 (Bx0-2134 ∷ CS01⁻ ∷ []) (lem-auto-CSd01-∣-BOX⟨0·2134⟩ c4) ▸
       at 0 2 (Bx0-2143 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·2134⟩ c4) ▸
       at 1 2 (CS01⁻ ∷ Sw34 ∷ []) (sym (c₂ (CS • CS • CS) (Swap ↑))) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CSd01 | BOX(0;2134) @12213443: 7 steps
lem-auto-CSd01-∣-BOX⟨0·2134⟩-at12213443 : Complete 4 → ⟪ (CS02⁻ ∷ Bx0-1243 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1243 ∷ CS02⁻ ∷ []) ⟫ʷ
lem-auto-CSd01-∣-BOX⟨0·2134⟩-at12213443 c4 = run b0
  where
  b0 : Chain (CS02⁻ ∷ Bx0-1243 ∷ []) (Bx0-1243 ∷ CS02⁻ ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS01⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd02 c4) ▸
       at 2 2 (Bx0-2143 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1243⟩ c4) ▸
       at 1 2 (Bx0-2143 ∷ CS01⁻ ∷ []) (lem-auto-CSd01-∣-BOX⟨0·2134⟩-at3443 c4) ▸
       at 0 2 (Bx0-1243 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2143⟩ c4) ▸
       at 1 2 (CS02⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd01 c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CSd01 | BOX(0;2134) @0112203443: 7 steps
lem-auto-CSd01-∣-BOX⟨0·2134⟩-at0112203443 : Complete 4 → ⟪ (CS12⁻ ∷ Bx1-0243 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0243 ∷ CS12⁻ ∷ []) ⟫ʷ
lem-auto-CSd01-∣-BOX⟨0·2134⟩-at0112203443 c4 = run b0
  where
  b0 : Chain (CS12⁻ ∷ Bx1-0243 ∷ []) (Bx1-0243 ∷ CS12⁻ ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS02⁻ ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS12⁻ ∷ []) (CS02⁻ ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-1243 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0243⟩ c4) ▸
       at 1 2 (Bx0-1243 ∷ CS02⁻ ∷ []) (lem-auto-CSd01-∣-BOX⟨0·2134⟩-at12213443 c4) ▸
       at 0 2 (Bx1-0243 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1243⟩ c4) ▸
       at 1 2 (CS12⁻ ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS02⁻ ∷ []) (CS12⁻ ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;2;3) | BOX(1;0243): 3 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨1·0243⟩ : Complete 4 → ⟪ (Sb⁻0-1-2-3 ∷ Bx1-0243 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0243 ∷ Sb⁻0-1-2-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨1·0243⟩ c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-2-3 ∷ Bx1-0243 ∷ []) (Bx1-0243 ∷ Sb⁻0-1-2-3 ∷ [])
  b0 = at 0 1 (CS12⁻ ∷ []) (refl) ▸
       at 0 2 (Bx1-0243 ∷ CS12⁻ ∷ []) (lem-auto-CSd01-∣-BOX⟨0·2134⟩-at0112203443 c4) ▸
       at 1 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸ done


-- auto SBOXd(0;1;2;3) | SBOX(1;0;24;3): 19 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-SBOX⟨1·0·24·3⟩ : Complete 4 → ⟪ (Sb⁻0-1-2-3 ∷ Sb1-0-24-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-24-3 ∷ Sb⁻0-1-2-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-SBOX⟨1·0·24·3⟩ c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sb⁻0-1-2-3 ∷ Sb1-0-24-3 ∷ []) (Bx1-0243 ∷ Toff324 ∷ CS03 ∷ CS12⁻ ∷ Toff324 ∷ Sb⁻1-0-3-4 ∷ [])
  b0 = at 1 1 (Bx1-0243 ∷ Toff324 ∷ Sb1-0-3-4 ∷ Toff324 ∷ Sb⁻1-0-3-4 ∷ []) (refl) ▸
       at 0 2 (Bx1-0243 ∷ Sb⁻0-1-2-3 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨1·0243⟩ c4) ▸
       at 1 1 (CS12⁻ ∷ []) (refl) ▸
       at 1 2 (Toff324 ∷ CS12⁻ ∷ []) (lw0 c4 (CS12⁻ ∷ Toff324 ∷ []) (Toff324 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 2 1 (CS12⁻ ∷ []) (refl) ▸
       at 3 1 (CS03 ∷ []) (refl) ▸
       at 2 2 (CS03 ∷ CS12⁻ ∷ []) (lw4 c4 (CS12⁻ ∷ CS03 ∷ []) (CS03 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Bx1-0243 ∷ Toff324 ∷ CS03 ∷ CS12⁻ ∷ Toff324 ∷ Sb⁻1-0-3-4 ∷ []) (Bx1-0243 ∷ Toff324 ∷ Sb1-0-3-4 ∷ Toff324 ∷ CS03⁻ ∷ CS12⁻ ∷ [])
  b1 = at 2 1 (Sb1-0-3-4 ∷ []) (refl) ▸
       at 3 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 3 1 (CS12⁻ ∷ []) (refl) ▸
       at 3 2 (Toff324 ∷ CS12⁻ ∷ []) (lw0 c4 (CS12⁻ ∷ Toff324 ∷ []) (Toff324 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 4 1 (CS12⁻ ∷ []) (refl) ▸
       at 5 1 (CS03⁻ ∷ []) (refl) ▸
       at 4 2 (CS03⁻ ∷ CS12⁻ ∷ []) (lw4 c4 (CS12⁻ ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Bx1-0243 ∷ Toff324 ∷ Sb1-0-3-4 ∷ Toff324 ∷ CS03⁻ ∷ CS12⁻ ∷ []) (Sb1-0-24-3 ∷ Sb⁻0-1-2-3 ∷ [])
  b2 = at 4 1 (Sb⁻1-0-3-4 ∷ []) (refl) ▸
       at 5 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 0 5 (Sb1-0-24-3 ∷ []) (refl) ▸ done


-- auto CS01 | BOX(0;2134): 1 steps
lem-auto-CS01-∣-BOX⟨0·2134⟩ : Complete 4 → ⟪ (CS01 ∷ Bx0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ CS01 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨0·2134⟩ c4 = run b0
  where
  b0 : Chain (CS01 ∷ Bx0-2134 ∷ []) (Bx0-2134 ∷ CS01 ∷ [])
  b0 = at 0 2 (Bx0-2134 ∷ CS01 ∷ []) (lem-CS20-beta-c-at1221 c4) ▸ done


-- auto CS01 | BOX(0;2134) @3443: 7 steps
lem-auto-CS01-∣-BOX⟨0·2134⟩-at3443 : Complete 4 → ⟪ (CS01 ∷ Bx0-2143 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2143 ∷ CS01 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨0·2134⟩-at3443 c4 = run b0
  where
  b0 : Chain (CS01 ∷ Bx0-2143 ∷ []) (Bx0-2143 ∷ CS01 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS01 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸
       at 2 2 (Bx0-2134 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·2143⟩ c4) ▸
       at 1 2 (Bx0-2134 ∷ CS01 ∷ []) (lem-auto-CS01-∣-BOX⟨0·2134⟩ c4) ▸
       at 0 2 (Bx0-2143 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·2134⟩ c4) ▸
       at 1 2 (CS01 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CS01 | BOX(0;2134) @12213443: 7 steps
lem-auto-CS01-∣-BOX⟨0·2134⟩-at12213443 : Complete 4 → ⟪ (CS02 ∷ Bx0-1243 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1243 ∷ CS02 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨0·2134⟩-at12213443 c4 = run b0
  where
  b0 : Chain (CS02 ∷ Bx0-1243 ∷ []) (Bx0-1243 ∷ CS02 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS01 ∷ Sw12 ∷ []) (lem-nat-1-CS02 c4) ▸
       at 2 2 (Bx0-2143 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1243⟩ c4) ▸
       at 1 2 (Bx0-2143 ∷ CS01 ∷ []) (lem-auto-CS01-∣-BOX⟨0·2134⟩-at3443 c4) ▸
       at 0 2 (Bx0-1243 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2143⟩ c4) ▸
       at 1 2 (CS02 ∷ Sw12 ∷ []) (lem-nat-1-CS01 c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CS01 | BOX(0;2134) @0112203443: 7 steps
lem-auto-CS01-∣-BOX⟨0·2134⟩-at0112203443 : Complete 4 → ⟪ (CS12 ∷ Bx1-0243 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0243 ∷ CS12 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨0·2134⟩-at0112203443 c4 = run b0
  where
  b0 : Chain (CS12 ∷ Bx1-0243 ∷ []) (Bx1-0243 ∷ CS12 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS02 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-1243 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0243⟩ c4) ▸
       at 1 2 (Bx0-1243 ∷ CS02 ∷ []) (lem-auto-CS01-∣-BOX⟨0·2134⟩-at12213443 c4) ▸
       at 0 2 (Bx1-0243 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1243⟩ c4) ▸
       at 1 2 (CS12 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS02 ∷ []) (CS12 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;2;3) | BOX(1;0243): 3 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨1·0243⟩ : Complete 4 → ⟪ (Sb0-1-2-3 ∷ Bx1-0243 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0243 ∷ Sb0-1-2-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨1·0243⟩ c4 = run b0
  where
  b0 : Chain (Sb0-1-2-3 ∷ Bx1-0243 ∷ []) (Bx1-0243 ∷ Sb0-1-2-3 ∷ [])
  b0 = at 0 1 (CS12 ∷ []) (refl) ▸
       at 0 2 (Bx1-0243 ∷ CS12 ∷ []) (lem-auto-CS01-∣-BOX⟨0·2134⟩-at0112203443 c4) ▸
       at 1 1 (Sb0-1-2-3 ∷ []) (refl) ▸ done


-- auto TOFF012 | CCZ234: 7 steps
lem-auto-TOFF012-∣-CCZ234 : Complete 4 → ⟪ (Toff012 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Toff012 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-CCZ234 c4 = run b0
  where
  b0 : Chain (Toff012 ∷ CCZ234 ∷ []) (CCZ234 ∷ Toff012 ∷ [])
  b0 = at 1 1 (CS24 ∷ CX34 ∷ CS24⁻ ∷ CX34 ∷ CS23 ∷ []) (lw0 c4 (CCZ234 ∷ []) (CS24 ∷ CX34 ∷ CS24⁻ ∷ CX34 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (CS24 ∷ Toff012 ∷ []) (pw3 c4 (Toff012 ∷ CS24 ∷ []) (CS24 ∷ Toff012 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CX34 ∷ Toff012 ∷ []) (c₃ (Toff) (CX₀₁)) ▸
       at 2 2 (CS24⁻ ∷ Toff012 ∷ []) (pw3 c4 (Toff012 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ Toff012 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CX34 ∷ Toff012 ∷ []) (c₃ (Toff) (CX₀₁)) ▸
       at 4 2 (CS23 ∷ Toff012 ∷ []) (lw4 c4 (Toff012 ∷ CS23 ∷ []) (CS23 ∷ Toff012 ∷ []) tt tt Eq.refl) ▸
       at 0 5 (CCZ234 ∷ []) (lw0 c4 (CS24 ∷ CX34 ∷ CS24⁻ ∷ CX34 ∷ CS23 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸ done


-- auto CSd01 | BOX(0;1234): 3 steps
lem-auto-CSd01-∣-BOX⟨0·1234⟩ : Complete 4 → ⟪ (CS01⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CS01⁻ ∷ []) ⟫ʷ
lem-auto-CSd01-∣-BOX⟨0·1234⟩ c4 = run b0
  where
  b0 : Chain (CS01⁻ ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CS01⁻ ∷ [])
  b0 = at 1 1 (Bx0-2134 ∷ []) (lem-sym12 c4) ▸
       at 0 2 (Bx0-2134 ∷ CS01⁻ ∷ []) (lem-CS20-beta-ci-at1221 c4) ▸
       at 0 1 (Bx0-1234 ∷ []) (lem-sym12-at1221 c4) ▸ done


-- auto CSd01 | BOX(0;1234) @3443: 7 steps
lem-auto-CSd01-∣-BOX⟨0·1234⟩-at3443 : Complete 4 → ⟪ (CS01⁻ ∷ Bx0-1243 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1243 ∷ CS01⁻ ∷ []) ⟫ʷ
lem-auto-CSd01-∣-BOX⟨0·1234⟩-at3443 c4 = run b0
  where
  b0 : Chain (CS01⁻ ∷ Bx0-1243 ∷ []) (Bx0-1243 ∷ CS01⁻ ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS01⁻ ∷ Sw34 ∷ []) (sym (c₂ (CS • CS • CS) (Swap ↑))) ▸
       at 2 2 (Bx0-1234 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1243⟩ c4) ▸
       at 1 2 (Bx0-1234 ∷ CS01⁻ ∷ []) (lem-auto-CSd01-∣-BOX⟨0·1234⟩ c4) ▸
       at 0 2 (Bx0-1243 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1234⟩ c4) ▸
       at 1 2 (CS01⁻ ∷ Sw34 ∷ []) (sym (c₂ (CS • CS • CS) (Swap ↑))) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CSd01 | BOX(0;1234) @12213443: 7 steps
lem-auto-CSd01-∣-BOX⟨0·1234⟩-at12213443 : Complete 4 → ⟪ (CS02⁻ ∷ Bx0-2143 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2143 ∷ CS02⁻ ∷ []) ⟫ʷ
lem-auto-CSd01-∣-BOX⟨0·1234⟩-at12213443 c4 = run b0
  where
  b0 : Chain (CS02⁻ ∷ Bx0-2143 ∷ []) (Bx0-2143 ∷ CS02⁻ ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS01⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd02 c4) ▸
       at 2 2 (Bx0-1243 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2143⟩ c4) ▸
       at 1 2 (Bx0-1243 ∷ CS01⁻ ∷ []) (lem-auto-CSd01-∣-BOX⟨0·1234⟩-at3443 c4) ▸
       at 0 2 (Bx0-2143 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1243⟩ c4) ▸
       at 1 2 (CS02⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd01 c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done

