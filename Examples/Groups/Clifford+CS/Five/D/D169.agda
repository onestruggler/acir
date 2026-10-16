{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D169 where

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
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-Cz-beta ; lem-beta-T-at12243143 ; lem-sym12 ; lem-sym23 ; lem-sym34)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-sym12-at1221 ; lem-sym23-at1221 ; lem-sym34-at1221)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-auto-BOX⟨0·1234⟩-∣-CCZ103 ; lem-sym12-at0112203443 ; lem-sym23-at011220 ; lem-sym23-at01122330 ; lem-sym23-at12213443 ; lem-sym23-at122331 ; lem-sym23-at12243143 ; lem-sym23-at2332 ; lem-sym23-at243243 ; lem-sym23-at3443 ; lem-sym34-at12213443 ; lem-sym34-at3443)
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-sym34-at122331)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-CX23-beta-at2332 ; lem-CX23-beta-at243243 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-CS21-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D006 using (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D007 using (lem-SBsym-at0113203442 ; lem-T312-beta-at12233441)
open import Examples.Groups.Clifford+CS.Five.D.D008 using (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS31-at2332 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-CS41-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D010 using (lem-sym34-at01122330)
open import Examples.Groups.Clifford+CS.Five.D.D012 using (lem-sym12-at01103443)
open import Examples.Groups.Clifford+CS.Five.D.D135 using (lem-auto-BOX⟨0·1234⟩-∣-CCZ142 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ243 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-CS02-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D136 using (lem-sym12-at1331)
open import Examples.Groups.Clifford+CS.Five.D.D137 using (lem-sym12-at12233441)
open import Examples.Groups.Clifford+CS.Five.D.D142 using (lem-auto-CCZ012-∣-CCZ342-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D150 using (lem-T312-beta-at12243143 ; lem-sym23-at13243241 ; lem-sym23-at133441 ; lem-sym34-at133441)
open import Examples.Groups.Clifford+CS.Five.D.D152 using (lem-auto-BOX⟨0·1234⟩-∣-CSd31)
open import Examples.Groups.Clifford+CS.Five.D.D153 using (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ143 ; lem-sym23-at0113243240 ; lem-sym23-at01133440 ; lem-sym34-at12243143)
open import Examples.Groups.Clifford+CS.Five.D.D157 using (lem-sym23-at12233441 ; lem-sym23-at122441 ; lem-sym34-at122441)
open import Examples.Groups.Clifford+CS.Five.D.D160 using (lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd02-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D165 using (lem-sym34-at01133440)
open import Examples.Groups.Clifford+CS.Five.D.D167 using (lem-auto-CS01-∣-BOX⟨0·2314⟩-at3443 ; lem-auto-CSd01-∣-BOX⟨0·2314⟩-at3443)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-1-BOX⟨0·2134⟩ ; lem-nat-1-BOX⟨0·2413⟩ ; lem-nat-1-CCZ023 ; lem-nat-2-BOX⟨0·1234⟩ ; lem-nat-2-BOX⟨0·1324⟩ ; lem-nat-2-CCZ012 ; lem-nat-2-CCZ013)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-1-BOX⟨0·1423⟩ ; lem-nat-1-CCZ013)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-2-CCZ124 ; lem-nat-2-CCZ134)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-0-TOFF403)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-1-BOX⟨0·1234⟩)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-0-BOX⟨0·1423⟩ ; lem-nat-0-TOFF024 ; lem-nat-0-TOFF413 ; lem-nat-1-TOFF401 ; lem-nat-2-TOFF402 ; lem-nat-3-TOFF301)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-nat-0-BOX⟨1·0423⟩ ; lem-nat-3-CCZ123 ; lem-nat-3-CCZ124)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-nat-0-BOX⟨0·2134⟩ ; lem-nat-0-BOX⟨1·2034⟩)
open import Examples.Groups.Clifford+CS.Five.D.R012 using (lem-nat-0-BOX⟨0·2143⟩ ; lem-nat-0-BOX⟨0·2314⟩ ; lem-nat-0-BOX⟨1·2043⟩ ; lem-nat-1-CS01 ; lem-nat-1-CS02)
open import Examples.Groups.Clifford+CS.Five.D.R013 using (lem-nat-2-CSd12 ; lem-nat-2-CSd13 ; lem-nat-2-TOFF403)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-nat-0-SBOX⟨0·1·42·3⟩ ; lem-nat-0-SBOX⟨1·0·42·3⟩ ; lem-nat-1-CSd02 ; lem-nat-1-SBOX⟨1·0·42·3⟩ ; lem-nat-1-SBOX⟨2·0·41·3⟩ ; lem-nat-2-BOX⟨1·0432⟩ ; lem-nat-2-SBOX⟨0·1·23·4⟩ ; lem-nat-2-SBOX⟨0·1·32·4⟩ ; lem-nat-2-SBOX⟨0·1·4·2⟩ ; lem-nat-2-SBOX⟨0·1·4·3⟩ ; lem-nat-2-SBOXd⟨0·1·4·2⟩ ; lem-nat-2-SBOXd⟨0·1·4·3⟩ ; lem-nat-3-SBOX⟨0·1·32·4⟩ ; lem-nat-3-SBOX⟨0·1·3·2⟩ ; lem-nat-3-SBOX⟨0·1·42·3⟩ ; lem-nat-3-SBOX⟨0·1·4·2⟩ ; lem-nat-3-SBOXd⟨0·1·3·2⟩ ; lem-nat-3-SBOXd⟨0·1·4·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R015 using (lem-nat-0-BOX⟨1·2340⟩ ; lem-nat-1-CSd01 ; lem-nat-3-BOX⟨1·0342⟩ ; lem-nat-3-SBOX⟨1·0·2·4⟩ ; lem-nat-3-SBOXd⟨1·0·2·4⟩)
open import Examples.Groups.Clifford+CS.Five.D.R017 using (lem-nat-1-TOFF402 ; lem-nat-3-TOFF401)
open import Examples.Groups.Clifford+CS.Five.D.R019 using (lem-nat-0-BOX⟨0·2341⟩ ; lem-nat-2-SBOX⟨0·1·2·3⟩ ; lem-nat-2-SBOX⟨0·1·3·2⟩ ; lem-nat-2-SBOXd⟨0·1·2·3⟩ ; lem-nat-2-SBOXd⟨0·1·3·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R020 using (lem-nat-2-BOX⟨1·0243⟩ ; lem-nat-2-SBOX⟨1·0·3·4⟩ ; lem-nat-2-SBOXd⟨1·0·3·4⟩)
open import Examples.Groups.Clifford+CS.Five.D.R021 using (lem-nat-0-BOX⟨0·2431⟩ ; lem-nat-0-BOX⟨1·2430⟩ ; lem-nat-1-SBOX⟨0·1·2·3⟩ ; lem-nat-1-SBOX⟨0·2·1·3⟩ ; lem-nat-1-SBOXd⟨0·1·2·3⟩ ; lem-nat-1-SBOXd⟨0·2·1·3⟩)
open import Examples.Groups.Clifford+CS.Five.D.R022 using (lem-nat-2-SBOX⟨1·0·2·4⟩ ; lem-nat-2-SBOXd⟨1·0·2·4⟩ ; lem-nat-3-SBOX⟨1·0·2·3⟩ ; lem-nat-3-SBOXd⟨1·0·2·3⟩)
open import Examples.Groups.Clifford+CS.Five.D.R023 using (lem-nat-2-BOX⟨1·0423⟩)
open import Examples.Groups.Clifford+CS.Five.D.R024 using (lem-nat-0-SBOXd⟨0·2·4·3⟩ ; lem-nat-0-SBOXd⟨1·2·4·3⟩ ; lem-nat-1-SBOXd⟨0·1·4·3⟩ ; lem-nat-1-SBOXd⟨0·2·4·3⟩)
open import Examples.Groups.Clifford+CS.Five.D.R026 using (lem-nat-2-BOX⟨1·0342⟩)
open import Examples.Groups.Clifford+CS.Five.D.R029 using (lem-nat-0-BOX⟨0·2413⟩ ; lem-nat-0-BOX⟨1·2403⟩)
open import Examples.Groups.Clifford+CS.Five.D.R031 using (lem-nat-0-BOX⟨0·3241⟩)
open import Examples.Groups.Clifford+CS.Five.D.R033 using (lem-nat-0-SBOX⟨0·1·2·3⟩ ; lem-nat-0-SBOX⟨1·0·2·3⟩ ; lem-nat-0-SBOXd⟨0·1·2·3⟩ ; lem-nat-0-SBOXd⟨1·0·2·3⟩)
open import Examples.Groups.Clifford+CS.Five.D.R034 using (lem-nat-1-SBOXd⟨1·3·4·2⟩ ; lem-nat-1-SBOXd⟨2·3·4·1⟩ ; lem-nat-2-SBOXd⟨1·2·4·3⟩ ; lem-nat-2-SBOXd⟨1·3·4·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R035 using (lem-comm-CCZ023-SBOX⟨0·1·4·3⟩ ; lem-comm-CCZ023-SBOXd⟨0·1·4·3⟩)
open import Examples.Groups.Clifford+CS.Five.D.R037 using (lem-nat-0-BOX⟨1·3204⟩ ; lem-nat-3-BOX⟨1·0432⟩ ; lem-nat-3-SBOXd⟨2·3·4·1⟩ ; lem-nat-3-SBOXd⟨2·4·3·1⟩)
-- auto BOX(0;1234) | CSd31 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd31-at2332 : Complete 4 → ⟪ (Bx0-1324 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd31-at2332 c4 = run b0
  where
  b0 : Chain (Bx0-1324 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ Bx0-1324 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ c4) ▸
       at 2 2 (CS13⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd12 c4) ▸
       at 1 2 (CS13⁻ ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd31 c4) ▸
       at 0 2 (CS12⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd13 c4) ▸
       at 1 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CCZ132: 26 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ132 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ132 c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (Sb0-1-23-4 ∷ CCZ123 ∷ []) (CS12 ∷ Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS13 ∷ [])
  b0 = at 1 1 (CS12 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ CS13 ∷ []) (lw4 c4 (CCZ123 ∷ []) (CS12 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (CS12 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS31-at2332 c4) ▸
       at 1 1 (Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ []) (refl) ▸
       at 5 1 (CS14⁻ ∷ []) (refl) ▸
       at 5 4 (CX32 ∷ CS12⁻ ∷ CX32 ∷ CS14⁻ ∷ []) (lw0 c4 (CS14⁻ ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ []) (CX32 ∷ CS12⁻ ∷ CX32 ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 8 1 (Sb⁻0-1-4-2 ∷ []) (refl) ▸
       at 4 4 (CX32 ∷ CS12⁻ ∷ CX32 ∷ Toff423 ∷ []) (lw0 c4 (Toff423 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ []) (CX32 ∷ CS12⁻ ∷ CX32 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CS12 ∷ Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS13 ∷ []) (CS12 ∷ CX32 ∷ CCZ134 ∷ CS12⁻ ∷ Bx0-1324 ∷ CX32 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS13 ∷ [])
  b1 = at 3 1 (CS14 ∷ []) (refl) ▸
       at 3 4 (CX32 ∷ CS12⁻ ∷ CX32 ∷ CS14 ∷ []) (lw0 c4 (CS14 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ []) (CX32 ∷ CS12⁻ ∷ CX32 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Sb0-1-4-2 ∷ []) (refl) ▸
       at 2 4 (CX32 ∷ CS12⁻ ∷ CX32 ∷ Toff423 ∷ []) (lw0 c4 (Toff423 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ []) (CX32 ∷ CS12⁻ ∷ CX32 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 1 0 (CX32 ∷ CX32 ∷ []) (lw4 c4 [] (CX32 ∷ CX32 ∷ []) tt tt Eq.refl) ▸
       at 2 3 (Bx0-1324 ∷ CCZ134 ∷ []) (lem-CX23-beta-at2332 c4) ▸
       at 2 2 (CCZ134 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at2332 c4) ▸
       at 3 2 (CS12⁻ ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd31-at2332 c4) ▸ done

  b2 : Chain (CS12 ∷ CX32 ∷ CCZ134 ∷ CS12⁻ ∷ Bx0-1324 ∷ CX32 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS13 ∷ []) (CS12 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ CS13 ∷ Sb0-1-32-4 ∷ [])
  b2 = at 4 0 (CX32 ∷ CX32 ∷ []) (lw4 c4 [] (CX32 ∷ CX32 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (Bx0-1324 ∷ CCZ134 ∷ []) (lem-CX23-beta-at2332 c4) ▸
       at 5 2 (CCZ134 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at2332 c4) ▸
       at 1 2 (CCZ134 ∷ CX32 ∷ []) (lw0 c4 (CX32 ∷ CCZ134 ∷ []) (CCZ134 ∷ CX32 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (CCZ134 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ []) (lw0 c4 (CX32 ∷ CS12⁻ ∷ CX32 ∷ CCZ134 ∷ []) (CCZ134 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ []) tt tt Eq.refl) ▸
       at 1 2 [] (lw0 c4 (CCZ134 ∷ CCZ134 ∷ []) [] tt tt Eq.refl) ▸
       at 4 5 (Sb0-1-32-4 ∷ []) (refl) ▸
       at 4 2 (CS13 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS21-at2332 c4) ▸ done

  b3 : Chain (CS12 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ CS13 ∷ Sb0-1-32-4 ∷ []) (CCZ123 ∷ Sb0-1-23-4 ∷ [])
  b3 = at 5 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 0 5 (CCZ123 ∷ []) (lw4 c4 (CS12 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ CS13 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ142 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ142-at2332 : Complete 4 → ⟪ (Bx0-1324 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ142-at2332 c4 = run b0
  where
  b0 : Chain (Bx0-1324 ∷ CCZ134 ∷ []) (CCZ134 ∷ Bx0-1324 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ c4) ▸
       at 2 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 1 2 (CCZ124 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ142 c4) ▸
       at 0 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 1 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CCZ142: 36 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ142 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ142 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (run b4))))
  where
  b0 : Chain (Sb0-1-23-4 ∷ CCZ124 ∷ []) (CS12 ∷ Bx0-1324 ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ CX42 ∷ CS12⁻ ∷ CX42 ∷ Sb⁻0-1-4-2 ∷ CS14 ∷ [])
  b0 = at 1 1 (CS12 ∷ CX42 ∷ CS12⁻ ∷ CX42 ∷ CS14 ∷ []) (lw0 c4 (CCZ124 ∷ []) (CS12 ∷ CX42 ∷ CS12⁻ ∷ CX42 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (CS12 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS31-at2332 c4) ▸
       at 1 1 (Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ []) (refl) ▸
       at 5 1 (CS14⁻ ∷ []) (refl) ▸
       at 5 4 (CX42 ∷ CS12⁻ ∷ CX42 ∷ CS14⁻ ∷ []) (lw0 c4 (CS14⁻ ∷ CX42 ∷ CS12⁻ ∷ CX42 ∷ []) (CX42 ∷ CS12⁻ ∷ CX42 ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 8 1 (Sb⁻0-1-4-2 ∷ []) (refl) ▸
       at 3 1 (CS14 ∷ []) (refl) ▸ done

  b1 : Chain (CS12 ∷ Bx0-1324 ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ CX42 ∷ CS12⁻ ∷ CX42 ∷ Sb⁻0-1-4-2 ∷ CS14 ∷ []) (CS12 ∷ CX42 ∷ Bx0-1243 ∷ CCZ134 ∷ CS12⁻ ∷ CX42 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS14 ∷ [])
  b1 = at 2 6 (CX42 ∷ CS12⁻ ∷ CX42 ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ []) (lw0 c4 (Toff423 ∷ CS14 ∷ Toff423 ∷ CX42 ∷ CS12⁻ ∷ CX42 ∷ []) (CX42 ∷ CS12⁻ ∷ CX42 ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Sb0-1-4-2 ∷ []) (refl) ▸
       at 1 0 (CX42 ∷ CX42 ∷ []) (lw0 c4 [] (CX42 ∷ CX42 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Bx0-1234 ∷ []) (lem-sym23-at2332 c4) ▸
       at 3 1 (Bx0-1243 ∷ []) (lem-sym34 c4) ▸
       at 3 1 (Bx0-1423 ∷ []) (lem-sym23-at3443 c4) ▸
       at 2 3 (Bx0-1423 ∷ CCZ134 ∷ []) (lem-CX23-beta-at243243 c4) ▸
       at 2 1 (Bx0-1243 ∷ []) (lem-sym23-at243243 c4) ▸ done

  b2 : Chain (CS12 ∷ CX42 ∷ Bx0-1243 ∷ CCZ134 ∷ CS12⁻ ∷ CX42 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS14 ∷ []) (CS12 ∷ CX42 ∷ CCZ134 ∷ CS12⁻ ∷ CX42 ∷ CX42 ∷ Bx0-1423 ∷ CX42 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS14 ∷ [])
  b2 = at 2 1 (Bx0-1234 ∷ []) (lem-sym34-at3443 c4) ▸
       at 2 1 (Bx0-1324 ∷ []) (lem-sym23 c4) ▸
       at 2 2 (CCZ134 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ142-at2332 c4) ▸
       at 3 2 (CS12⁻ ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd31-at2332 c4) ▸
       at 4 0 (CX42 ∷ CX42 ∷ []) (lw0 c4 [] (CX42 ∷ CX42 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Bx0-1234 ∷ []) (lem-sym23-at2332 c4) ▸
       at 6 1 (Bx0-1243 ∷ []) (lem-sym34 c4) ▸
       at 6 1 (Bx0-1423 ∷ []) (lem-sym23-at3443 c4) ▸ done

  b3 : Chain (CS12 ∷ CX42 ∷ CCZ134 ∷ CS12⁻ ∷ CX42 ∷ CX42 ∷ Bx0-1423 ∷ CX42 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS14 ∷ []) (CS12 ∷ CX42 ∷ CS12⁻ ∷ CX42 ∷ Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS14 ∷ [])
  b3 = at 5 3 (Bx0-1423 ∷ CCZ134 ∷ []) (lem-CX23-beta-at243243 c4) ▸
       at 5 1 (Bx0-1243 ∷ []) (lem-sym23-at243243 c4) ▸
       at 5 1 (Bx0-1234 ∷ []) (lem-sym34-at3443 c4) ▸
       at 5 1 (Bx0-1324 ∷ []) (lem-sym23 c4) ▸
       at 5 2 (CCZ134 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ142-at2332 c4) ▸
       at 1 2 (CCZ134 ∷ CX42 ∷ []) (lw0 c4 (CX42 ∷ CCZ134 ∷ []) (CCZ134 ∷ CX42 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (CCZ134 ∷ CX42 ∷ CS12⁻ ∷ CX42 ∷ []) (lw0 c4 (CX42 ∷ CS12⁻ ∷ CX42 ∷ CCZ134 ∷ []) (CCZ134 ∷ CX42 ∷ CS12⁻ ∷ CX42 ∷ []) tt tt Eq.refl) ▸
       at 1 2 [] (lw0 c4 (CCZ134 ∷ CCZ134 ∷ []) [] tt tt Eq.refl) ▸ done

  b4 : Chain (CS12 ∷ CX42 ∷ CS12⁻ ∷ CX42 ∷ Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ CS14 ∷ []) (CCZ124 ∷ Sb0-1-23-4 ∷ [])
  b4 = at 4 5 (Sb0-1-32-4 ∷ []) (refl) ▸
       at 4 2 (CS14 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS41-at2332 c4) ▸
       at 5 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 0 5 (CCZ124 ∷ []) (lw0 c4 (CS12 ∷ CX42 ∷ CS12⁻ ∷ CX42 ∷ CS14 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl) ▸ done


-- auto CSd01 | BOX(0;2314) @12213443: 7 steps
lem-auto-CSd01-∣-BOX⟨0·2314⟩-at12213443 : Complete 4 → ⟪ (CS02⁻ ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ CS02⁻ ∷ []) ⟫ʷ
lem-auto-CSd01-∣-BOX⟨0·2314⟩-at12213443 c4 = run b0
  where
  b0 : Chain (CS02⁻ ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ CS02⁻ ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS01⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd02 c4) ▸
       at 2 2 (Bx0-2413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1423⟩ c4) ▸
       at 1 2 (Bx0-2413 ∷ CS01⁻ ∷ []) (lem-auto-CSd01-∣-BOX⟨0·2314⟩-at3443 c4) ▸
       at 0 2 (Bx0-1423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2413⟩ c4) ▸
       at 1 2 (CS02⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd01 c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CSd01 | BOX(0;2314) @0112203443: 7 steps
lem-auto-CSd01-∣-BOX⟨0·2314⟩-at0112203443 : Complete 4 → ⟪ (CS12⁻ ∷ Bx1-0423 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0423 ∷ CS12⁻ ∷ []) ⟫ʷ
lem-auto-CSd01-∣-BOX⟨0·2314⟩-at0112203443 c4 = run b0
  where
  b0 : Chain (CS12⁻ ∷ Bx1-0423 ∷ []) (Bx1-0423 ∷ CS12⁻ ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS02⁻ ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS12⁻ ∷ []) (CS02⁻ ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ c4) ▸
       at 1 2 (Bx0-1423 ∷ CS02⁻ ∷ []) (lem-auto-CSd01-∣-BOX⟨0·2314⟩-at12213443 c4) ▸
       at 0 2 (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ c4) ▸
       at 1 2 (CS12⁻ ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS02⁻ ∷ []) (CS12⁻ ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;2;3) | BOX(1;0423): 3 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨1·0423⟩ : Complete 4 → ⟪ (Sb⁻0-1-2-3 ∷ Bx1-0423 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0423 ∷ Sb⁻0-1-2-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨1·0423⟩ c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-2-3 ∷ Bx1-0423 ∷ []) (Bx1-0423 ∷ Sb⁻0-1-2-3 ∷ [])
  b0 = at 0 1 (CS12⁻ ∷ []) (refl) ▸
       at 0 2 (Bx1-0423 ∷ CS12⁻ ∷ []) (lem-auto-CSd01-∣-BOX⟨0·2314⟩-at0112203443 c4) ▸
       at 1 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸ done


-- auto CS01 | BOX(0;2314) @12213443: 7 steps
lem-auto-CS01-∣-BOX⟨0·2314⟩-at12213443 : Complete 4 → ⟪ (CS02 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ CS02 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨0·2314⟩-at12213443 c4 = run b0
  where
  b0 : Chain (CS02 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ CS02 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS01 ∷ Sw12 ∷ []) (lem-nat-1-CS02 c4) ▸
       at 2 2 (Bx0-2413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1423⟩ c4) ▸
       at 1 2 (Bx0-2413 ∷ CS01 ∷ []) (lem-auto-CS01-∣-BOX⟨0·2314⟩-at3443 c4) ▸
       at 0 2 (Bx0-1423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2413⟩ c4) ▸
       at 1 2 (CS02 ∷ Sw12 ∷ []) (lem-nat-1-CS01 c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CS01 | BOX(0;2314) @0112203443: 7 steps
lem-auto-CS01-∣-BOX⟨0·2314⟩-at0112203443 : Complete 4 → ⟪ (CS12 ∷ Bx1-0423 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0423 ∷ CS12 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨0·2314⟩-at0112203443 c4 = run b0
  where
  b0 : Chain (CS12 ∷ Bx1-0423 ∷ []) (Bx1-0423 ∷ CS12 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS02 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ c4) ▸
       at 1 2 (Bx0-1423 ∷ CS02 ∷ []) (lem-auto-CS01-∣-BOX⟨0·2314⟩-at12213443 c4) ▸
       at 0 2 (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ c4) ▸
       at 1 2 (CS12 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS02 ∷ []) (CS12 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;2;3) | BOX(1;0423): 3 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨1·0423⟩ : Complete 4 → ⟪ (Sb0-1-2-3 ∷ Bx1-0423 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0423 ∷ Sb0-1-2-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨1·0423⟩ c4 = run b0
  where
  b0 : Chain (Sb0-1-2-3 ∷ Bx1-0423 ∷ []) (Bx1-0423 ∷ Sb0-1-2-3 ∷ [])
  b0 = at 0 1 (CS12 ∷ []) (refl) ▸
       at 0 2 (Bx1-0423 ∷ CS12 ∷ []) (lem-auto-CS01-∣-BOX⟨0·2314⟩-at0112203443 c4) ▸
       at 1 1 (Sb0-1-2-3 ∷ []) (refl) ▸ done


-- sym23 @0112203443: 5 steps
lem-sym23-at0112203443 : Complete 4 → ⟪ (Bx1-2043 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2403 ∷ []) ⟫ʷ
lem-sym23-at0112203443 c4 = run b0
  where
  b0 : Chain (Bx1-2043 ∷ []) (Bx1-2403 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-2143 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·2043⟩ c4) ▸
       at 1 1 (Bx0-2413 ∷ []) (lem-sym23-at12213443 c4) ▸
       at 0 2 (Bx1-2403 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·2413⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- beta-T @0112243043: 8 steps
lem-beta-T-at0112243043 : Complete 4 → ⟪ (Bx1-2403 ∷ []) ⟫ʷ ≈ ⟪ (Toff124 ∷ CCZ013 ∷ Toff124 ∷ CCZ013 ∷ []) ⟫ʷ
lem-beta-T-at0112243043 c4 = run b0
  where
  b0 : Chain (Bx1-2403 ∷ []) (Toff124 ∷ CCZ013 ∷ Toff124 ∷ CCZ013 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-2413 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·2403⟩ c4) ▸
       at 1 1 (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-beta-T-at12243143 c4) ▸
       at 0 2 (Toff124 ∷ Sw01 ∷ []) (lem-nat-0-TOFF024 c4) ▸
       at 1 2 (CCZ013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff124 ∷ Sw01 ∷ []) (lem-nat-0-TOFF024 c4) ▸
       at 3 2 (CCZ013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | CCZ342 @01102332: 7 steps
lem-auto-CCZ012-∣-CCZ342-at01102332 : Complete 4 → ⟪ (CCZ013 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ CCZ013 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-CCZ342-at01102332 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ013 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 1 2 (CCZ234 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-CCZ342-at2332 c4) ▸
       at 0 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 1 2 (CCZ013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym23 @0112243043: 5 steps
lem-sym23-at0112243043 : Complete 4 → ⟪ (Bx1-2403 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2043 ∷ []) ⟫ʷ
lem-sym23-at0112243043 c4 = run b0
  where
  b0 : Chain (Bx1-2403 ∷ []) (Bx1-2043 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-2413 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·2403⟩ c4) ▸
       at 1 1 (Bx0-2143 ∷ []) (lem-sym23-at12243143 c4) ▸
       at 0 2 (Bx1-2043 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·2143⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | BOX(1;0243): 31 steps
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0243⟩ : Complete 4 → ⟪ (Bx0-1234 ∷ Bx1-0243 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0243 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0243⟩ c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (Bx0-1234 ∷ Bx1-0243 ∷ []) (Toff124 ∷ Bx0-2413 ∷ CCZ234 ∷ CCZ013 ∷ Toff124 ∷ CCZ013 ∷ [])
  b0 = at 1 1 (Bx1-2043 ∷ []) (lem-sym12-at01103443 c4) ▸
       at 1 1 (Bx1-2403 ∷ []) (lem-sym23-at0112203443 c4) ▸
       at 1 1 (Toff124 ∷ CCZ013 ∷ Toff124 ∷ CCZ013 ∷ []) (lem-beta-T-at0112243043 c4) ▸
       at 0 0 (Toff124 ∷ Toff124 ∷ []) (lw0 c4 [] (Toff124 ∷ Toff124 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Bx0-2134 ∷ []) (lem-sym12 c4) ▸
       at 2 1 (Bx0-2143 ∷ []) (lem-sym34-at1221 c4) ▸
       at 2 1 (Bx0-2413 ∷ []) (lem-sym23-at12213443 c4) ▸
       at 1 3 (Bx0-2413 ∷ CCZ234 ∷ []) (lem-T312-beta-at12243143 c4) ▸ done

  b1 : Chain (Toff124 ∷ Bx0-2413 ∷ CCZ234 ∷ CCZ013 ∷ Toff124 ∷ CCZ013 ∷ []) (Toff124 ∷ CCZ234 ∷ CCZ013 ∷ Toff124 ∷ Toff124 ∷ Bx0-2143 ∷ Toff124 ∷ CCZ013 ∷ [])
  b1 = at 1 1 (Bx0-2143 ∷ []) (lem-sym23-at12243143 c4) ▸
       at 1 1 (Bx0-2134 ∷ []) (lem-sym34-at12213443 c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym12-at1221 c4) ▸
       at 1 2 (CCZ234 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ243 c4) ▸
       at 2 2 (CCZ013 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ103 c4) ▸
       at 3 0 (Toff124 ∷ Toff124 ∷ []) (lw0 c4 [] (Toff124 ∷ Toff124 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Bx0-2134 ∷ []) (lem-sym12 c4) ▸
       at 5 1 (Bx0-2143 ∷ []) (lem-sym34-at1221 c4) ▸ done

  b2 : Chain (Toff124 ∷ CCZ234 ∷ CCZ013 ∷ Toff124 ∷ Toff124 ∷ Bx0-2143 ∷ Toff124 ∷ CCZ013 ∷ []) (CCZ234 ∷ Toff124 ∷ CCZ013 ∷ Toff124 ∷ CCZ234 ∷ CCZ013 ∷ Bx0-1234 ∷ [])
  b2 = at 5 1 (Bx0-2413 ∷ []) (lem-sym23-at12213443 c4) ▸
       at 4 3 (Bx0-2413 ∷ CCZ234 ∷ []) (lem-T312-beta-at12243143 c4) ▸
       at 4 1 (Bx0-2143 ∷ []) (lem-sym23-at12243143 c4) ▸
       at 4 1 (Bx0-2134 ∷ []) (lem-sym34-at12213443 c4) ▸
       at 4 1 (Bx0-1234 ∷ []) (lem-sym12-at1221 c4) ▸
       at 4 2 (CCZ234 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ243 c4) ▸
       at 5 2 (CCZ013 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ103 c4) ▸
       at 0 2 (CCZ234 ∷ Toff124 ∷ []) (lw0 c4 (Toff124 ∷ CCZ234 ∷ []) (CCZ234 ∷ Toff124 ∷ []) tt tt Eq.refl) ▸ done

  b3 : Chain (CCZ234 ∷ Toff124 ∷ CCZ013 ∷ Toff124 ∷ CCZ234 ∷ CCZ013 ∷ Bx0-1234 ∷ []) (Bx1-0243 ∷ Bx0-1234 ∷ [])
  b3 = at 3 2 (CCZ234 ∷ Toff124 ∷ []) (lw0 c4 (Toff124 ∷ CCZ234 ∷ []) (CCZ234 ∷ Toff124 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ234 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-CCZ342-at01102332 c4) ▸
       at 1 2 (CCZ234 ∷ Toff124 ∷ []) (lw0 c4 (Toff124 ∷ CCZ234 ∷ []) (CCZ234 ∷ Toff124 ∷ []) tt tt Eq.refl) ▸
       at 0 2 [] (lw0 c4 (CCZ234 ∷ CCZ234 ∷ []) [] tt tt Eq.refl) ▸
       at 0 4 (Bx1-2403 ∷ []) (sym (lem-beta-T-at0112243043 c4)) ▸
       at 0 1 (Bx1-2043 ∷ []) (lem-sym23-at0112243043 c4) ▸
       at 0 1 (Bx1-0243 ∷ []) (lem-sym12-at0112203443 c4) ▸ done


-- auto CCZ012 | TOFF301 SBOXd(2;4;3;1): 2 steps
lem-auto-CCZ012-∣-TOFF301-SBOXd⟨2·4·3·1⟩ : Complete 4 → ⟪ (CCZ012 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ Sb⁻2-4-3-1 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-TOFF301-SBOXd⟨2·4·3·1⟩ c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) (Toff301 ∷ Sb⁻2-4-3-1 ∷ CCZ012 ∷ [])
  b0 = at 0 2 (Toff301 ∷ CCZ012 ∷ []) (lw4 c4 (CCZ012 ∷ Toff301 ∷ []) (Toff301 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻2-4-3-1 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CS • CS • CS)) ▸ done


-- auto SBOXd(0;1;2;3) | BOX(1;0423) @2332: 7 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨1·0423⟩-at2332 : Complete 4 → ⟪ (Sb⁻0-1-3-2 ∷ Bx1-0432 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0432 ∷ Sb⁻0-1-3-2 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨1·0423⟩-at2332 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-3-2 ∷ Bx1-0432 ∷ []) (Bx1-0432 ∷ Sb⁻0-1-3-2 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-2-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·3·2⟩ c4) ▸
       at 2 2 (Bx1-0423 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·0432⟩ c4) ▸
       at 1 2 (Bx1-0423 ∷ Sb⁻0-1-2-3 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨1·0423⟩ c4) ▸
       at 0 2 (Bx1-0432 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·0423⟩ c4) ▸
       at 1 2 (Sb⁻0-1-3-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·2·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;2;3) | BOX(1;0423) @243243: 7 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨1·0423⟩-at243243 : Complete 4 → ⟪ (Sb⁻0-1-4-2 ∷ Bx1-0342 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0342 ∷ Sb⁻0-1-4-2 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨1·0423⟩-at243243 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-4-2 ∷ Bx1-0342 ∷ []) (Bx1-0342 ∷ Sb⁻0-1-4-2 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-3-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·4·2⟩ c4) ▸
       at 2 2 (Bx1-0432 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·0342⟩ c4) ▸
       at 1 2 (Bx1-0432 ∷ Sb⁻0-1-3-2 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨1·0423⟩-at2332 c4) ▸
       at 0 2 (Bx1-0342 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·0432⟩ c4) ▸
       at 1 2 (Sb⁻0-1-4-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·3·2⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;2;3) | BOX(1;0423) @2442: 7 steps
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨1·0423⟩-at2442 : Complete 4 → ⟪ (Sb⁻0-1-4-3 ∷ Bx1-0243 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0243 ∷ Sb⁻0-1-4-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨1·0423⟩-at2442 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-4-3 ∷ Bx1-0243 ∷ []) (Bx1-0243 ∷ Sb⁻0-1-4-3 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-4-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·4·3⟩ c4) ▸
       at 2 2 (Bx1-0342 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·0243⟩ c4) ▸
       at 1 2 (Bx1-0342 ∷ Sb⁻0-1-4-2 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨1·0423⟩-at243243 c4) ▸
       at 0 2 (Bx1-0243 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·0342⟩ c4) ▸
       at 1 2 (Sb⁻0-1-4-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·4·2⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym34 @0112243043: 5 steps
lem-sym34-at0112243043 : Complete 4 → ⟪ (Bx1-2403 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2430 ∷ []) ⟫ʷ
lem-sym34-at0112243043 c4 = run b0
  where
  b0 : Chain (Bx1-2403 ∷ []) (Bx1-2430 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-2413 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·2403⟩ c4) ▸
       at 1 1 (Bx0-2431 ∷ []) (lem-sym34-at12243143 c4) ▸
       at 0 2 (Bx1-2430 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·2431⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym23 @01122440: 5 steps
lem-sym23-at01122440 : Complete 4 → ⟪ (Bx1-2430 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2340 ∷ []) ⟫ʷ
lem-sym23-at01122440 c4 = run b0
  where
  b0 : Chain (Bx1-2430 ∷ []) (Bx1-2340 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-2431 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·2430⟩ c4) ▸
       at 1 1 (Bx0-2341 ∷ []) (lem-sym23-at122441 c4) ▸
       at 0 2 (Bx1-2340 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·2341⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- T312-beta @0112233440: 8 steps
lem-T312-beta-at0112233440 : Complete 4 → ⟪ (Toff423 ∷ Bx1-2340 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2340 ∷ CCZ023 ∷ []) ⟫ʷ
lem-T312-beta-at0112233440 c4 = run b0
  where
  b0 : Chain (Toff423 ∷ Bx1-2340 ∷ Toff423 ∷ []) (Bx1-2340 ∷ CCZ023 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff423 ∷ Sw01 ∷ []) (c₂ (Swap) (Toffᵗ)) ▸
       at 2 2 (Bx0-2341 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·2340⟩ c4) ▸
       at 3 2 (Toff423 ∷ Sw01 ∷ []) (c₂ (Swap) (Toffᵗ)) ▸
       at 1 3 (Bx0-2341 ∷ CCZ123 ∷ []) (lem-T312-beta-at12233441 c4) ▸
       at 0 2 (Bx1-2340 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·2341⟩ c4) ▸
       at 1 2 (CCZ023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ123 ∷ []) (CCZ023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym23 @0112233440: 5 steps
lem-sym23-at0112233440 : Complete 4 → ⟪ (Bx1-2340 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2430 ∷ []) ⟫ʷ
lem-sym23-at0112233440 c4 = run b0
  where
  b0 : Chain (Bx1-2340 ∷ []) (Bx1-2430 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-2341 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·2340⟩ c4) ▸
       at 1 1 (Bx0-2431 ∷ []) (lem-sym23-at12233441 c4) ▸
       at 0 2 (Bx1-2430 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·2431⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym34 @01122440: 5 steps
lem-sym34-at01122440 : Complete 4 → ⟪ (Bx1-2430 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2403 ∷ []) ⟫ʷ
lem-sym34-at01122440 c4 = run b0
  where
  b0 : Chain (Bx1-2430 ∷ []) (Bx1-2403 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-2431 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·2430⟩ c4) ▸
       at 1 1 (Bx0-2413 ∷ []) (lem-sym34-at122441 c4) ▸
       at 0 2 (Bx1-2403 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·2413⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;2;3) | BOX(1;0423) @2332: 7 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨1·0423⟩-at2332 : Complete 4 → ⟪ (Sb0-1-3-2 ∷ Bx1-0432 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0432 ∷ Sb0-1-3-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨1·0423⟩-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-3-2 ∷ Bx1-0432 ∷ []) (Bx1-0432 ∷ Sb0-1-3-2 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-2-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·3·2⟩ c4) ▸
       at 2 2 (Bx1-0423 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·0432⟩ c4) ▸
       at 1 2 (Bx1-0423 ∷ Sb0-1-2-3 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨1·0423⟩ c4) ▸
       at 0 2 (Bx1-0432 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·0423⟩ c4) ▸
       at 1 2 (Sb0-1-3-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·2·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;2;3) | BOX(1;0423) @243243: 7 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨1·0423⟩-at243243 : Complete 4 → ⟪ (Sb0-1-4-2 ∷ Bx1-0342 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0342 ∷ Sb0-1-4-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨1·0423⟩-at243243 c4 = run b0
  where
  b0 : Chain (Sb0-1-4-2 ∷ Bx1-0342 ∷ []) (Bx1-0342 ∷ Sb0-1-4-2 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-3-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·4·2⟩ c4) ▸
       at 2 2 (Bx1-0432 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·0342⟩ c4) ▸
       at 1 2 (Bx1-0432 ∷ Sb0-1-3-2 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨1·0423⟩-at2332 c4) ▸
       at 0 2 (Bx1-0342 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·0432⟩ c4) ▸
       at 1 2 (Sb0-1-4-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·3·2⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;2;3) | BOX(1;0423) @2442: 7 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨1·0423⟩-at2442 : Complete 4 → ⟪ (Sb0-1-4-3 ∷ Bx1-0243 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0243 ∷ Sb0-1-4-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨1·0423⟩-at2442 c4 = run b0
  where
  b0 : Chain (Sb0-1-4-3 ∷ Bx1-0243 ∷ []) (Bx1-0243 ∷ Sb0-1-4-3 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-4-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·4·3⟩ c4) ▸
       at 2 2 (Bx1-0342 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·0243⟩ c4) ▸
       at 1 2 (Bx1-0342 ∷ Sb0-1-4-2 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨1·0423⟩-at243243 c4) ▸
       at 0 2 (Bx1-0243 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·0342⟩ c4) ▸
       at 1 2 (Sb0-1-4-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·4·2⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | TOFF301 SBOXd(2;4;3;1) @3443: 9 steps
lem-auto-CCZ012-∣-TOFF301-SBOXd⟨2·4·3·1⟩-at3443 : Complete 4 → ⟪ (CCZ012 ∷ Toff401 ∷ Sb⁻2-3-4-1 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ Sb⁻2-3-4-1 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-TOFF301-SBOXd⟨2·4·3·1⟩-at3443 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ012 ∷ Toff401 ∷ Sb⁻2-3-4-1 ∷ []) (Toff401 ∷ Sb⁻2-3-4-1 ∷ CCZ012 ∷ Sw34 ∷ Sw34 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 2 2 (Toff301 ∷ Sw34 ∷ []) (lem-nat-3-TOFF401 c4) ▸
       at 3 2 (Sb⁻2-4-3-1 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨2·3·4·1⟩ c4) ▸
       at 1 3 (Toff301 ∷ Sb⁻2-4-3-1 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-TOFF301-SBOXd⟨2·4·3·1⟩ c4) ▸
       at 0 2 (Toff401 ∷ Sw34 ∷ []) (lem-nat-3-TOFF301 c4) ▸
       at 1 2 (Sb⁻2-3-4-1 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨2·4·3·1⟩ c4) ▸
       at 2 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸ done

  b1 : Chain (Toff401 ∷ Sb⁻2-3-4-1 ∷ CCZ012 ∷ Sw34 ∷ Sw34 ∷ []) (Toff401 ∷ Sb⁻2-3-4-1 ∷ CCZ012 ∷ [])
  b1 = at 3 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | TOFF301 SBOXd(2;4;3;1) @12213443: 9 steps
lem-auto-CCZ012-∣-TOFF301-SBOXd⟨2·4·3·1⟩-at12213443 : Complete 4 → ⟪ (CCZ012 ∷ Toff402 ∷ Sb⁻1-3-4-2 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ Sb⁻1-3-4-2 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-TOFF301-SBOXd⟨2·4·3·1⟩-at12213443 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ012 ∷ Toff402 ∷ Sb⁻1-3-4-2 ∷ []) (Toff402 ∷ Sb⁻1-3-4-2 ∷ CCZ012 ∷ Sw12 ∷ Sw12 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff401 ∷ Sw12 ∷ []) (lem-nat-1-TOFF402 c4) ▸
       at 3 2 (Sb⁻2-3-4-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·3·4·2⟩ c4) ▸
       at 1 3 (Toff401 ∷ Sb⁻2-3-4-1 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-TOFF301-SBOXd⟨2·4·3·1⟩-at3443 c4) ▸
       at 0 2 (Toff402 ∷ Sw12 ∷ []) (lem-nat-1-TOFF401 c4) ▸
       at 1 2 (Sb⁻1-3-4-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·3·4·1⟩ c4) ▸
       at 2 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Toff402 ∷ Sb⁻1-3-4-2 ∷ CCZ012 ∷ Sw12 ∷ Sw12 ∷ []) (Toff402 ∷ Sb⁻1-3-4-2 ∷ CCZ012 ∷ [])
  b1 = at 3 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | TOFF301 SBOXd(2;4;3;1) @13213442: 9 steps
lem-auto-CCZ012-∣-TOFF301-SBOXd⟨2·4·3·1⟩-at13213442 : Complete 4 → ⟪ (CCZ013 ∷ Toff403 ∷ Sb⁻1-2-4-3 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ Sb⁻1-2-4-3 ∷ CCZ013 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-TOFF301-SBOXd⟨2·4·3·1⟩-at13213442 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ013 ∷ Toff403 ∷ Sb⁻1-2-4-3 ∷ []) (Toff403 ∷ Sb⁻1-2-4-3 ∷ CCZ013 ∷ Sw23 ∷ Sw23 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 2 2 (Toff402 ∷ Sw23 ∷ []) (lem-nat-2-TOFF403 c4) ▸
       at 3 2 (Sb⁻1-3-4-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·2·4·3⟩ c4) ▸
       at 1 3 (Toff402 ∷ Sb⁻1-3-4-2 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-TOFF301-SBOXd⟨2·4·3·1⟩-at12213443 c4) ▸
       at 0 2 (Toff403 ∷ Sw23 ∷ []) (lem-nat-2-TOFF402 c4) ▸
       at 1 2 (Sb⁻1-2-4-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·3·4·2⟩ c4) ▸
       at 2 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸ done

  b1 : Chain (Toff403 ∷ Sb⁻1-2-4-3 ∷ CCZ013 ∷ Sw23 ∷ Sw23 ∷ []) (Toff403 ∷ Sb⁻1-2-4-3 ∷ CCZ013 ∷ [])
  b1 = at 3 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | TOFF301 SBOXd(2;4;3;1) @0113203442: 9 steps
lem-auto-CCZ012-∣-TOFF301-SBOXd⟨2·4·3·1⟩-at0113203442 : Complete 4 → ⟪ (CCZ013 ∷ Toff413 ∷ Sb⁻0-2-4-3 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ Sb⁻0-2-4-3 ∷ CCZ013 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-TOFF301-SBOXd⟨2·4·3·1⟩-at0113203442 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ013 ∷ Toff413 ∷ Sb⁻0-2-4-3 ∷ []) (Toff413 ∷ Sb⁻0-2-4-3 ∷ CCZ013 ∷ Sw01 ∷ Sw01 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff403 ∷ Sw01 ∷ []) (lem-nat-0-TOFF413 c4) ▸
       at 3 2 (Sb⁻1-2-4-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨0·2·4·3⟩ c4) ▸
       at 1 3 (Toff403 ∷ Sb⁻1-2-4-3 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-TOFF301-SBOXd⟨2·4·3·1⟩-at13213442 c4) ▸
       at 0 2 (Toff413 ∷ Sw01 ∷ []) (lem-nat-0-TOFF403 c4) ▸
       at 1 2 (Sb⁻0-2-4-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·2·4·3⟩ c4) ▸
       at 2 2 (CCZ013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Toff413 ∷ Sb⁻0-2-4-3 ∷ CCZ013 ∷ Sw01 ∷ Sw01 ∷ []) (Toff413 ∷ Sb⁻0-2-4-3 ∷ CCZ013 ∷ [])
  b1 = at 3 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | TOFF301 SBOXd(2;4;3;1) @0213203441: 9 steps
lem-auto-CCZ012-∣-TOFF301-SBOXd⟨2·4·3·1⟩-at0213203441 : Complete 4 → ⟪ (CCZ023 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ Sb⁻0-1-4-3 ∷ CCZ023 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-TOFF301-SBOXd⟨2·4·3·1⟩-at0213203441 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ023 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (Toff423 ∷ Sb⁻0-1-4-3 ∷ CCZ023 ∷ Sw12 ∷ Sw12 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 2 2 (Toff413 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff423 ∷ []) (Toff413 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Sb⁻0-2-4-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨0·1·4·3⟩ c4) ▸
       at 1 3 (Toff413 ∷ Sb⁻0-2-4-3 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-TOFF301-SBOXd⟨2·4·3·1⟩-at0113203442 c4) ▸
       at 0 2 (Toff423 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff413 ∷ []) (Toff423 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-4-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨0·2·4·3⟩ c4) ▸
       at 2 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸ done

  b1 : Chain (Toff423 ∷ Sb⁻0-1-4-3 ∷ CCZ023 ∷ Sw12 ∷ Sw12 ∷ []) (Toff423 ∷ Sb⁻0-1-4-3 ∷ CCZ023 ∷ [])
  b1 = at 3 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | BOX(1;0243): 31 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨1·0243⟩ : Complete 4 → ⟪ (Sb0-1-23-4 ∷ Bx1-0243 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0243 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-BOX⟨1·0243⟩ c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (Sb0-1-23-4 ∷ Bx1-0243 ∷ []) (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Bx1-2340 ∷ CCZ023 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 4 2 (Bx1-0243 ∷ Sb⁻0-1-4-3 ∷ []) (lem-auto-SBOXd⟨0·1·2·3⟩-∣-BOX⟨1·0423⟩-at2442 c4) ▸
       at 5 0 (Toff423 ∷ Toff423 ∷ []) (lw0 c4 [] (Toff423 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Bx1-2043 ∷ []) (lem-sym12-at01103443 c4) ▸
       at 4 1 (Bx1-2403 ∷ []) (lem-sym23-at0112203443 c4) ▸
       at 4 1 (Bx1-2430 ∷ []) (lem-sym34-at0112243043 c4) ▸
       at 4 1 (Bx1-2340 ∷ []) (lem-sym23-at01122440 c4) ▸
       at 3 3 (Bx1-2340 ∷ CCZ023 ∷ []) (lem-T312-beta-at0112233440 c4) ▸ done

  b1 : Chain (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Bx1-2340 ∷ CCZ023 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (Bx0-1234 ∷ Toff423 ∷ Bx1-2403 ∷ Toff423 ∷ Toff423 ∷ Sb0-1-4-3 ∷ CCZ023 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ [])
  b1 = at 3 1 (Bx1-2430 ∷ []) (lem-sym23-at0112233440 c4) ▸
       at 3 1 (Bx1-2403 ∷ []) (lem-sym34-at01122440 c4) ▸
       at 3 1 (Bx1-2043 ∷ []) (lem-sym23-at0112243043 c4) ▸
       at 3 1 (Bx1-0243 ∷ []) (lem-sym12-at0112203443 c4) ▸
       at 2 2 (Bx1-0243 ∷ Sb0-1-4-3 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-BOX⟨1·0423⟩-at2442 c4) ▸
       at 3 0 (Toff423 ∷ Toff423 ∷ []) (lw0 c4 [] (Toff423 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Bx1-2043 ∷ []) (lem-sym12-at01103443 c4) ▸
       at 2 1 (Bx1-2403 ∷ []) (lem-sym23-at0112203443 c4) ▸ done

  b2 : Chain (Bx0-1234 ∷ Toff423 ∷ Bx1-2403 ∷ Toff423 ∷ Toff423 ∷ Sb0-1-4-3 ∷ CCZ023 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (Bx1-0243 ∷ Bx0-1234 ∷ CCZ023 ∷ Toff423 ∷ Sb0-1-4-3 ∷ CCZ023 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ [])
  b2 = at 2 1 (Bx1-2430 ∷ []) (lem-sym34-at0112243043 c4) ▸
       at 2 1 (Bx1-2340 ∷ []) (lem-sym23-at01122440 c4) ▸
       at 1 3 (Bx1-2340 ∷ CCZ023 ∷ []) (lem-T312-beta-at0112233440 c4) ▸
       at 1 1 (Bx1-2430 ∷ []) (lem-sym23-at0112233440 c4) ▸
       at 1 1 (Bx1-2403 ∷ []) (lem-sym34-at01122440 c4) ▸
       at 1 1 (Bx1-2043 ∷ []) (lem-sym23-at0112243043 c4) ▸
       at 1 1 (Bx1-0243 ∷ []) (lem-sym12-at0112203443 c4) ▸
       at 0 2 (Bx1-0243 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-BOX⟨1·0243⟩ c4) ▸ done

  b3 : Chain (Bx1-0243 ∷ Bx0-1234 ∷ CCZ023 ∷ Toff423 ∷ Sb0-1-4-3 ∷ CCZ023 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (Bx1-0243 ∷ Sb0-1-23-4 ∷ [])
  b3 = at 5 3 (Toff423 ∷ Sb⁻0-1-4-3 ∷ CCZ023 ∷ []) (lem-auto-CCZ012-∣-TOFF301-SBOXd⟨2·4·3·1⟩-at0213203441 c4) ▸
       at 2 2 (Toff423 ∷ CCZ023 ∷ []) (pw1 c4 (CCZ023 ∷ Toff423 ∷ []) (Toff423 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Sb0-1-4-3 ∷ CCZ023 ∷ []) (lem-comm-CCZ023-SBOX⟨0·1·4·3⟩ c4) ▸
       at 4 2 (Toff423 ∷ CCZ023 ∷ []) (pw1 c4 (CCZ023 ∷ Toff423 ∷ []) (Toff423 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Sb⁻0-1-4-3 ∷ CCZ023 ∷ []) (lem-comm-CCZ023-SBOXd⟨0·1·4·3⟩ c4) ▸
       at 6 2 [] (lw4 c4 (CCZ023 ∷ CCZ023 ∷ []) [] tt tt Eq.refl) ▸
       at 1 5 (Sb0-1-23-4 ∷ []) (refl) ▸ done


-- Cz-beta @1221: 7 steps
lem-Cz-beta-at1221 : Complete 4 → ⟪ (CCZ012 ∷ Bx0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ CCZ012 ∷ []) ⟫ʷ
lem-Cz-beta-at1221 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Bx0-2134 ∷ []) (Bx0-2134 ∷ CCZ012 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-1234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2134⟩ c4) ▸
       at 1 2 (Bx0-1234 ∷ CCZ012 ∷ []) (lem-Cz-beta c4) ▸
       at 0 2 (Bx0-2134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1234⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | BOX(0;3421): 11 steps
lem-auto-CCZ012-∣-BOX⟨0·3421⟩ : Complete 4 → ⟪ (CCZ012 ∷ Bx0-3421 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3421 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨0·3421⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ012 ∷ Bx0-3421 ∷ []) (Bx0-2341 ∷ CCZ012 ∷ [])
  b0 = at 0 1 (CCZ012 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Bx0-3241 ∷ []) (lem-sym23-at13243241 c4) ▸
       at 1 1 (Bx0-3214 ∷ []) (lem-sym34-at133441 c4) ▸
       at 1 1 (Bx0-2314 ∷ []) (lem-sym12-at1331 c4) ▸
       at 1 1 (Bx0-2134 ∷ []) (lem-sym23-at122331 c4) ▸
       at 0 2 (Bx0-2134 ∷ CCZ012 ∷ []) (lem-Cz-beta-at1221 c4) ▸
       at 0 1 (Bx0-2314 ∷ []) (lem-sym23-at1221 c4) ▸
       at 0 1 (Bx0-2341 ∷ []) (lem-sym34-at122331 c4) ▸ done

  b1 : Chain (Bx0-2341 ∷ CCZ012 ∷ []) (Bx0-3421 ∷ CCZ012 ∷ [])
  b1 = at 0 1 (Bx0-3241 ∷ []) (lem-sym12-at12233441 c4) ▸
       at 0 1 (Bx0-3421 ∷ []) (lem-sym23-at133441 c4) ▸
       at 1 1 (CCZ012 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸ done


-- sym12 @011330: 5 steps
lem-sym12-at011330 : Complete 4 → ⟪ (Bx1-3204 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2304 ∷ []) ⟫ʷ
lem-sym12-at011330 c4 = run b0
  where
  b0 : Chain (Bx1-3204 ∷ []) (Bx1-2304 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-3214 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·3204⟩ c4) ▸
       at 1 1 (Bx0-2314 ∷ []) (lem-sym12-at1331 c4) ▸
       at 0 2 (Bx1-2304 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·2314⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- Cz-beta @011220: 7 steps
lem-Cz-beta-at011220 : Complete 4 → ⟪ (CCZ012 ∷ Bx1-2034 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2034 ∷ CCZ012 ∷ []) ⟫ʷ
lem-Cz-beta-at011220 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Bx1-2034 ∷ []) (Bx1-2034 ∷ CCZ012 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-2134 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·2034⟩ c4) ▸
       at 1 2 (Bx0-2134 ∷ CCZ012 ∷ []) (lem-Cz-beta-at1221 c4) ▸
       at 0 2 (Bx1-2034 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·2134⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym12 @0112233440: 5 steps
lem-sym12-at0112233440 : Complete 4 → ⟪ (Bx1-2340 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3240 ∷ []) ⟫ʷ
lem-sym12-at0112233440 c4 = run b0
  where
  b0 : Chain (Bx1-2340 ∷ []) (Bx1-3240 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-2341 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·2340⟩ c4) ▸
       at 1 1 (Bx0-3241 ∷ []) (lem-sym12-at12233441 c4) ▸
       at 0 2 (Bx1-3240 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·3241⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | BOX(1;3420): 11 steps
lem-auto-CCZ012-∣-BOX⟨1·3420⟩ : Complete 4 → ⟪ (CCZ012 ∷ Bx1-3420 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3420 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨1·3420⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ012 ∷ Bx1-3420 ∷ []) (Bx1-2340 ∷ CCZ012 ∷ [])
  b0 = at 0 1 (CCZ012 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Bx1-3240 ∷ []) (lem-sym23-at0113243240 c4) ▸
       at 1 1 (Bx1-3204 ∷ []) (lem-sym34-at01133440 c4) ▸
       at 1 1 (Bx1-2304 ∷ []) (lem-sym12-at011330 c4) ▸
       at 1 1 (Bx1-2034 ∷ []) (lem-sym23-at01122330 c4) ▸
       at 0 2 (Bx1-2034 ∷ CCZ012 ∷ []) (lem-Cz-beta-at011220 c4) ▸
       at 0 1 (Bx1-2304 ∷ []) (lem-sym23-at011220 c4) ▸
       at 0 1 (Bx1-2340 ∷ []) (lem-sym34-at01122330 c4) ▸ done

  b1 : Chain (Bx1-2340 ∷ CCZ012 ∷ []) (Bx1-3420 ∷ CCZ012 ∷ [])
  b1 = at 0 1 (Bx1-3240 ∷ []) (lem-sym12-at0112233440 c4) ▸
       at 0 1 (Bx1-3420 ∷ []) (lem-sym23-at01133440 c4) ▸
       at 1 1 (CCZ012 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | SBOX(1;0;3;4): 5 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩ : Complete 4 → ⟪ (Sb0-1-23-4 ∷ Sb1-0-3-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-3-4 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩ c4 = run b0
  where
  b0 : Chain (Sb0-1-23-4 ∷ Sb1-0-3-4 ∷ []) (Sb1-0-3-4 ∷ Sb0-1-23-4 ∷ [])
  b0 = at 1 1 (CS03 ∷ []) (refl) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (CS03 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS02-at2332 c4) ▸
       at 1 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 0 1 (Sb1-0-3-4 ∷ []) (refl) ▸ done


-- auto SBOX(0;1;23;4) | SBOXd(1;0;3;4): 5 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩ : Complete 4 → ⟪ (Sb0-1-23-4 ∷ Sb⁻1-0-3-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-3-4 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩ c4 = run b0
  where
  b0 : Chain (Sb0-1-23-4 ∷ Sb⁻1-0-3-4 ∷ []) (Sb⁻1-0-3-4 ∷ Sb0-1-23-4 ∷ [])
  b0 = at 1 1 (CS03⁻ ∷ []) (refl) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (CS03⁻ ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd02-at2332 c4) ▸
       at 1 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸
       at 0 1 (Sb⁻1-0-3-4 ∷ []) (refl) ▸ done


-- auto SBOX(0;1;23;4) | CCZ143 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ143-at2332 : Complete 4 → ⟪ (Sb0-1-32-4 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ143-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 1 2 (CCZ134 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ143 c4) ▸
       at 0 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CCZ143 @243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ143-at243243 : Complete 4 → ⟪ (Sb0-1-42-3 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ143-at243243 c4 = run b0
  where
  b0 : Chain (Sb0-1-42-3 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sb0-1-42-3 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·42·3⟩ c4) ▸
       at 2 2 (CCZ124 ∷ Sw34 ∷ []) (lem-nat-3-CCZ123 c4) ▸
       at 1 2 (CCZ124 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ143-at2332 c4) ▸
       at 0 2 (CCZ123 ∷ Sw34 ∷ []) (lem-nat-3-CCZ124 c4) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CCZ143 @0110243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ143-at0110243243 : Complete 4 → ⟪ (Sb1-0-42-3 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ143-at0110243243 c4 = run b0
  where
  b0 : Chain (Sb1-0-42-3 ∷ CCZ023 ∷ []) (CCZ023 ∷ Sb1-0-42-3 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·42·3⟩ c4) ▸
       at 2 2 (CCZ123 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ023 ∷ []) (CCZ123 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ123 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ143-at243243 c4) ▸
       at 0 2 (CCZ023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ123 ∷ []) (CCZ023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CCZ143 @0210243143: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ143-at0210243143 : Complete 4 → ⟪ (Sb2-0-41-3 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ143-at0210243143 c4 = run b0
  where
  b0 : Chain (Sb2-0-41-3 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sb2-0-41-3 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·41·3⟩ c4) ▸
       at 2 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 1 2 (CCZ023 ∷ Sb1-0-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ143-at0110243243 c4) ▸
       at 0 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 1 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | SBOX(1;0;3;4) @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at2332 : Complete 4 → ⟪ (Sb0-1-32-4 ∷ Sb1-0-2-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-2-4 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ Sb1-0-2-4 ∷ []) (Sb1-0-2-4 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 (Sb1-0-3-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·2·4⟩ c4) ▸
       at 1 2 (Sb1-0-3-4 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩ c4) ▸
       at 0 2 (Sb1-0-2-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·3·4⟩ c4) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | SBOX(1;0;3;4) @243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at243243 : Complete 4 → ⟪ (Sb0-1-42-3 ∷ Sb1-0-2-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-2-3 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at243243 c4 = run b0
  where
  b0 : Chain (Sb0-1-42-3 ∷ Sb1-0-2-3 ∷ []) (Sb1-0-2-3 ∷ Sb0-1-42-3 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·42·3⟩ c4) ▸
       at 2 2 (Sb1-0-2-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨1·0·2·3⟩ c4) ▸
       at 1 2 (Sb1-0-2-4 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at2332 c4) ▸
       at 0 2 (Sb1-0-2-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨1·0·2·4⟩ c4) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | SBOX(1;0;3;4) @0110243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at0110243243 : Complete 4 → ⟪ (Sb1-0-42-3 ∷ Sb0-1-2-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-2-3 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at0110243243 c4 = run b0
  where
  b0 : Chain (Sb1-0-42-3 ∷ Sb0-1-2-3 ∷ []) (Sb0-1-2-3 ∷ Sb1-0-42-3 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·42·3⟩ c4) ▸
       at 2 2 (Sb1-0-2-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·2·3⟩ c4) ▸
       at 1 2 (Sb1-0-2-3 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at243243 c4) ▸
       at 0 2 (Sb0-1-2-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·2·3⟩ c4) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | SBOX(1;0;3;4) @0210243143: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at0210243143 : Complete 4 → ⟪ (Sb2-0-41-3 ∷ Sb0-2-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-1-3 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at0210243143 c4 = run b0
  where
  b0 : Chain (Sb2-0-41-3 ∷ Sb0-2-1-3 ∷ []) (Sb0-2-1-3 ∷ Sb2-0-41-3 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·41·3⟩ c4) ▸
       at 2 2 (Sb0-1-2-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·1·3⟩ c4) ▸
       at 1 2 (Sb0-1-2-3 ∷ Sb1-0-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at0110243243 c4) ▸
       at 0 2 (Sb0-2-1-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·2·3⟩ c4) ▸
       at 1 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | SBOXd(1;0;3;4) @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at2332 : Complete 4 → ⟪ (Sb0-1-32-4 ∷ Sb⁻1-0-2-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-2-4 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ Sb⁻1-0-2-4 ∷ []) (Sb⁻1-0-2-4 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 (Sb⁻1-0-3-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·0·2·4⟩ c4) ▸
       at 1 2 (Sb⁻1-0-3-4 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩ c4) ▸
       at 0 2 (Sb⁻1-0-2-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·0·3·4⟩ c4) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | SBOXd(1;0;3;4) @243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at243243 : Complete 4 → ⟪ (Sb0-1-42-3 ∷ Sb⁻1-0-2-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-2-3 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at243243 c4 = run b0
  where
  b0 : Chain (Sb0-1-42-3 ∷ Sb⁻1-0-2-3 ∷ []) (Sb⁻1-0-2-3 ∷ Sb0-1-42-3 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·42·3⟩ c4) ▸
       at 2 2 (Sb⁻1-0-2-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨1·0·2·3⟩ c4) ▸
       at 1 2 (Sb⁻1-0-2-4 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at2332 c4) ▸
       at 0 2 (Sb⁻1-0-2-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨1·0·2·4⟩ c4) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | SBOXd(1;0;3;4) @0110243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at0110243243 : Complete 4 → ⟪ (Sb1-0-42-3 ∷ Sb⁻0-1-2-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-2-3 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at0110243243 c4 = run b0
  where
  b0 : Chain (Sb1-0-42-3 ∷ Sb⁻0-1-2-3 ∷ []) (Sb⁻0-1-2-3 ∷ Sb1-0-42-3 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·42·3⟩ c4) ▸
       at 2 2 (Sb⁻1-0-2-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨0·1·2·3⟩ c4) ▸
       at 1 2 (Sb⁻1-0-2-3 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at243243 c4) ▸
       at 0 2 (Sb⁻0-1-2-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·2·3⟩ c4) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | SBOXd(1;0;3;4) @0210243143: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at0210243143 : Complete 4 → ⟪ (Sb2-0-41-3 ∷ Sb⁻0-2-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-2-1-3 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at0210243143 c4 = run b0
  where
  b0 : Chain (Sb2-0-41-3 ∷ Sb⁻0-2-1-3 ∷ []) (Sb⁻0-2-1-3 ∷ Sb2-0-41-3 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·41·3⟩ c4) ▸
       at 2 2 (Sb⁻0-1-2-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨0·2·1·3⟩ c4) ▸
       at 1 2 (Sb⁻0-1-2-3 ∷ Sb1-0-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at0110243243 c4) ▸
       at 0 2 (Sb⁻0-2-1-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨0·1·2·3⟩ c4) ▸
       at 1 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done

