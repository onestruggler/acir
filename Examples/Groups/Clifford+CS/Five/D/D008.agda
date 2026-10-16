{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D008 where

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
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-BOXd-BOX ; lem-CS20-beta-c ; lem-K0-pass-c ; lem-K0-pass-ci ; lem-sym12 ; lem-sym23 ; lem-sym34)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-sym12-at1221 ; lem-sym34-at1221)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-F0d ; lem-sym23-at12213443 ; lem-sym23-at12243143 ; lem-sym23-at2332 ; lem-sym23-at243243 ; lem-sym23-at3443 ; lem-sym34-at12213443 ; lem-sym34-at3443)
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-CS20-beta-c-at1221 ; lem-SBsymd)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-CS12-beta-at2332 ; lem-CS12-beta-at243243 ; lem-CSd12-beta-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D006 using (lem-F5-CS01)
open import Examples.Groups.Clifford+CS.Five.D.D007 using (lem-CS12-beta-at12243143 ; lem-SBsym-at0113203442 ; lem-auto-BOX⟨0·1234⟩-∣-CSd41 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-CS41 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-CX34)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-2-TOFF301)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-2-TOFF201)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-0-TOFF403)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-0-TOFF413 ; lem-nat-1-TOFF401 ; lem-nat-2-TOFF402 ; lem-nat-3-TOFF301)
open import Examples.Groups.Clifford+CS.Five.D.R012 using (lem-nat-1-CS01 ; lem-nat-1-CS02)
open import Examples.Groups.Clifford+CS.Five.D.R013 using (lem-nat-2-CS12 ; lem-nat-2-CS13 ; lem-nat-2-TOFF403)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-nat-2-CS02 ; lem-nat-2-SBOX⟨0·1·23·4⟩ ; lem-nat-2-SBOX⟨0·1·32·4⟩ ; lem-nat-3-CS23 ; lem-nat-3-CS24)
open import Examples.Groups.Clifford+CS.Five.D.R017 using (lem-nat-1-TOFF402 ; lem-nat-3-TOFF401)
open import Examples.Groups.Clifford+CS.Five.D.R018 using (lem-nat-0-BOXd⟨0·1234⟩ ; lem-nat-0-BOXd⟨1·0234⟩ ; lem-nat-0-BOXd⟨4·0231⟩ ; lem-nat-0-SBOXd⟨0·1·23·4⟩ ; lem-nat-0-SBOXd⟨1·0·32·4⟩ ; lem-nat-0-SBOXd⟨4·0·23·1⟩ ; lem-nat-1-BOXd⟨1·0234⟩ ; lem-nat-1-BOXd⟨2·0134⟩ ; lem-nat-1-SBOXd⟨1·0·32·4⟩ ; lem-nat-1-SBOXd⟨2·0·13·4⟩ ; lem-nat-1-SBOXd⟨4·0·31·2⟩ ; lem-nat-2-BOXd⟨2·0134⟩ ; lem-nat-2-BOXd⟨3·0124⟩ ; lem-nat-2-SBOXd⟨0·1·23·4⟩ ; lem-nat-2-SBOXd⟨0·1·32·4⟩ ; lem-nat-2-SBOXd⟨1·0·23·4⟩ ; lem-nat-2-SBOXd⟨4·0·32·1⟩ ; lem-nat-3-BOXd⟨3·0124⟩ ; lem-nat-3-BOXd⟨4·0123⟩ ; lem-nat-3-SBOXd⟨2·0·14·3⟩ ; lem-nat-3-SBOXd⟨2·0·31·4⟩ ; lem-nat-3-SBOXd⟨3·0·41·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R019 using (lem-nat-0-BOXd⟨4·1230⟩ ; lem-nat-1-BOXd⟨4·0132⟩ ; lem-nat-1-BOXd⟨4·0231⟩ ; lem-nat-2-BOXd⟨4·0123⟩ ; lem-nat-2-BOXd⟨4·0132⟩ ; lem-nat-2-CS03)
-- auto SBOX(0;1;23;4) | CSd41: 9 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd41 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS14⁻ ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd41 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-1-23-4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 4 1 (CS14⁻ ∷ []) (refl) ▸
       at 4 2 (CS14⁻ ∷ CS14⁻ ∷ []) (lw0 c4 (CS14⁻ ∷ CS14⁻ ∷ []) (CS14⁻ ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 2 1 (CS14 ∷ []) (refl) ▸
       at 1 4 (CS14⁻ ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ []) (lw0 c4 (Toff423 ∷ CS14 ∷ Toff423 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ Toff423 ∷ CS14 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Sb0-1-4-3 ∷ []) (refl) ▸
       at 0 2 (CS14⁻ ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd41 c4) ▸ done

  b1 : Chain (CS14⁻ ∷ Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (CS14⁻ ∷ Sb0-1-23-4 ∷ [])
  b1 = at 1 5 (Sb0-1-23-4 ∷ []) (refl) ▸ done


-- auto BOX(0;1234) | CS31: 5 steps
lem-auto-BOX⟨0·1234⟩-∣-CS31 : Complete 4 → ⟪ (Bx0-1234 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS31 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ CS13 ∷ []) (CS13 ∷ Bx0-1234 ∷ [])
  b0 = at 1 1 (CS13 ∷ []) (lw4 c4 (CS13 ∷ []) (CS13 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx0-1324 ∷ []) (lem-sym23 c4) ▸
       at 0 2 (CS13 ∷ Bx0-1324 ∷ []) (sym (lem-CS12-beta-at2332 c4)) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym23-at2332 c4) ▸
       at 0 1 (CS13 ∷ []) (lw4 c4 (CS13 ∷ []) (CS13 ∷ []) tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CS31: 11 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS31 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS31 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-1-23-4 ∷ CS13 ∷ []) (Bx0-1234 ∷ Toff423 ∷ CS13 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 4 1 (CS14⁻ ∷ []) (refl) ▸
       at 4 2 (CS13 ∷ CS14⁻ ∷ []) (lw0 c4 (CS14⁻ ∷ CS13 ∷ []) (CS13 ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 3 2 (CS13 ∷ Toff423 ∷ []) (lw0 c4 (Toff423 ∷ CS13 ∷ []) (CS13 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (CS14 ∷ []) (refl) ▸
       at 2 2 (CS13 ∷ CS14 ∷ []) (lw0 c4 (CS14 ∷ CS13 ∷ []) (CS13 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Sb0-1-4-3 ∷ []) (refl) ▸ done

  b1 : Chain (Bx0-1234 ∷ Toff423 ∷ CS13 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (CS13 ∷ Sb0-1-23-4 ∷ [])
  b1 = at 1 2 (CS13 ∷ Toff423 ∷ []) (lw0 c4 (Toff423 ∷ CS13 ∷ []) (CS13 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (CS13 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS31 c4) ▸
       at 1 5 (Sb0-1-23-4 ∷ []) (refl) ▸ done


-- auto SBOX(0;1;23;4) | CS41 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS41-at2332 : Complete 4 → ⟪ (Sb0-1-32-4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS41-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ CS14 ∷ []) (CS14 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 (CS14 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS14 ∷ []) (CS14 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS14 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS41 c4) ▸
       at 0 2 (CS14 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS14 ∷ []) (CS14 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CX34 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CX34-at2332 : Complete 4 → ⟪ (Sb0-1-32-4 ∷ CX24 ∷ []) ⟫ʷ ≈ ⟪ (CX24 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CX34-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ CX24 ∷ []) (CX24 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 (CX34 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CX24 ∷ []) (CX34 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CX34 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CX34 c4) ▸
       at 0 2 (CX24 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CX34 ∷ []) (CX24 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CSd41 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd41-at2332 : Complete 4 → ⟪ (Sb0-1-32-4 ∷ CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS14⁻ ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd41-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 (CS14⁻ ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS14⁻ ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd41 c4) ▸
       at 0 2 (CS14⁻ ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CS31 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS31-at2332 : Complete 4 → ⟪ (Sb0-1-32-4 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS31-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ CS12 ∷ []) (CS12 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 (CS13 ∷ Sw23 ∷ []) (lem-nat-2-CS12 c4) ▸
       at 1 2 (CS13 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS31 c4) ▸
       at 0 2 (CS12 ∷ Sw23 ∷ []) (lem-nat-2-CS13 c4) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CCZ124: 9 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ124 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ124 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-1-23-4 ∷ CCZ124 ∷ []) (CS14 ∷ CX24 ∷ CS14⁻ ∷ CX24 ∷ CS12 ∷ Sb0-1-23-4 ∷ [])
  b0 = at 1 1 (CS14 ∷ CX24 ∷ CS14⁻ ∷ CX24 ∷ CS12 ∷ []) (lw0 c4 (CCZ124 ∷ []) (CS14 ∷ CX24 ∷ CS14⁻ ∷ CX24 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb0-1-32-4 ∷ []) (lem-SBsym-at0113203442 c4) ▸
       at 0 2 (CS14 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS41-at2332 c4) ▸
       at 1 2 (CX24 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CX34-at2332 c4) ▸
       at 2 2 (CS14⁻ ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CSd41-at2332 c4) ▸
       at 3 2 (CX24 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CX34-at2332 c4) ▸
       at 4 2 (CS12 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS31-at2332 c4) ▸
       at 5 1 (Sb0-1-23-4 ∷ []) (sym (lem-SBsym-at0113203442 c4)) ▸ done

  b1 : Chain (CS14 ∷ CX24 ∷ CS14⁻ ∷ CX24 ∷ CS12 ∷ Sb0-1-23-4 ∷ []) (CCZ124 ∷ Sb0-1-23-4 ∷ [])
  b1 = at 0 5 (CCZ124 ∷ []) (lw0 c4 (CS14 ∷ CX24 ∷ CS14⁻ ∷ CX24 ∷ CS12 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl) ▸ done


-- F5d CS01: 64 steps
lem-F5d-CS01 : Complete 4 → ⟪ (CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-0-41-3 ∷ X4 ∷ Sb⁻2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-F5d-CS01 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (run b7)))))))
  where
  b0 : Chain (CS01⁻ ∷ []) (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CS01⁻ ∷ [])
  b0 = at 0 0 (CS03 ∷ CS03⁻ ∷ []) (lw4 c4 [] (CS03 ∷ CS03⁻ ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 1 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 1 0 (Toff314 ∷ Toff314 ∷ []) (lw0 c4 [] (Toff314 ∷ Toff314 ∷ []) tt tt Eq.refl) ▸
       at 2 0 (CS03⁻ ∷ CS03 ∷ []) (lw4 c4 [] (CS03⁻ ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 3 0 (Toff314 ∷ Toff314 ∷ []) (lw0 c4 [] (Toff314 ∷ Toff314 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CS01⁻ ∷ []) (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻0-213 ∷ CCZ024 ∷ CCZ024 ∷ Bx0-213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CS01⁻ ∷ [])
  b1 = at 4 0 (CZ03 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ []) (lw4 c4 [] (CZ03 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Bx⁻2-03 ∷ []) (refl) ▸
       at 7 1 (Bx⁻2-03 ∷ []) (refl) ▸
       at 4 6 (Bx⁻0-213 ∷ []) (refl) ▸
       at 7 1 (Bx2-03 ∷ []) (refl) ▸
       at 10 1 (Bx2-03 ∷ []) (refl) ▸
       at 5 6 (Bx0-213 ∷ []) (refl) ▸
       at 5 0 (CCZ024 ∷ CCZ024 ∷ []) (pw1 c4 [] (CCZ024 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻0-213 ∷ CCZ024 ∷ CCZ024 ∷ Bx0-213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CS01⁻ ∷ []) (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻0-213 ∷ CCZ024 ∷ Toff204 ∷ Bx⁻0-213 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CS01⁻ ∷ [])
  b2 = at 6 0 (Toff204 ∷ Toff204 ∷ []) (pw1 c4 [] (Toff204 ∷ Toff204 ∷ []) tt tt Eq.refl) ▸
       at 7 0 (CZ03 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ []) (lw4 c4 [] (CZ03 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (Bx⁻2-03 ∷ []) (refl) ▸
       at 10 1 (Bx⁻2-03 ∷ []) (refl) ▸
       at 7 6 (Bx⁻0-213 ∷ []) (refl) ▸
       at 10 1 (Bx2-03 ∷ []) (refl) ▸
       at 13 1 (Bx2-03 ∷ []) (refl) ▸
       at 8 6 (Bx0-213 ∷ []) (refl) ▸ done

  b3 : Chain (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻0-213 ∷ CCZ024 ∷ Toff204 ∷ Bx⁻0-213 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ CS01⁻ ∷ []) (Sb⁻2-0-41-3 ∷ X4 ∷ CS03 ∷ CS03⁻ ∷ X4 ∷ Sb2-0-41-3 ∷ CS01⁻ ∷ [])
  b3 = at 8 0 (Toff204 ∷ Toff204 ∷ []) (pw1 c4 [] (Toff204 ∷ Toff204 ∷ []) tt tt Eq.refl) ▸
       at 9 0 (CCZ024 ∷ CCZ024 ∷ []) (pw1 c4 [] (CCZ024 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 4 6 (Bx⁻2-0413 ∷ []) (refl) ▸
       at 5 6 (Bx2-0413 ∷ []) (refl) ▸
       at 0 5 (Sb⁻2-0-41-3 ∷ []) (refl) ▸
       at 1 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 1 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 0 (CS03 ∷ CS03⁻ ∷ []) (lw4 c4 [] (CS03 ∷ CS03⁻ ∷ []) tt tt Eq.refl) ▸ done

  b4 : Chain (Sb⁻2-0-41-3 ∷ X4 ∷ CS03 ∷ CS03⁻ ∷ X4 ∷ Sb2-0-41-3 ∷ CS01⁻ ∷ []) (Sb⁻2-0-41-3 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ CZ03 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb2-0-41-3 ∷ CS01⁻ ∷ [])
  b4 = at 2 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 3 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 0 (Toff314 ∷ Toff314 ∷ []) (lw0 c4 [] (Toff314 ∷ Toff314 ∷ []) tt tt Eq.refl) ▸
       at 4 0 (CS03⁻ ∷ CS03 ∷ []) (lw4 c4 [] (CS03⁻ ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 5 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 5 0 (Toff314 ∷ Toff314 ∷ []) (lw0 c4 [] (Toff314 ∷ Toff314 ∷ []) tt tt Eq.refl) ▸
       at 6 0 (CZ03 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ []) (lw4 c4 [] (CZ03 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ []) tt tt Eq.refl) ▸ done

  b5 : Chain (Sb⁻2-0-41-3 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ CZ03 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb2-0-41-3 ∷ CS01⁻ ∷ []) (Sb⁻2-0-41-3 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻0-213 ∷ CCZ024 ∷ Toff204 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb2-0-41-3 ∷ CS01⁻ ∷ [])
  b5 = at 6 1 (Bx⁻2-03 ∷ []) (refl) ▸
       at 9 1 (Bx⁻2-03 ∷ []) (refl) ▸
       at 6 6 (Bx⁻0-213 ∷ []) (refl) ▸
       at 9 1 (Bx2-03 ∷ []) (refl) ▸
       at 12 1 (Bx2-03 ∷ []) (refl) ▸
       at 7 6 (Bx0-213 ∷ []) (refl) ▸
       at 7 0 (CCZ024 ∷ CCZ024 ∷ []) (pw1 c4 [] (CCZ024 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 8 0 (Toff204 ∷ Toff204 ∷ []) (pw1 c4 [] (Toff204 ∷ Toff204 ∷ []) tt tt Eq.refl) ▸ done

  b6 : Chain (Sb⁻2-0-41-3 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻0-213 ∷ CCZ024 ∷ Toff204 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb2-0-41-3 ∷ CS01⁻ ∷ []) (Sb⁻2-0-41-3 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻0-213 ∷ CCZ024 ∷ Toff204 ∷ Bx⁻0-213 ∷ Toff204 ∷ Toff204 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb2-0-41-3 ∷ CS01⁻ ∷ [])
  b6 = at 9 0 (CZ03 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ []) (lw4 c4 [] (CZ03 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ []) tt tt Eq.refl) ▸
       at 9 1 (Bx⁻2-03 ∷ []) (refl) ▸
       at 12 1 (Bx⁻2-03 ∷ []) (refl) ▸
       at 9 6 (Bx⁻0-213 ∷ []) (refl) ▸
       at 12 1 (Bx2-03 ∷ []) (refl) ▸
       at 15 1 (Bx2-03 ∷ []) (refl) ▸
       at 10 6 (Bx0-213 ∷ []) (refl) ▸
       at 10 0 (Toff204 ∷ Toff204 ∷ []) (pw1 c4 [] (Toff204 ∷ Toff204 ∷ []) tt tt Eq.refl) ▸ done

  b7 : Chain (Sb⁻2-0-41-3 ∷ X4 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻0-213 ∷ CCZ024 ∷ Toff204 ∷ Bx⁻0-213 ∷ Toff204 ∷ Toff204 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ Sb2-0-41-3 ∷ CS01⁻ ∷ []) (Sb⁻2-0-41-3 ∷ X4 ∷ Sb⁻2-0-41-3 ∷ X4 ∷ [])
  b7 = at 11 0 (CCZ024 ∷ CCZ024 ∷ []) (pw1 c4 [] (CCZ024 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 6 6 (Bx⁻2-0413 ∷ []) (refl) ▸
       at 7 6 (Bx2-0413 ∷ []) (refl) ▸
       at 2 5 (Sb⁻2-0-41-3 ∷ []) (refl) ▸
       at 3 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 3 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 4 (CS01 ∷ []) (lem-F5-CS01 c4) ▸
       at 4 2 [] (lw4 c4 (CS01 ∷ CS01⁻ ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOXd(0;1234) | CS14: 7 steps
lem-auto-BOXd⟨0·1234⟩-∣-CS14 : Complete 4 → ⟪ (Bx⁻0-1234 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ Bx⁻0-1234 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-CS14 c4 = run b0
  where
  b0 : Chain (Bx⁻0-1234 ∷ CS14 ∷ []) (CS14 ∷ Bx⁻0-1234 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ []) (lem-BOXd-BOX c4) ▸
       at 0 1 (Bx0-1243 ∷ []) (lem-sym34 c4) ▸
       at 0 1 (Bx0-1423 ∷ []) (lem-sym23-at3443 c4) ▸
       at 0 2 (CS14 ∷ Bx0-1423 ∷ []) (sym (lem-CS12-beta-at243243 c4)) ▸
       at 1 1 (Bx0-1243 ∷ []) (lem-sym23-at243243 c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym34-at3443 c4) ▸
       at 1 1 (Bx⁻0-1234 ∷ []) (sym (lem-BOXd-BOX c4)) ▸ done


-- auto SBOXd(0;1;23;4) | CS14: 9 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS14 : Complete 4 → ⟪ (Sb⁻0-1-23-4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ Sb⁻0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS14 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb⁻0-1-23-4 ∷ CS14 ∷ []) (CS14 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ [])
  b0 = at 0 1 (Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ []) (refl) ▸
       at 4 2 (CS14 ∷ Bx⁻0-1234 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-CS14 c4) ▸
       at 2 1 (CS14⁻ ∷ []) (refl) ▸
       at 1 4 (CS14 ∷ Toff423 ∷ CS14⁻ ∷ Toff423 ∷ []) (lw0 c4 (Toff423 ∷ CS14⁻ ∷ Toff423 ∷ CS14 ∷ []) (CS14 ∷ Toff423 ∷ CS14⁻ ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 0 1 (CS14 ∷ []) (refl) ▸
       at 0 2 (CS14 ∷ CS14 ∷ []) (lw0 c4 (CS14 ∷ CS14 ∷ []) (CS14 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Sb0-1-4-3 ∷ []) (refl) ▸ done

  b1 : Chain (CS14 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ []) (CS14 ∷ Sb⁻0-1-23-4 ∷ [])
  b1 = at 1 5 (Sb⁻0-1-23-4 ∷ []) (refl) ▸ done


-- SBsymd @3443: 5 steps
lem-SBsymd-at3443 : Complete 4 → ⟪ (Sb⁻2-0-31-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-0-13-4 ∷ []) ⟫ʷ
lem-SBsymd-at3443 c4 = run b0
  where
  b0 : Chain (Sb⁻2-0-31-4 ∷ []) (Sb⁻2-0-13-4 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻2-0-41-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨2·0·31·4⟩ c4) ▸
       at 1 1 (Sb⁻2-0-14-3 ∷ []) (lem-SBsymd c4) ▸
       at 0 2 (Sb⁻2-0-13-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨2·0·14·3⟩ c4) ▸
       at 1 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- SBsymd @12213443: 5 steps
lem-SBsymd-at12213443 : Complete 4 → ⟪ (Sb⁻1-0-32-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-23-4 ∷ []) ⟫ʷ
lem-SBsymd-at12213443 c4 = run b0
  where
  b0 : Chain (Sb⁻1-0-32-4 ∷ []) (Sb⁻1-0-23-4 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻2-0-31-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·0·32·4⟩ c4) ▸
       at 1 1 (Sb⁻2-0-13-4 ∷ []) (lem-SBsymd-at3443 c4) ▸
       at 0 2 (Sb⁻1-0-23-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·13·4⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- SBsymd @13213442: 5 steps
lem-SBsymd-at13213442 : Complete 4 → ⟪ (Sb⁻1-0-23-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-32-4 ∷ []) ⟫ʷ
lem-SBsymd-at13213442 c4 = run b0
  where
  b0 : Chain (Sb⁻1-0-23-4 ∷ []) (Sb⁻1-0-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻1-0-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·0·23·4⟩ c4) ▸
       at 1 1 (Sb⁻1-0-23-4 ∷ []) (lem-SBsymd-at12213443 c4) ▸
       at 0 2 (Sb⁻1-0-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·0·23·4⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- SBsymd @0113203442: 5 steps
lem-SBsymd-at0113203442 : Complete 4 → ⟪ (Sb⁻0-1-23-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-32-4 ∷ []) ⟫ʷ
lem-SBsymd-at0113203442 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-23-4 ∷ []) (Sb⁻0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻1-0-23-4 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨0·1·23·4⟩ c4) ▸
       at 1 1 (Sb⁻1-0-32-4 ∷ []) (lem-SBsymd-at13213442 c4) ▸
       at 0 2 (Sb⁻0-1-32-4 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·32·4⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;23;4) | CS14 @2332: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS14-at2332 : Complete 4 → ⟪ (Sb⁻0-1-32-4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ Sb⁻0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS14-at2332 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-32-4 ∷ CS14 ∷ []) (CS14 ∷ Sb⁻0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·32·4⟩ c4) ▸
       at 2 2 (CS14 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS14 ∷ []) (CS14 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS14 ∷ Sb⁻0-1-23-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS14 c4) ▸
       at 0 2 (CS14 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS14 ∷ []) (CS14 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;23;4) | SBOX(0;1;4;3): 5 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨0·1·4·3⟩ : Complete 4 → ⟪ (Sb⁻0-1-23-4 ∷ Sb0-1-4-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-4-3 ∷ Sb⁻0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨0·1·4·3⟩ c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-23-4 ∷ Sb0-1-4-3 ∷ []) (Sb0-1-4-3 ∷ Sb⁻0-1-23-4 ∷ [])
  b0 = at 1 1 (CS14 ∷ []) (refl) ▸
       at 0 1 (Sb⁻0-1-32-4 ∷ []) (lem-SBsymd-at0113203442 c4) ▸
       at 0 2 (CS14 ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS14-at2332 c4) ▸
       at 1 1 (Sb⁻0-1-23-4 ∷ []) (sym (lem-SBsymd-at0113203442 c4)) ▸
       at 0 1 (Sb0-1-4-3 ∷ []) (refl) ▸ done


-- auto BOXd(0;1234) | K0: 3 steps
lem-auto-BOXd⟨0·1234⟩-∣-K0 : Complete 4 → ⟪ (Bx⁻0-1234 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ Bx⁻0-1234 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-K0 c4 = run b0
  where
  b0 : Chain (Bx⁻0-1234 ∷ K0 ∷ []) (K0 ∷ Bx⁻0-1234 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ []) (lem-BOXd-BOX c4) ▸
       at 0 2 (K0 ∷ Bx0-1234 ∷ []) (sym (lem-K0-pass-c c4)) ▸
       at 1 1 (Bx⁻0-1234 ∷ []) (sym (lem-BOXd-BOX c4)) ▸ done


-- F0d @3443: 5 steps
lem-F0d-at3443 : Complete 4 → ⟪ (Sb⁻2-0-31-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻4-0-31-2 ∷ []) ⟫ʷ
lem-F0d-at3443 c4 = run b0
  where
  b0 : Chain (Sb⁻2-0-31-4 ∷ []) (Sb⁻4-0-31-2 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻2-0-41-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨2·0·31·4⟩ c4) ▸
       at 1 1 (Sb⁻3-0-41-2 ∷ []) (lem-F0d c4) ▸
       at 0 2 (Sb⁻4-0-31-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨3·0·41·2⟩ c4) ▸
       at 1 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- F0d @12213443: 5 steps
lem-F0d-at12213443 : Complete 4 → ⟪ (Sb⁻1-0-32-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻4-0-32-1 ∷ []) ⟫ʷ
lem-F0d-at12213443 c4 = run b0
  where
  b0 : Chain (Sb⁻1-0-32-4 ∷ []) (Sb⁻4-0-32-1 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻2-0-31-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·0·32·4⟩ c4) ▸
       at 1 1 (Sb⁻4-0-31-2 ∷ []) (lem-F0d-at3443 c4) ▸
       at 0 2 (Sb⁻4-0-32-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨4·0·31·2⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- F0d @13213442: 5 steps
lem-F0d-at13213442 : Complete 4 → ⟪ (Sb⁻1-0-23-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻4-0-23-1 ∷ []) ⟫ʷ
lem-F0d-at13213442 c4 = run b0
  where
  b0 : Chain (Sb⁻1-0-23-4 ∷ []) (Sb⁻4-0-23-1 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻1-0-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·0·23·4⟩ c4) ▸
       at 1 1 (Sb⁻4-0-32-1 ∷ []) (lem-F0d-at12213443 c4) ▸
       at 0 2 (Sb⁻4-0-23-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨4·0·32·1⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- F0d @0113203442: 5 steps
lem-F0d-at0113203442 : Complete 4 → ⟪ (Sb⁻0-1-23-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻4-1-23-0 ∷ []) ⟫ʷ
lem-F0d-at0113203442 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-23-4 ∷ []) (Sb⁻4-1-23-0 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻1-0-23-4 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨0·1·23·4⟩ c4) ▸
       at 1 1 (Sb⁻4-0-23-1 ∷ []) (lem-F0d-at13213442 c4) ▸
       at 0 2 (Sb⁻4-1-23-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨4·0·23·1⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOXd(0;1234) | K0 @0110: 7 steps
lem-auto-BOXd⟨0·1234⟩-∣-K0-at0110 : Complete 4 → ⟪ (Bx⁻1-0234 ∷ K1 ∷ []) ⟫ʷ ≈ ⟪ (K1 ∷ Bx⁻1-0234 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-K0-at0110 c4 = run b0
  where
  b0 : Chain (Bx⁻1-0234 ∷ K1 ∷ []) (K1 ∷ Bx⁻1-0234 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx⁻0-1234 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨1·0234⟩ c4) ▸
       at 2 2 (K0 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ K1 ∷ []) (K0 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (K0 ∷ Bx⁻0-1234 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-K0 c4) ▸
       at 0 2 (K1 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ K0 ∷ []) (K1 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx⁻1-0234 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨0·1234⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOXd(0;1234) | K0 @021021: 7 steps
lem-auto-BOXd⟨0·1234⟩-∣-K0-at021021 : Complete 4 → ⟪ (Bx⁻2-0134 ∷ K2 ∷ []) ⟫ʷ ≈ ⟪ (K2 ∷ Bx⁻2-0134 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-K0-at021021 c4 = run b0
  where
  b0 : Chain (Bx⁻2-0134 ∷ K2 ∷ []) (K2 ∷ Bx⁻2-0134 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx⁻1-0234 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨2·0134⟩ c4) ▸
       at 2 2 (K1 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ K2 ∷ []) (K1 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (K1 ∷ Bx⁻1-0234 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-K0-at0110 c4) ▸
       at 0 2 (K2 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ K1 ∷ []) (K2 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx⁻2-0134 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨1·0234⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOXd(0;1234) | K0 @03102132: 7 steps
lem-auto-BOXd⟨0·1234⟩-∣-K0-at03102132 : Complete 4 → ⟪ (Bx⁻3-0124 ∷ K3 ∷ []) ⟫ʷ ≈ ⟪ (K3 ∷ Bx⁻3-0124 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-K0-at03102132 c4 = run b0
  where
  b0 : Chain (Bx⁻3-0124 ∷ K3 ∷ []) (K3 ∷ Bx⁻3-0124 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx⁻2-0134 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨3·0124⟩ c4) ▸
       at 2 2 (K2 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ K3 ∷ []) (K2 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (K2 ∷ Bx⁻2-0134 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-K0-at021021 c4) ▸
       at 0 2 (K3 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ K2 ∷ []) (K3 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx⁻3-0124 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨2·0134⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOXd(0;1234) | K0 @0410213243: 7 steps
lem-auto-BOXd⟨0·1234⟩-∣-K0-at0410213243 : Complete 4 → ⟪ (Bx⁻4-0123 ∷ K4 ∷ []) ⟫ʷ ≈ ⟪ (K4 ∷ Bx⁻4-0123 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-K0-at0410213243 c4 = run b0
  where
  b0 : Chain (Bx⁻4-0123 ∷ K4 ∷ []) (K4 ∷ Bx⁻4-0123 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx⁻3-0124 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨4·0123⟩ c4) ▸
       at 2 2 (K3 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ K4 ∷ []) (K3 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (K3 ∷ Bx⁻3-0124 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-K0-at03102132 c4) ▸
       at 0 2 (K4 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ K3 ∷ []) (K4 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx⁻4-0123 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨3·0124⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOXd(0;1234) | K0 @04102142: 7 steps
lem-auto-BOXd⟨0·1234⟩-∣-K0-at04102142 : Complete 4 → ⟪ (Bx⁻4-0132 ∷ K4 ∷ []) ⟫ʷ ≈ ⟪ (K4 ∷ Bx⁻4-0132 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-K0-at04102142 c4 = run b0
  where
  b0 : Chain (Bx⁻4-0132 ∷ K4 ∷ []) (K4 ∷ Bx⁻4-0132 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx⁻4-0123 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨4·0132⟩ c4) ▸
       at 2 2 (K4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K)) ▸
       at 1 2 (K4 ∷ Bx⁻4-0123 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-K0-at0410213243 c4) ▸
       at 0 2 (K4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K)) ▸
       at 1 2 (Bx⁻4-0132 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨4·0123⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOXd(0;1234) | K0 @041041: 7 steps
lem-auto-BOXd⟨0·1234⟩-∣-K0-at041041 : Complete 4 → ⟪ (Bx⁻4-0231 ∷ K4 ∷ []) ⟫ʷ ≈ ⟪ (K4 ∷ Bx⁻4-0231 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-K0-at041041 c4 = run b0
  where
  b0 : Chain (Bx⁻4-0231 ∷ K4 ∷ []) (K4 ∷ Bx⁻4-0231 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx⁻4-0132 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨4·0231⟩ c4) ▸
       at 2 2 (K4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K ↑)) ▸
       at 1 2 (K4 ∷ Bx⁻4-0132 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-K0-at04102142 c4) ▸
       at 0 2 (K4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K ↑)) ▸
       at 1 2 (Bx⁻4-0231 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨4·0132⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOXd(0;1234) | K0 @0440: 7 steps
lem-auto-BOXd⟨0·1234⟩-∣-K0-at0440 : Complete 4 → ⟪ (Bx⁻4-1230 ∷ K4 ∷ []) ⟫ʷ ≈ ⟪ (K4 ∷ Bx⁻4-1230 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-K0-at0440 c4 = run b0
  where
  b0 : Chain (Bx⁻4-1230 ∷ K4 ∷ []) (K4 ∷ Bx⁻4-1230 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx⁻4-0231 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨4·1230⟩ c4) ▸
       at 2 2 (K4 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ ↑)) ▸
       at 1 2 (K4 ∷ Bx⁻4-0231 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-K0-at041041 c4) ▸
       at 0 2 (K4 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ ↑)) ▸
       at 1 2 (Bx⁻4-1230 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨4·0231⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;23;4) | K4: 13 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-K4 : Complete 4 → ⟪ (Sb⁻0-1-23-4 ∷ K4 ∷ []) ⟫ʷ ≈ ⟪ (K4 ∷ Sb⁻0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-K4 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb⁻0-1-23-4 ∷ K4 ∷ []) (Sb4-1-0-3 ∷ K4 ∷ Toff023 ∷ Sb⁻4-1-0-3 ∷ Toff023 ∷ Bx⁻4-1230 ∷ [])
  b0 = at 0 1 (Sb⁻4-1-23-0 ∷ []) (lem-F0d-at0113203442 c4) ▸
       at 0 1 (Sb4-1-0-3 ∷ Toff023 ∷ Sb⁻4-1-0-3 ∷ Toff023 ∷ Bx⁻4-1230 ∷ []) (refl) ▸
       at 4 2 (K4 ∷ Bx⁻4-1230 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-K0-at0440 c4) ▸
       at 3 2 (K4 ∷ Toff023 ∷ []) (pw1 c4 (Toff023 ∷ K4 ∷ []) (K4 ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (CS01⁻ ∷ []) (refl) ▸
       at 2 2 (K4 ∷ CS01⁻ ∷ []) (lw2 c4 (CS01⁻ ∷ K4 ∷ []) (K4 ∷ CS01⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Sb⁻4-1-0-3 ∷ []) (refl) ▸
       at 1 2 (K4 ∷ Toff023 ∷ []) (pw1 c4 (Toff023 ∷ K4 ∷ []) (K4 ∷ Toff023 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Sb4-1-0-3 ∷ K4 ∷ Toff023 ∷ Sb⁻4-1-0-3 ∷ Toff023 ∷ Bx⁻4-1230 ∷ []) (K4 ∷ Sb⁻0-1-23-4 ∷ [])
  b1 = at 0 1 (CS01 ∷ []) (refl) ▸
       at 0 2 (K4 ∷ CS01 ∷ []) (lw2 c4 (CS01 ∷ K4 ∷ []) (K4 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Sb4-1-0-3 ∷ []) (refl) ▸
       at 1 5 (Sb⁻4-1-23-0 ∷ []) (refl) ▸
       at 1 1 (Sb⁻0-1-23-4 ∷ []) (sym (lem-F0d-at0113203442 c4)) ▸ done


-- auto BOXd(0;1234) | CS24: 9 steps
lem-auto-BOXd⟨0·1234⟩-∣-CS24 : Complete 4 → ⟪ (Bx⁻0-1234 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ Bx⁻0-1234 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-CS24 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx⁻0-1234 ∷ CS24 ∷ []) (CS24 ∷ Bx0-1234 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ []) (lem-BOXd-BOX c4) ▸
       at 0 1 (Bx0-2134 ∷ []) (lem-sym12 c4) ▸
       at 0 1 (Bx0-2143 ∷ []) (lem-sym34-at1221 c4) ▸
       at 0 1 (Bx0-2413 ∷ []) (lem-sym23-at12213443 c4) ▸
       at 0 2 (CS24 ∷ Bx0-2413 ∷ []) (sym (lem-CS12-beta-at12243143 c4)) ▸
       at 1 1 (Bx0-2143 ∷ []) (lem-sym23-at12243143 c4) ▸
       at 1 1 (Bx0-2134 ∷ []) (lem-sym34-at12213443 c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym12-at1221 c4) ▸ done

  b1 : Chain (CS24 ∷ Bx0-1234 ∷ []) (CS24 ∷ Bx⁻0-1234 ∷ [])
  b1 = at 1 1 (Bx⁻0-1234 ∷ []) (sym (lem-BOXd-BOX c4)) ▸ done


-- auto SBOXd(0;1;23;4) | CS24: 9 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS24 : Complete 4 → ⟪ (Sb⁻0-1-23-4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ Sb⁻0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS24 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb⁻0-1-23-4 ∷ CS24 ∷ []) (CS24 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ [])
  b0 = at 0 1 (Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ []) (refl) ▸
       at 4 2 (CS24 ∷ Bx⁻0-1234 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-CS24 c4) ▸
       at 2 1 (CS14⁻ ∷ []) (refl) ▸
       at 1 4 (CS24 ∷ Toff423 ∷ CS14⁻ ∷ Toff423 ∷ []) (lw0 c4 (Toff423 ∷ CS14⁻ ∷ Toff423 ∷ CS24 ∷ []) (CS24 ∷ Toff423 ∷ CS14⁻ ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 0 1 (CS14 ∷ []) (refl) ▸
       at 0 2 (CS24 ∷ CS14 ∷ []) (lw0 c4 (CS14 ∷ CS24 ∷ []) (CS24 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Sb0-1-4-3 ∷ []) (refl) ▸ done

  b1 : Chain (CS24 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ []) (CS24 ∷ Sb⁻0-1-23-4 ∷ [])
  b1 = at 1 5 (Sb⁻0-1-23-4 ∷ []) (refl) ▸ done


-- auto BOXd(0;1234) | Kd0: 3 steps
lem-auto-BOXd⟨0·1234⟩-∣-Kd0 : Complete 4 → ⟪ (Bx⁻0-1234 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ Bx⁻0-1234 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-Kd0 c4 = run b0
  where
  b0 : Chain (Bx⁻0-1234 ∷ K0⁻ ∷ []) (K0⁻ ∷ Bx⁻0-1234 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ []) (lem-BOXd-BOX c4) ▸
       at 0 2 (K0⁻ ∷ Bx0-1234 ∷ []) (sym (lem-K0-pass-ci c4)) ▸
       at 1 1 (Bx⁻0-1234 ∷ []) (sym (lem-BOXd-BOX c4)) ▸ done


-- auto BOXd(0;1234) | Kd0 @0110: 7 steps
lem-auto-BOXd⟨0·1234⟩-∣-Kd0-at0110 : Complete 4 → ⟪ (Bx⁻1-0234 ∷ K1⁻ ∷ []) ⟫ʷ ≈ ⟪ (K1⁻ ∷ Bx⁻1-0234 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-Kd0-at0110 c4 = run b0
  where
  b0 : Chain (Bx⁻1-0234 ∷ K1⁻ ∷ []) (K1⁻ ∷ Bx⁻1-0234 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx⁻0-1234 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨1·0234⟩ c4) ▸
       at 2 2 (K0⁻ ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ K1⁻ ∷ []) (K0⁻ ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (K0⁻ ∷ Bx⁻0-1234 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-Kd0 c4) ▸
       at 0 2 (K1⁻ ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ K0⁻ ∷ []) (K1⁻ ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx⁻1-0234 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨0·1234⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOXd(0;1234) | Kd0 @021021: 7 steps
lem-auto-BOXd⟨0·1234⟩-∣-Kd0-at021021 : Complete 4 → ⟪ (Bx⁻2-0134 ∷ K2⁻ ∷ []) ⟫ʷ ≈ ⟪ (K2⁻ ∷ Bx⁻2-0134 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-Kd0-at021021 c4 = run b0
  where
  b0 : Chain (Bx⁻2-0134 ∷ K2⁻ ∷ []) (K2⁻ ∷ Bx⁻2-0134 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx⁻1-0234 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨2·0134⟩ c4) ▸
       at 2 2 (K1⁻ ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ K2⁻ ∷ []) (K1⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (K1⁻ ∷ Bx⁻1-0234 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-Kd0-at0110 c4) ▸
       at 0 2 (K2⁻ ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ K1⁻ ∷ []) (K2⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx⁻2-0134 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨1·0234⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOXd(0;1234) | Kd0 @03102132: 7 steps
lem-auto-BOXd⟨0·1234⟩-∣-Kd0-at03102132 : Complete 4 → ⟪ (Bx⁻3-0124 ∷ K3⁻ ∷ []) ⟫ʷ ≈ ⟪ (K3⁻ ∷ Bx⁻3-0124 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-Kd0-at03102132 c4 = run b0
  where
  b0 : Chain (Bx⁻3-0124 ∷ K3⁻ ∷ []) (K3⁻ ∷ Bx⁻3-0124 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx⁻2-0134 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨3·0124⟩ c4) ▸
       at 2 2 (K2⁻ ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ K3⁻ ∷ []) (K2⁻ ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (K2⁻ ∷ Bx⁻2-0134 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-Kd0-at021021 c4) ▸
       at 0 2 (K3⁻ ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ K2⁻ ∷ []) (K3⁻ ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx⁻3-0124 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨2·0134⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOXd(0;1234) | Kd0 @0410213243: 7 steps
lem-auto-BOXd⟨0·1234⟩-∣-Kd0-at0410213243 : Complete 4 → ⟪ (Bx⁻4-0123 ∷ K4⁻ ∷ []) ⟫ʷ ≈ ⟪ (K4⁻ ∷ Bx⁻4-0123 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-Kd0-at0410213243 c4 = run b0
  where
  b0 : Chain (Bx⁻4-0123 ∷ K4⁻ ∷ []) (K4⁻ ∷ Bx⁻4-0123 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx⁻3-0124 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨4·0123⟩ c4) ▸
       at 2 2 (K3⁻ ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ K4⁻ ∷ []) (K3⁻ ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (K3⁻ ∷ Bx⁻3-0124 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-Kd0-at03102132 c4) ▸
       at 0 2 (K4⁻ ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ K3⁻ ∷ []) (K4⁻ ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx⁻4-0123 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨3·0124⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOXd(0;1234) | Kd0 @04102142: 7 steps
lem-auto-BOXd⟨0·1234⟩-∣-Kd0-at04102142 : Complete 4 → ⟪ (Bx⁻4-0132 ∷ K4⁻ ∷ []) ⟫ʷ ≈ ⟪ (K4⁻ ∷ Bx⁻4-0132 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-Kd0-at04102142 c4 = run b0
  where
  b0 : Chain (Bx⁻4-0132 ∷ K4⁻ ∷ []) (K4⁻ ∷ Bx⁻4-0132 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx⁻4-0123 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨4·0132⟩ c4) ▸
       at 2 2 (K4⁻ ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K • iI)) ▸
       at 1 2 (K4⁻ ∷ Bx⁻4-0123 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-Kd0-at0410213243 c4) ▸
       at 0 2 (K4⁻ ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K • iI)) ▸
       at 1 2 (Bx⁻4-0132 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨4·0123⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOXd(0;1234) | Kd0 @041041: 7 steps
lem-auto-BOXd⟨0·1234⟩-∣-Kd0-at041041 : Complete 4 → ⟪ (Bx⁻4-0231 ∷ K4⁻ ∷ []) ⟫ʷ ≈ ⟪ (K4⁻ ∷ Bx⁻4-0231 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-Kd0-at041041 c4 = run b0
  where
  b0 : Chain (Bx⁻4-0231 ∷ K4⁻ ∷ []) (K4⁻ ∷ Bx⁻4-0231 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx⁻4-0132 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨4·0231⟩ c4) ▸
       at 2 2 (K4⁻ ∷ Sw12 ∷ []) (c₃ (Swap ↑) ((K • iI) ↑)) ▸
       at 1 2 (K4⁻ ∷ Bx⁻4-0132 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-Kd0-at04102142 c4) ▸
       at 0 2 (K4⁻ ∷ Sw12 ∷ []) (c₃ (Swap ↑) ((K • iI) ↑)) ▸
       at 1 2 (Bx⁻4-0231 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨4·0132⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOXd(0;1234) | Kd0 @0440: 7 steps
lem-auto-BOXd⟨0·1234⟩-∣-Kd0-at0440 : Complete 4 → ⟪ (Bx⁻4-1230 ∷ K4⁻ ∷ []) ⟫ʷ ≈ ⟪ (K4⁻ ∷ Bx⁻4-1230 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-Kd0-at0440 c4 = run b0
  where
  b0 : Chain (Bx⁻4-1230 ∷ K4⁻ ∷ []) (K4⁻ ∷ Bx⁻4-1230 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx⁻4-0231 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨4·1230⟩ c4) ▸
       at 2 2 (K4⁻ ∷ Sw01 ∷ []) (c₂ (Swap) ((K • iI) ↑ ↑)) ▸
       at 1 2 (K4⁻ ∷ Bx⁻4-0231 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-Kd0-at041041 c4) ▸
       at 0 2 (K4⁻ ∷ Sw01 ∷ []) (c₂ (Swap) ((K • iI) ↑ ↑)) ▸
       at 1 2 (Bx⁻4-1230 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨4·0231⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;23;4) | Kd4: 13 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-Kd4 : Complete 4 → ⟪ (Sb⁻0-1-23-4 ∷ K4⁻ ∷ []) ⟫ʷ ≈ ⟪ (K4⁻ ∷ Sb⁻0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-Kd4 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb⁻0-1-23-4 ∷ K4⁻ ∷ []) (Sb4-1-0-3 ∷ K4⁻ ∷ Toff023 ∷ Sb⁻4-1-0-3 ∷ Toff023 ∷ Bx⁻4-1230 ∷ [])
  b0 = at 0 1 (Sb⁻4-1-23-0 ∷ []) (lem-F0d-at0113203442 c4) ▸
       at 0 1 (Sb4-1-0-3 ∷ Toff023 ∷ Sb⁻4-1-0-3 ∷ Toff023 ∷ Bx⁻4-1230 ∷ []) (refl) ▸
       at 4 2 (K4⁻ ∷ Bx⁻4-1230 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-Kd0-at0440 c4) ▸
       at 3 2 (K4⁻ ∷ Toff023 ∷ []) (pw1 c4 (Toff023 ∷ K4⁻ ∷ []) (K4⁻ ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (CS01⁻ ∷ []) (refl) ▸
       at 2 2 (K4⁻ ∷ CS01⁻ ∷ []) (lw2 c4 (CS01⁻ ∷ K4⁻ ∷ []) (K4⁻ ∷ CS01⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Sb⁻4-1-0-3 ∷ []) (refl) ▸
       at 1 2 (K4⁻ ∷ Toff023 ∷ []) (pw1 c4 (Toff023 ∷ K4⁻ ∷ []) (K4⁻ ∷ Toff023 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Sb4-1-0-3 ∷ K4⁻ ∷ Toff023 ∷ Sb⁻4-1-0-3 ∷ Toff023 ∷ Bx⁻4-1230 ∷ []) (K4⁻ ∷ Sb⁻0-1-23-4 ∷ [])
  b1 = at 0 1 (CS01 ∷ []) (refl) ▸
       at 0 2 (K4⁻ ∷ CS01 ∷ []) (lw2 c4 (CS01 ∷ K4⁻ ∷ []) (K4⁻ ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Sb4-1-0-3 ∷ []) (refl) ▸
       at 1 5 (Sb⁻4-1-23-0 ∷ []) (refl) ▸
       at 1 1 (Sb⁻0-1-23-4 ∷ []) (sym (lem-F0d-at0113203442 c4)) ▸ done


-- auto BOXd(0;1234) | CSd14: 7 steps
lem-auto-BOXd⟨0·1234⟩-∣-CSd14 : Complete 4 → ⟪ (Bx⁻0-1234 ∷ CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS14⁻ ∷ Bx⁻0-1234 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-CSd14 c4 = run b0
  where
  b0 : Chain (Bx⁻0-1234 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ Bx⁻0-1234 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ []) (lem-BOXd-BOX c4) ▸
       at 0 1 (Bx0-1243 ∷ []) (lem-sym34 c4) ▸
       at 0 1 (Bx0-1423 ∷ []) (lem-sym23-at3443 c4) ▸
       at 0 2 (CS14⁻ ∷ Bx0-1423 ∷ []) (sym (lem-CSd12-beta-at243243 c4)) ▸
       at 1 1 (Bx0-1243 ∷ []) (lem-sym23-at243243 c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym34-at3443 c4) ▸
       at 1 1 (Bx⁻0-1234 ∷ []) (sym (lem-BOXd-BOX c4)) ▸ done


-- auto SBOXd(0;1;23;4) | CSd14: 9 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CSd14 : Complete 4 → ⟪ (Sb⁻0-1-23-4 ∷ CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS14⁻ ∷ Sb⁻0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CSd14 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb⁻0-1-23-4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ [])
  b0 = at 0 1 (Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ []) (refl) ▸
       at 4 2 (CS14⁻ ∷ Bx⁻0-1234 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-CSd14 c4) ▸
       at 2 1 (CS14⁻ ∷ []) (refl) ▸
       at 1 4 (CS14⁻ ∷ Toff423 ∷ CS14⁻ ∷ Toff423 ∷ []) (lw0 c4 (Toff423 ∷ CS14⁻ ∷ Toff423 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ Toff423 ∷ CS14⁻ ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 0 1 (CS14 ∷ []) (refl) ▸
       at 0 2 (CS14⁻ ∷ CS14 ∷ []) (lw0 c4 (CS14 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Sb0-1-4-3 ∷ []) (refl) ▸ done

  b1 : Chain (CS14⁻ ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ []) (CS14⁻ ∷ Sb⁻0-1-23-4 ∷ [])
  b1 = at 1 5 (Sb⁻0-1-23-4 ∷ []) (refl) ▸ done


-- auto SBOXd(0;1;23;4) | CSd14 @2332: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CSd14-at2332 : Complete 4 → ⟪ (Sb⁻0-1-32-4 ∷ CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS14⁻ ∷ Sb⁻0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CSd14-at2332 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-32-4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ Sb⁻0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·32·4⟩ c4) ▸
       at 2 2 (CS14⁻ ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS14⁻ ∷ Sb⁻0-1-23-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CSd14 c4) ▸
       at 0 2 (CS14⁻ ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;23;4) | SBOXd(0;1;4;3): 5 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨0·1·4·3⟩ : Complete 4 → ⟪ (Sb⁻0-1-23-4 ∷ Sb⁻0-1-4-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-4-3 ∷ Sb⁻0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨0·1·4·3⟩ c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-23-4 ∷ Sb⁻0-1-4-3 ∷ []) (Sb⁻0-1-4-3 ∷ Sb⁻0-1-23-4 ∷ [])
  b0 = at 1 1 (CS14⁻ ∷ []) (refl) ▸
       at 0 1 (Sb⁻0-1-32-4 ∷ []) (lem-SBsymd-at0113203442 c4) ▸
       at 0 2 (CS14⁻ ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CSd14-at2332 c4) ▸
       at 1 1 (Sb⁻0-1-23-4 ∷ []) (sym (lem-SBsymd-at0113203442 c4)) ▸
       at 0 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸ done


-- auto SBOXd(0;1;23;4) | K0: 11 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-K0 : Complete 4 → ⟪ (Sb⁻0-1-23-4 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ Sb⁻0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-K0 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb⁻0-1-23-4 ∷ K0 ∷ []) (CS14 ∷ K0 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ [])
  b0 = at 0 1 (Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ []) (refl) ▸
       at 4 2 (K0 ∷ Bx⁻0-1234 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-K0 c4) ▸
       at 3 2 (K0 ∷ Toff423 ∷ []) (lw1 c4 (Toff423 ∷ K0 ∷ []) (K0 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (CS14⁻ ∷ []) (refl) ▸
       at 2 2 (K0 ∷ CS14⁻ ∷ []) (pw2 c4 (CS14⁻ ∷ K0 ∷ []) (K0 ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 1 2 (K0 ∷ Toff423 ∷ []) (lw1 c4 (Toff423 ∷ K0 ∷ []) (K0 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (CS14 ∷ []) (refl) ▸ done

  b1 : Chain (CS14 ∷ K0 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ []) (K0 ∷ Sb⁻0-1-23-4 ∷ [])
  b1 = at 0 2 (K0 ∷ CS14 ∷ []) (pw2 c4 (CS14 ∷ K0 ∷ []) (K0 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Sb0-1-4-3 ∷ []) (refl) ▸
       at 1 5 (Sb⁻0-1-23-4 ∷ []) (refl) ▸ done


-- auto BOXd(0;1234) | CS20: 5 steps
lem-auto-BOXd⟨0·1234⟩-∣-CS20 : Complete 4 → ⟪ (Bx⁻0-1234 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ Bx⁻0-1234 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-CS20 c4 = run b0
  where
  b0 : Chain (Bx⁻0-1234 ∷ CS02 ∷ []) (CS02 ∷ Bx⁻0-1234 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ []) (lem-BOXd-BOX c4) ▸
       at 1 1 (CS02 ∷ []) (lw4 c4 (CS02 ∷ []) (CS02 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (CS02 ∷ Bx0-1234 ∷ []) (sym (lem-CS20-beta-c c4)) ▸
       at 0 1 (CS02 ∷ []) (lw4 c4 (CS02 ∷ []) (CS02 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Bx⁻0-1234 ∷ []) (sym (lem-BOXd-BOX c4)) ▸ done


-- auto SBOXd(0;1;23;4) | CS20: 11 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS20 : Complete 4 → ⟪ (Sb⁻0-1-23-4 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ Sb⁻0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS20 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb⁻0-1-23-4 ∷ CS02 ∷ []) (CS14 ∷ CS02 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ [])
  b0 = at 0 1 (Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ []) (refl) ▸
       at 4 2 (CS02 ∷ Bx⁻0-1234 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-CS20 c4) ▸
       at 3 2 (CS02 ∷ Toff423 ∷ []) (pw1 c4 (Toff423 ∷ CS02 ∷ []) (CS02 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (CS14⁻ ∷ []) (refl) ▸
       at 2 2 (CS02 ∷ CS14⁻ ∷ []) (pw3 c4 (CS14⁻ ∷ CS02 ∷ []) (CS02 ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 1 2 (CS02 ∷ Toff423 ∷ []) (pw1 c4 (Toff423 ∷ CS02 ∷ []) (CS02 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (CS14 ∷ []) (refl) ▸ done

  b1 : Chain (CS14 ∷ CS02 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ []) (CS02 ∷ Sb⁻0-1-23-4 ∷ [])
  b1 = at 0 2 (CS02 ∷ CS14 ∷ []) (pw3 c4 (CS14 ∷ CS02 ∷ []) (CS02 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Sb0-1-4-3 ∷ []) (refl) ▸
       at 1 5 (Sb⁻0-1-23-4 ∷ []) (refl) ▸ done


-- auto BOXd(0;1234) | CS10: 7 steps
lem-auto-BOXd⟨0·1234⟩-∣-CS10 : Complete 4 → ⟪ (Bx⁻0-1234 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ Bx⁻0-1234 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-CS10 c4 = run b0
  where
  b0 : Chain (Bx⁻0-1234 ∷ CS01 ∷ []) (CS01 ∷ Bx⁻0-1234 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ []) (lem-BOXd-BOX c4) ▸
       at 1 1 (CS01 ∷ []) (lw4 c4 (CS01 ∷ []) (CS01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx0-2134 ∷ []) (lem-sym12 c4) ▸
       at 0 2 (CS01 ∷ Bx0-2134 ∷ []) (sym (lem-CS20-beta-c-at1221 c4)) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym12-at1221 c4) ▸
       at 0 1 (CS01 ∷ []) (lw4 c4 (CS01 ∷ []) (CS01 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Bx⁻0-1234 ∷ []) (sym (lem-BOXd-BOX c4)) ▸ done


-- auto TOFF012 | CS34: 1 steps
lem-auto-TOFF012-∣-CS34 : Complete 4 → ⟪ (Toff012 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ Toff012 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-CS34 c4 = run b0
  where
  b0 : Chain (Toff012 ∷ CS34 ∷ []) (CS34 ∷ Toff012 ∷ [])
  b0 = at 0 2 (CS34 ∷ Toff012 ∷ []) (c₃ (Toff) (CS)) ▸ done


-- auto TOFF012 | CS34 @0110: 7 steps
lem-auto-TOFF012-∣-CS34-at0110 : Complete 4 → ⟪ (Toff102 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ Toff102 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-CS34-at0110 c4 = run b0
  where
  b0 : Chain (Toff102 ∷ CS34 ∷ []) (CS34 ∷ Toff102 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff102 ∷ []) (Toff012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CS34 ∷ Sw01 ∷ []) (c₂ (Swap) (CS ↑)) ▸
       at 1 2 (CS34 ∷ Toff012 ∷ []) (lem-auto-TOFF012-∣-CS34 c4) ▸
       at 0 2 (CS34 ∷ Sw01 ∷ []) (c₂ (Swap) (CS ↑)) ▸
       at 1 2 (Toff102 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff012 ∷ []) (Toff102 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto TOFF012 | CS34 @021021: 7 steps
lem-auto-TOFF012-∣-CS34-at021021 : Complete 4 → ⟪ (Toff201 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ Toff201 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-CS34-at021021 c4 = run b0
  where
  b0 : Chain (Toff201 ∷ CS34 ∷ []) (CS34 ∷ Toff201 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff102 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff201 ∷ []) (Toff102 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS)) ▸
       at 1 2 (CS34 ∷ Toff102 ∷ []) (lem-auto-TOFF012-∣-CS34-at0110 c4) ▸
       at 0 2 (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS)) ▸
       at 1 2 (Toff201 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff102 ∷ []) (Toff201 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto TOFF012 | CS34 @03102132: 7 steps
lem-auto-TOFF012-∣-CS34-at03102132 : Complete 4 → ⟪ (Toff301 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ Toff301 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-CS34-at03102132 c4 = run b0
  where
  b0 : Chain (Toff301 ∷ CS24 ∷ []) (CS24 ∷ Toff301 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff201 ∷ Sw23 ∷ []) (lem-nat-2-TOFF301 c4) ▸
       at 2 2 (CS34 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS24 ∷ []) (CS34 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS34 ∷ Toff201 ∷ []) (lem-auto-TOFF012-∣-CS34-at021021 c4) ▸
       at 0 2 (CS24 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS34 ∷ []) (CS24 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff301 ∷ Sw23 ∷ []) (lem-nat-2-TOFF201 c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto TOFF012 | CS34 @0410213243: 7 steps
lem-auto-TOFF012-∣-CS34-at0410213243 : Complete 4 → ⟪ (Toff401 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ Toff401 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-CS34-at0410213243 c4 = run b0
  where
  b0 : Chain (Toff401 ∷ CS23 ∷ []) (CS23 ∷ Toff401 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff301 ∷ Sw34 ∷ []) (lem-nat-3-TOFF401 c4) ▸
       at 2 2 (CS24 ∷ Sw34 ∷ []) (lem-nat-3-CS23 c4) ▸
       at 1 2 (CS24 ∷ Toff301 ∷ []) (lem-auto-TOFF012-∣-CS34-at03102132 c4) ▸
       at 0 2 (CS23 ∷ Sw34 ∷ []) (lem-nat-3-CS24 c4) ▸
       at 1 2 (Toff401 ∷ Sw34 ∷ []) (lem-nat-3-TOFF301 c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto TOFF012 | CS34 @04103143: 7 steps
lem-auto-TOFF012-∣-CS34-at04103143 : Complete 4 → ⟪ (Toff402 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Toff402 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-CS34-at04103143 c4 = run b0
  where
  b0 : Chain (Toff402 ∷ CS13 ∷ []) (CS13 ∷ Toff402 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff401 ∷ Sw12 ∷ []) (lem-nat-1-TOFF402 c4) ▸
       at 2 2 (CS23 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS13 ∷ []) (CS23 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS23 ∷ Toff401 ∷ []) (lem-auto-TOFF012-∣-CS34-at0410213243 c4) ▸
       at 0 2 (CS13 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS23 ∷ []) (CS13 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff402 ∷ Sw12 ∷ []) (lem-nat-1-TOFF401 c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto TOFF012 | CS34 @0410233142: 7 steps
lem-auto-TOFF012-∣-CS34-at0410233142 : Complete 4 → ⟪ (Toff403 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ Toff403 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-CS34-at0410233142 c4 = run b0
  where
  b0 : Chain (Toff403 ∷ CS12 ∷ []) (CS12 ∷ Toff403 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff402 ∷ Sw23 ∷ []) (lem-nat-2-TOFF403 c4) ▸
       at 2 2 (CS13 ∷ Sw23 ∷ []) (lem-nat-2-CS12 c4) ▸
       at 1 2 (CS13 ∷ Toff402 ∷ []) (lem-auto-TOFF012-∣-CS34-at04103143 c4) ▸
       at 0 2 (CS12 ∷ Sw23 ∷ []) (lem-nat-2-CS13 c4) ▸
       at 1 2 (Toff403 ∷ Sw23 ∷ []) (lem-nat-2-TOFF402 c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto TOFF012 | CS34 @04233042: 7 steps
lem-auto-TOFF012-∣-CS34-at04233042 : Complete 4 → ⟪ (Toff413 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ Toff413 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-CS34-at04233042 c4 = run b0
  where
  b0 : Chain (Toff413 ∷ CS02 ∷ []) (CS02 ∷ Toff413 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff403 ∷ Sw01 ∷ []) (lem-nat-0-TOFF413 c4) ▸
       at 2 2 (CS12 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS02 ∷ []) (CS12 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS12 ∷ Toff403 ∷ []) (lem-auto-TOFF012-∣-CS34-at0410233142 c4) ▸
       at 0 2 (CS02 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff413 ∷ Sw01 ∷ []) (lem-nat-0-TOFF403 c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto TOFF012 | CS34 @0412233041: 7 steps
lem-auto-TOFF012-∣-CS34-at0412233041 : Complete 4 → ⟪ (Toff423 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ Toff423 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-CS34-at0412233041 c4 = run b0
  where
  b0 : Chain (Toff423 ∷ CS01 ∷ []) (CS01 ∷ Toff423 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff413 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff423 ∷ []) (Toff413 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CS02 ∷ Sw12 ∷ []) (lem-nat-1-CS01 c4) ▸
       at 1 2 (CS02 ∷ Toff413 ∷ []) (lem-auto-TOFF012-∣-CS34-at04233042 c4) ▸
       at 0 2 (CS01 ∷ Sw12 ∷ []) (lem-nat-1-CS02 c4) ▸
       at 1 2 (Toff423 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff413 ∷ []) (Toff423 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto TOFF012 | CS34 @0412233140: 7 steps
lem-auto-TOFF012-∣-CS34-at0412233140 : Complete 4 → ⟪ (Toff423 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ Toff423 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-CS34-at0412233140 c4 = run b0
  where
  b0 : Chain (Toff423 ∷ CS01 ∷ []) (CS01 ∷ Toff423 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff423 ∷ Sw01 ∷ []) (c₂ (Swap) (Toffᵗ)) ▸
       at 2 2 (CS01 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS01 ∷ []) (CS01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS01 ∷ Toff423 ∷ []) (lem-auto-TOFF012-∣-CS34-at0412233041 c4) ▸
       at 0 2 (CS01 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS01 ∷ []) (CS01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff423 ∷ Sw01 ∷ []) (c₂ (Swap) (Toffᵗ)) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;23;4) | CS10: 11 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS10 : Complete 4 → ⟪ (Sb⁻0-1-23-4 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ Sb⁻0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS10 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb⁻0-1-23-4 ∷ CS01 ∷ []) (CS14 ∷ CS01 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ [])
  b0 = at 0 1 (Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ []) (refl) ▸
       at 4 2 (CS01 ∷ Bx⁻0-1234 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-CS10 c4) ▸
       at 3 2 (CS01 ∷ Toff423 ∷ []) (lem-auto-TOFF012-∣-CS34-at0412233140 c4) ▸
       at 2 1 (CS14⁻ ∷ []) (refl) ▸
       at 2 2 (CS01 ∷ CS14⁻ ∷ []) (pw2 c4 (CS14⁻ ∷ CS01 ∷ []) (CS01 ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 1 2 (CS01 ∷ Toff423 ∷ []) (lem-auto-TOFF012-∣-CS34-at0412233140 c4) ▸
       at 0 1 (CS14 ∷ []) (refl) ▸ done

  b1 : Chain (CS14 ∷ CS01 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ []) (CS01 ∷ Sb⁻0-1-23-4 ∷ [])
  b1 = at 0 2 (CS01 ∷ CS14 ∷ []) (pw2 c4 (CS14 ∷ CS01 ∷ []) (CS01 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Sb0-1-4-3 ∷ []) (refl) ▸
       at 1 5 (Sb⁻0-1-23-4 ∷ []) (refl) ▸ done


-- auto SBOXd(0;1;23;4) | CS20 @2332: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS20-at2332 : Complete 4 → ⟪ (Sb⁻0-1-32-4 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Sb⁻0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS20-at2332 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-32-4 ∷ CS03 ∷ []) (CS03 ∷ Sb⁻0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·32·4⟩ c4) ▸
       at 2 2 (CS02 ∷ Sw23 ∷ []) (lem-nat-2-CS03 c4) ▸
       at 1 2 (CS02 ∷ Sb⁻0-1-23-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS20 c4) ▸
       at 0 2 (CS03 ∷ Sw23 ∷ []) (lem-nat-2-CS02 c4) ▸
       at 1 2 (Sb⁻0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;23;4) | CS10 @2332: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS10-at2332 : Complete 4 → ⟪ (Sb⁻0-1-32-4 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ Sb⁻0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS10-at2332 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-32-4 ∷ CS01 ∷ []) (CS01 ∷ Sb⁻0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·32·4⟩ c4) ▸
       at 2 2 (CS01 ∷ Sw23 ∷ []) (sym (c₂ (CS) (Swap))) ▸
       at 1 2 (CS01 ∷ Sb⁻0-1-23-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS10 c4) ▸
       at 0 2 (CS01 ∷ Sw23 ∷ []) (sym (c₂ (CS) (Swap))) ▸
       at 1 2 (Sb⁻0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done

