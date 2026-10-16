{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D222 where

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
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-BOXd-BOX ; lem-CS12-beta ; lem-sym12 ; lem-sym23 ; lem-sym34)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-sym12-at1221)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-Cz-beta-at243243 ; lem-sym23-at2332 ; lem-sym23-at243243 ; lem-sym23-at3443 ; lem-sym34-at3443)
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-CS20-beta-c-at1221)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-CS12-beta-at2332 ; lem-CS12-beta-at243243 ; lem-CSd12-beta-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D008 using (lem-F0d-at12213443 ; lem-SBsymd-at0113203442 ; lem-auto-TOFF012-∣-CS34 ; lem-auto-TOFF012-∣-CS34-at0412233041)
open import Examples.Groups.Clifford+CS.Five.D.D012 using (lem-auto-SBOXd⟨0·1·23·4⟩-∣-K4-at2332 ; lem-auto-SBOXd⟨0·1·23·4⟩-∣-Kd4-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D079 using (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS34-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D145 using (lem-T312-beta-at14233142 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at122441 ; lem-auto-BOX⟨0·1234⟩-∣-CS14-at122441 ; lem-sym12-at122441 ; lem-sym12-at1441 ; lem-sym23-at14233241 ; lem-sym23-at1441 ; lem-sym34-at14233142 ; lem-sym34-at14233241)
open import Examples.Groups.Clifford+CS.Five.D.D146 using (lem-auto-BOX⟨0·1234⟩-∣-CSd14-at122441 ; lem-beta-inv-at122441)
open import Examples.Groups.Clifford+CS.Five.D.D153 using (lem-beta-T-at0410233241)
open import Examples.Groups.Clifford+CS.Five.D.D154 using (lem-X1-beta-at1441)
open import Examples.Groups.Clifford+CS.Five.D.D211 using (lem-auto-CS01-∣-SBOX⟨2·0·31·4⟩-at0113203442)
open import Examples.Groups.Clifford+CS.Five.D.D221 using (lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at122441 ; lem-auto-BOX⟨0·1234⟩-∣-CS13-at122441)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-0-CCZ124)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-0-TOFF403)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-nat-0-BOX⟨0·1234⟩ ; lem-nat-1-BOX⟨1·0234⟩ ; lem-nat-2-BOX⟨2·0134⟩)
open import Examples.Groups.Clifford+CS.Five.D.R013 using (lem-nat-2-CS12 ; lem-nat-2-CS13)
open import Examples.Groups.Clifford+CS.Five.D.R016 using (lem-nat-1-BOX⟨4·0312⟩)
open import Examples.Groups.Clifford+CS.Five.D.R017 using (lem-nat-3-BOX⟨3·0124⟩)
open import Examples.Groups.Clifford+CS.Five.D.R018 using (lem-nat-0-BOXd⟨1·0234⟩ ; lem-nat-1-BOXd⟨2·0134⟩ ; lem-nat-2-BOXd⟨3·0124⟩ ; lem-nat-2-SBOXd⟨0·1·23·4⟩ ; lem-nat-2-SBOXd⟨0·1·32·4⟩ ; lem-nat-3-BOXd⟨4·0123⟩)
open import Examples.Groups.Clifford+CS.Five.D.R021 using (lem-nat-1-SBOX⟨0·1·43·2⟩ ; lem-nat-1-SBOX⟨0·2·43·1⟩)
open import Examples.Groups.Clifford+CS.Five.D.R029 using (lem-nat-0-BOX⟨4·0321⟩ ; lem-nat-0-BOX⟨4·1320⟩)
open import Examples.Groups.Clifford+CS.Five.D.R030 using (lem-nat-1-BOX⟨4·0123⟩ ; lem-nat-2-BOX⟨4·0213⟩)
open import Examples.Groups.Clifford+CS.Five.D.R041 using (lem-nat-0-SBOXd⟨0·1·32·4⟩ ; lem-nat-0-SBOXd⟨4·0·32·1⟩)
open import Examples.Groups.Clifford+CS.Five.D.R042 using (lem-comm-CCZ024-CSd13 ; lem-comm-TOFF413-CX02 ; lem-nat-0-BOXd⟨4·1320⟩ ; lem-nat-1-BOXd⟨4·0213⟩ ; lem-nat-1-BOXd⟨4·0321⟩ ; lem-nat-2-BOXd⟨4·0312⟩)
-- F5 CS23: 38 steps
lem-F5-CS23 : Complete 4 → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ []) ⟫ʷ
lem-F5-CS23 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (run b4))))
  where
  b0 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (CCZ123 ∷ Bx0-2431 ∷ X4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ [])
  b0 = at 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 3 1 (CS12 ∷ []) (refl) ▸
       at 5 1 (CS12⁻ ∷ []) (refl) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Bx0-4231 ∷ []) (lem-sym12-at122441 c4) ▸
       at 0 3 (CCZ123 ∷ Bx0-4231 ∷ []) (lem-X1-beta-at1441 c4) ▸
       at 1 1 (Bx0-2431 ∷ []) (lem-sym12-at1441 c4) ▸
       at 8 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ123 ∷ Bx0-2431 ∷ X4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (CCZ123 ∷ CS23 ∷ CCZ123 ∷ CS12 ∷ Toff134 ∷ Toff134 ∷ Bx0-4231 ∷ Toff134 ∷ CS12⁻ ∷ Toff134 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b1 = at 10 1 (CS12 ∷ []) (refl) ▸
       at 12 1 (CS12⁻ ∷ []) (refl) ▸
       at 2 6 (CS23 ∷ CCZ123 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff134 ∷ []) (lw0 c4 (X4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ []) (CS23 ∷ CCZ123 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff134 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS23 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS13-at122441 c4) ▸
       at 2 2 (CCZ123 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at122441 c4) ▸
       at 3 2 (CS12 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS14-at122441 c4) ▸
       at 4 0 (Toff134 ∷ Toff134 ∷ []) (lw0 c4 [] (Toff134 ∷ Toff134 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Bx0-4231 ∷ []) (lem-sym12-at122441 c4) ▸ done

  b2 : Chain (CCZ123 ∷ CS23 ∷ CCZ123 ∷ CS12 ∷ Toff134 ∷ Toff134 ∷ Bx0-4231 ∷ Toff134 ∷ CS12⁻ ∷ Toff134 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (CCZ123 ∷ CS23 ∷ CCZ123 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Bx0-2431 ∷ Toff134 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b2 = at 6 1 (Bx0-4321 ∷ []) (lem-sym23-at1441 c4) ▸
       at 6 1 (Bx0-4312 ∷ []) (lem-sym34-at14233241 c4) ▸
       at 5 3 (Bx0-4312 ∷ CCZ234 ∷ []) (lem-T312-beta-at14233142 c4) ▸
       at 5 1 (Bx0-4321 ∷ []) (lem-sym34-at14233142 c4) ▸
       at 5 1 (Bx0-4231 ∷ []) (lem-sym23-at14233241 c4) ▸
       at 5 1 (Bx0-2431 ∷ []) (lem-sym12-at1441 c4) ▸
       at 5 2 (CCZ234 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at122441 c4) ▸
       at 6 2 (CS12⁻ ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd14-at122441 c4) ▸ done

  b3 : Chain (CCZ123 ∷ CS23 ∷ CCZ123 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Bx0-2431 ∷ Toff134 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (CCZ123 ∷ CS23 ∷ CCZ123 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff134 ∷ Bx0-2431 ∷ CCZ234 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b3 = at 7 0 (Toff134 ∷ Toff134 ∷ []) (lw0 c4 [] (Toff134 ∷ Toff134 ∷ []) tt tt Eq.refl) ▸
       at 9 1 (Bx0-4231 ∷ []) (lem-sym12-at122441 c4) ▸
       at 9 1 (Bx0-4321 ∷ []) (lem-sym23-at1441 c4) ▸
       at 9 1 (Bx0-4312 ∷ []) (lem-sym34-at14233241 c4) ▸
       at 8 3 (Bx0-4312 ∷ CCZ234 ∷ []) (lem-T312-beta-at14233142 c4) ▸
       at 8 1 (Bx0-4321 ∷ []) (lem-sym34-at14233142 c4) ▸
       at 8 1 (Bx0-4231 ∷ []) (lem-sym23-at14233241 c4) ▸
       at 8 1 (Bx0-2431 ∷ []) (lem-sym12-at1441 c4) ▸ done

  b4 : Chain (CCZ123 ∷ CS23 ∷ CCZ123 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff134 ∷ Bx0-2431 ∷ CCZ234 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (CS23 ∷ [])
  b4 = at 8 2 (CCZ234 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at122441 c4) ▸
       at 1 5 (CCZ234 ∷ CS23 ∷ CCZ123 ∷ CS12 ∷ Toff134 ∷ []) (lw0 c4 (CS23 ∷ CCZ123 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ []) (CCZ234 ∷ CS23 ∷ CCZ123 ∷ CS12 ∷ Toff134 ∷ []) tt tt Eq.refl) ▸
       at 2 7 (CCZ234 ∷ CS23 ∷ CCZ123 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff134 ∷ []) (lw0 c4 (CS23 ∷ CCZ123 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff134 ∷ CCZ234 ∷ []) (CCZ234 ∷ CS23 ∷ CCZ123 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff134 ∷ []) tt tt Eq.refl) ▸
       at 1 2 [] (lw0 c4 (CCZ234 ∷ CCZ234 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 [] (lem-beta-inv-at122441 c4) ▸
       at 0 11 (CS23 ∷ []) (lw0 c4 (CCZ123 ∷ CS23 ∷ CCZ123 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff134 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (CS23 ∷ []) tt tt Eq.refl) ▸ done


-- auto CS01 | SBOX(2;0;31;4) @0213203441: 7 steps
lem-auto-CS01-∣-SBOX⟨2·0·31·4⟩-at0213203441 : Complete 4 → ⟪ (CS23 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ CS23 ∷ []) ⟫ʷ
lem-auto-CS01-∣-SBOX⟨2·0·31·4⟩-at0213203441 c4 = run b0
  where
  b0 : Chain (CS23 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ CS23 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS13 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS23 ∷ []) (CS13 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·43·1⟩ c4) ▸
       at 1 2 (Sb0-1-43-2 ∷ CS13 ∷ []) (lem-auto-CS01-∣-SBOX⟨2·0·31·4⟩-at0113203442 c4) ▸
       at 0 2 (Sb0-2-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·43·2⟩ c4) ▸
       at 1 2 (CS23 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS13 ∷ []) (CS23 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- F4 CS23^0|CS23^1: 63 steps
lem-F4-CS23ᵖ0∣CS23ᵖ1 : Complete 4 → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS23ᵖ0∣CS23ᵖ1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (run b7)))))))
  where
  b0 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (CS23 ∷ CCZ024 ∷ Toff024 ∷ Bx2-031 ∷ Bx⁻0-21 ∷ CCZ023 ∷ Toff203 ∷ CZ12 ∷ Toff203 ∷ CCZ023 ∷ Toff024 ∷ CCZ024 ∷ [])
  b0 = at 0 4 (CS23 ∷ []) (lem-F5-CS23 c4) ▸
       at 1 0 (CCZ024 ∷ CCZ024 ∷ []) (pw1 c4 [] (CCZ024 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 2 0 (Toff024 ∷ Toff024 ∷ []) (pw1 c4 [] (Toff024 ∷ Toff024 ∷ []) tt tt Eq.refl) ▸
       at 3 0 (CCZ023 ∷ Toff203 ∷ CZ12 ∷ Toff203 ∷ CCZ023 ∷ CZ12 ∷ CZ12 ∷ CCZ023 ∷ Toff203 ∷ CZ12 ∷ Toff203 ∷ CCZ023 ∷ []) (lw4 c4 [] (CCZ023 ∷ Toff203 ∷ CZ12 ∷ Toff203 ∷ CCZ023 ∷ CZ12 ∷ CZ12 ∷ CCZ023 ∷ Toff203 ∷ CZ12 ∷ Toff203 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Bx0-21 ∷ []) (refl) ▸
       at 8 1 (Bx0-21 ∷ []) (refl) ▸
       at 3 6 (Bx2-031 ∷ []) (refl) ▸
       at 4 1 (Bx⁻0-21 ∷ []) (refl) ▸ done

  b1 : Chain (CS23 ∷ CCZ024 ∷ Toff024 ∷ Bx2-031 ∷ Bx⁻0-21 ∷ CCZ023 ∷ Toff203 ∷ CZ12 ∷ Toff203 ∷ CCZ023 ∷ Toff024 ∷ CCZ024 ∷ []) (CS23 ∷ CCZ024 ∷ Toff024 ∷ Bx2-031 ∷ Toff024 ∷ CCZ024 ∷ Bx2-031 ∷ CZ12 ∷ CCZ023 ∷ Toff203 ∷ CZ12 ∷ Toff203 ∷ CCZ023 ∷ CCZ024 ∷ Toff024 ∷ Bx⁻2-031 ∷ Toff024 ∷ CCZ024 ∷ [])
  b1 = at 7 1 (Bx⁻0-21 ∷ []) (refl) ▸
       at 4 6 (Bx⁻2-031 ∷ []) (refl) ▸
       at 4 0 (Toff024 ∷ Toff024 ∷ []) (pw1 c4 [] (Toff024 ∷ Toff024 ∷ []) tt tt Eq.refl) ▸
       at 5 0 (CCZ024 ∷ CCZ024 ∷ []) (pw1 c4 [] (CCZ024 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 6 0 (CCZ023 ∷ Toff203 ∷ CZ12 ∷ Toff203 ∷ CCZ023 ∷ CZ12 ∷ CZ12 ∷ CCZ023 ∷ Toff203 ∷ CZ12 ∷ Toff203 ∷ CCZ023 ∷ []) (lw4 c4 [] (CCZ023 ∷ Toff203 ∷ CZ12 ∷ Toff203 ∷ CCZ023 ∷ CZ12 ∷ CZ12 ∷ CCZ023 ∷ Toff203 ∷ CZ12 ∷ Toff203 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 8 1 (Bx0-21 ∷ []) (refl) ▸
       at 11 1 (Bx0-21 ∷ []) (refl) ▸
       at 6 6 (Bx2-031 ∷ []) (refl) ▸ done

  b2 : Chain (CS23 ∷ CCZ024 ∷ Toff024 ∷ Bx2-031 ∷ Toff024 ∷ CCZ024 ∷ Bx2-031 ∷ CZ12 ∷ CCZ023 ∷ Toff203 ∷ CZ12 ∷ Toff203 ∷ CCZ023 ∷ CCZ024 ∷ Toff024 ∷ Bx⁻2-031 ∷ Toff024 ∷ CCZ024 ∷ []) (CS23 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ CS12⁻ ∷ Toff134 ∷ Bx⁻0-2431 ∷ [])
  b2 = at 7 1 (Bx⁻0-21 ∷ []) (refl) ▸
       at 10 1 (Bx⁻0-21 ∷ []) (refl) ▸
       at 7 6 (Bx⁻2-031 ∷ []) (refl) ▸
       at 1 6 (Bx0-2431 ∷ []) (refl) ▸
       at 2 6 (Bx⁻0-2431 ∷ []) (refl) ▸
       at 2 0 (Toff134 ∷ Toff134 ∷ []) (lw0 c4 [] (Toff134 ∷ Toff134 ∷ []) tt tt Eq.refl) ▸
       at 3 0 (CS12 ∷ CS12⁻ ∷ []) (lw4 c4 [] (CS12 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Sb0-2-1-3 ∷ []) (refl) ▸ done

  b3 : Chain (CS23 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ CS12⁻ ∷ Toff134 ∷ Bx⁻0-2431 ∷ []) (Sb0-2-43-1 ∷ CS23 ∷ Sb⁻0-2-43-1 ∷ [])
  b3 = at 4 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 4 0 (Toff134 ∷ Toff134 ∷ []) (lw0 c4 [] (Toff134 ∷ Toff134 ∷ []) tt tt Eq.refl) ▸
       at 5 0 (CS12⁻ ∷ CS12 ∷ []) (lw4 c4 [] (CS12⁻ ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 6 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 1 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 2 5 (Sb⁻0-2-43-1 ∷ []) (refl) ▸
       at 0 2 (Sb0-2-43-1 ∷ CS23 ∷ []) (lem-auto-CS01-∣-SBOX⟨2·0·31·4⟩-at0213203441 c4) ▸ done

  b4 : Chain (Sb0-2-43-1 ∷ CS23 ∷ Sb⁻0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Sb⁻0-2-1-3 ∷ Toff134 ∷ Bx⁻0-2431 ∷ [])
  b4 = at 1 1 (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F5-CS23 c4)) ▸
       at 5 1 (Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ Toff134 ∷ Bx⁻0-2431 ∷ []) (refl) ▸
       at 4 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 8 1 (CS12⁻ ∷ []) (refl) ▸
       at 9 1 (CS12 ∷ []) (refl) ▸
       at 8 2 [] (lw4 c4 (CS12⁻ ∷ CS12 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 [] (lw0 c4 (Toff134 ∷ Toff134 ∷ []) [] tt tt Eq.refl) ▸
       at 6 1 (CS12 ∷ []) (refl) ▸ done

  b5 : Chain (Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Sb⁻0-2-1-3 ∷ Toff134 ∷ Bx⁻0-2431 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CCZ024 ∷ Toff024 ∷ Bx2-031 ∷ Toff024 ∷ CCZ024 ∷ CCZ023 ∷ Toff203 ∷ CZ12 ∷ Toff203 ∷ CCZ023 ∷ CZ12 ∷ Bx⁻2-031 ∷ CCZ024 ∷ Toff024 ∷ Bx⁻2-031 ∷ Toff024 ∷ CCZ024 ∷ [])
  b5 = at 7 1 (CS12⁻ ∷ []) (refl) ▸
       at 6 2 [] (lw4 c4 (CS12 ∷ CS12⁻ ∷ []) [] tt tt Eq.refl) ▸
       at 5 2 [] (lw0 c4 (Toff134 ∷ Toff134 ∷ []) [] tt tt Eq.refl) ▸
       at 5 1 (Bx⁻2-031 ∷ CCZ024 ∷ Toff024 ∷ Bx⁻2-031 ∷ Toff024 ∷ CCZ024 ∷ []) (refl) ▸
       at 4 1 (CCZ024 ∷ Toff024 ∷ Bx2-031 ∷ Toff024 ∷ CCZ024 ∷ Bx2-031 ∷ []) (refl) ▸
       at 9 1 (CCZ023 ∷ Toff203 ∷ Bx0-21 ∷ Toff203 ∷ CCZ023 ∷ Bx0-21 ∷ []) (refl) ▸
       at 11 1 (CZ12 ∷ []) (refl) ▸
       at 14 1 (CZ12 ∷ []) (refl) ▸ done

  b6 : Chain (Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CCZ024 ∷ Toff024 ∷ Bx2-031 ∷ Toff024 ∷ CCZ024 ∷ CCZ023 ∷ Toff203 ∷ CZ12 ∷ Toff203 ∷ CCZ023 ∷ CZ12 ∷ Bx⁻2-031 ∷ CCZ024 ∷ Toff024 ∷ Bx⁻2-031 ∷ Toff024 ∷ CCZ024 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CCZ024 ∷ Toff024 ∷ CCZ023 ∷ Toff203 ∷ CZ12 ∷ Toff203 ∷ CCZ023 ∷ Bx0-21 ∷ Bx⁻2-031 ∷ Toff024 ∷ CCZ024 ∷ [])
  b6 = at 15 1 (Bx⁻0-21 ∷ CCZ023 ∷ Toff203 ∷ Bx⁻0-21 ∷ Toff203 ∷ CCZ023 ∷ []) (refl) ▸
       at 15 1 (CZ12 ∷ []) (refl) ▸
       at 18 1 (CZ12 ∷ []) (refl) ▸
       at 9 12 [] (lw4 c4 (CCZ023 ∷ Toff203 ∷ CZ12 ∷ Toff203 ∷ CCZ023 ∷ CZ12 ∷ CZ12 ∷ CCZ023 ∷ Toff203 ∷ CZ12 ∷ Toff203 ∷ CCZ023 ∷ []) [] tt tt Eq.refl) ▸
       at 8 2 [] (pw1 c4 (CCZ024 ∷ CCZ024 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 [] (pw1 c4 (Toff024 ∷ Toff024 ∷ []) [] tt tt Eq.refl) ▸
       at 6 1 (CCZ023 ∷ Toff203 ∷ Bx0-21 ∷ Toff203 ∷ CCZ023 ∷ Bx0-21 ∷ []) (refl) ▸
       at 8 1 (CZ12 ∷ []) (refl) ▸ done

  b7 : Chain (Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CCZ024 ∷ Toff024 ∷ CCZ023 ∷ Toff203 ∷ CZ12 ∷ Toff203 ∷ CCZ023 ∷ Bx0-21 ∷ Bx⁻2-031 ∷ Toff024 ∷ CCZ024 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  b7 = at 11 1 (CZ12 ∷ []) (refl) ▸
       at 12 1 (Bx⁻0-21 ∷ CCZ023 ∷ Toff203 ∷ Bx⁻0-21 ∷ Toff203 ∷ CCZ023 ∷ []) (refl) ▸
       at 12 1 (CZ12 ∷ []) (refl) ▸
       at 15 1 (CZ12 ∷ []) (refl) ▸
       at 6 12 [] (lw4 c4 (CCZ023 ∷ Toff203 ∷ CZ12 ∷ Toff203 ∷ CCZ023 ∷ CZ12 ∷ CZ12 ∷ CCZ023 ∷ Toff203 ∷ CZ12 ∷ Toff203 ∷ CCZ023 ∷ []) [] tt tt Eq.refl) ▸
       at 5 2 [] (pw1 c4 (Toff024 ∷ Toff024 ∷ []) [] tt tt Eq.refl) ▸
       at 4 2 [] (pw1 c4 (CCZ024 ∷ CCZ024 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto TOFF012 | CS34 @3443: 7 steps
lem-auto-TOFF012-∣-CS34-at3443 : Complete 4 → ⟪ (Toff012 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ Toff012 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-CS34-at3443 c4 = run b0
  where
  b0 : Chain (Toff012 ∷ CS34 ∷ []) (CS34 ∷ Toff012 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff012 ∷ Sw34 ∷ []) (sym (c₃ (Toff) (Swap))) ▸
       at 2 2 (CS34 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ CS34 ∷ []) (CS34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS34 ∷ Toff012 ∷ []) (lem-auto-TOFF012-∣-CS34 c4) ▸
       at 0 2 (CS34 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ CS34 ∷ []) (CS34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff012 ∷ Sw34 ∷ []) (sym (c₃ (Toff) (Swap))) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto TOFF012 | CCZ342: 19 steps
lem-auto-TOFF012-∣-CCZ342 : Complete 4 → ⟪ (Toff012 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Toff012 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-CCZ342 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Toff012 ∷ CCZ234 ∷ []) (CS23 ∷ K0 ∷ CS01 ∷ CX21 ∷ CX42 ∷ CS01⁻ ∷ CS23⁻ ∷ CX42 ∷ CX21 ∷ CS02 ∷ K0⁻ ∷ CS34 ∷ [])
  b0 = at 1 1 (CS23 ∷ CX42 ∷ CS23⁻ ∷ CX42 ∷ CS34 ∷ []) (lw0 c4 (CCZ234 ∷ []) (CS23 ∷ CX42 ∷ CS23⁻ ∷ CX42 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (CS23 ∷ Toff012 ∷ []) (lw4 c4 (Toff012 ∷ CS23 ∷ []) (CS23 ∷ Toff012 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (lw4 c4 (Toff012 ∷ []) (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 4 (CX42 ∷ CS23⁻ ∷ CX42 ∷ K0⁻ ∷ []) (lw1 c4 (K0⁻ ∷ CX42 ∷ CS23⁻ ∷ CX42 ∷ []) (CX42 ∷ CS23⁻ ∷ CX42 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 1 (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 6 4 (CX42 ∷ CS23⁻ ∷ CX42 ∷ CS02 ∷ []) (pw1 c4 (CS02 ∷ CX42 ∷ CS23⁻ ∷ CX42 ∷ []) (CX42 ∷ CS23⁻ ∷ CX42 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 5 4 (CX42 ∷ CS23⁻ ∷ CX42 ∷ CX21 ∷ []) (lw0 c4 (CX21 ∷ CX42 ∷ CS23⁻ ∷ CX42 ∷ []) (CX42 ∷ CS23⁻ ∷ CX42 ∷ CX21 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CX42 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (Swap ↑ • CX₁₀ • Swap ↑)) ▸ done

  b1 : Chain (CS23 ∷ K0 ∷ CS01 ∷ CX21 ∷ CX42 ∷ CS01⁻ ∷ CS23⁻ ∷ CX42 ∷ CX21 ∷ CS02 ∷ K0⁻ ∷ CS34 ∷ []) (CS23 ∷ CX42 ∷ CS23⁻ ∷ CX42 ∷ K0 ∷ CCZ012 ∷ K0⁻ ∷ CS34 ∷ [])
  b1 = at 5 2 (CS23⁻ ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (CS • CS • CS)) ▸
       at 6 2 (CX42 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (Swap ↑ • CX₁₀ • Swap ↑)) ▸
       at 3 4 (CX42 ∷ CS23⁻ ∷ CX42 ∷ CX21 ∷ []) (lw0 c4 (CX21 ∷ CX42 ∷ CS23⁻ ∷ CX42 ∷ []) (CX42 ∷ CS23⁻ ∷ CX42 ∷ CX21 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CX42 ∷ CS01 ∷ []) (c₂ (CS) (Swap ↑ • CX₁₀ • Swap ↑)) ▸
       at 3 2 (CS23⁻ ∷ CS01 ∷ []) (c₂ (CS) (CS • CS • CS)) ▸
       at 4 2 (CX42 ∷ CS01 ∷ []) (c₂ (CS) (Swap ↑ • CX₁₀ • Swap ↑)) ▸
       at 5 5 (CCZ012 ∷ []) (lw4 c4 (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 1 4 (CX42 ∷ CS23⁻ ∷ CX42 ∷ K0 ∷ []) (lw1 c4 (K0 ∷ CX42 ∷ CS23⁻ ∷ CX42 ∷ []) (CX42 ∷ CS23⁻ ∷ CX42 ∷ K0 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (CS23 ∷ CX42 ∷ CS23⁻ ∷ CX42 ∷ K0 ∷ CCZ012 ∷ K0⁻ ∷ CS34 ∷ []) (CCZ234 ∷ Toff012 ∷ [])
  b2 = at 4 3 (Toff012 ∷ []) (lw4 c4 (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (Toff012 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CS34 ∷ Toff012 ∷ []) (lem-auto-TOFF012-∣-CS34-at3443 c4) ▸
       at 0 5 (CCZ234 ∷ []) (lw0 c4 (CS23 ∷ CX42 ∷ CS23⁻ ∷ CX42 ∷ CS34 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸ done


-- auto TOFF012 | TOFF342: 5 steps
lem-auto-TOFF012-∣-TOFF342 : Complete 4 → ⟪ (Toff012 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ Toff012 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-TOFF342 c4 = run b0
  where
  b0 : Chain (Toff012 ∷ Toff324 ∷ []) (Toff324 ∷ Toff012 ∷ [])
  b0 = at 1 1 (K3 ∷ CCZ234 ∷ K3⁻ ∷ []) (lw0 c4 (Toff324 ∷ []) (K3 ∷ CCZ234 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 0 2 (K3 ∷ Toff012 ∷ []) (lw4 c4 (Toff012 ∷ K3 ∷ []) (K3 ∷ Toff012 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ234 ∷ Toff012 ∷ []) (lem-auto-TOFF012-∣-CCZ342 c4) ▸
       at 2 2 (K3⁻ ∷ Toff012 ∷ []) (lw4 c4 (Toff012 ∷ K3⁻ ∷ []) (K3⁻ ∷ Toff012 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Toff324 ∷ []) (lw0 c4 (K3 ∷ CCZ234 ∷ K3⁻ ∷ []) (Toff324 ∷ []) tt tt Eq.refl) ▸ done


-- auto BOXd(0;1234) | CS21: 5 steps
lem-auto-BOXd⟨0·1234⟩-∣-CS21 : Complete 4 → ⟪ (Bx⁻0-1234 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ Bx⁻0-1234 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-CS21 c4 = run b0
  where
  b0 : Chain (Bx⁻0-1234 ∷ CS12 ∷ []) (CS12 ∷ Bx⁻0-1234 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ []) (lem-BOXd-BOX c4) ▸
       at 1 1 (CS12 ∷ []) (lw4 c4 (CS12 ∷ []) (CS12 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (CS12 ∷ Bx0-1234 ∷ []) (sym (lem-CS12-beta c4)) ▸
       at 0 1 (CS12 ∷ []) (lw4 c4 (CS12 ∷ []) (CS12 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Bx⁻0-1234 ∷ []) (sym (lem-BOXd-BOX c4)) ▸ done


-- auto SBOXd(0;1;23;4) | CS21: 11 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS21 : Complete 4 → ⟪ (Sb⁻0-1-23-4 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ Sb⁻0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS21 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb⁻0-1-23-4 ∷ CS12 ∷ []) (CS14 ∷ CS12 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ [])
  b0 = at 0 1 (Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ []) (refl) ▸
       at 4 2 (CS12 ∷ Bx⁻0-1234 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-CS21 c4) ▸
       at 3 2 (CS12 ∷ Toff423 ∷ []) (lw0 c4 (Toff423 ∷ CS12 ∷ []) (CS12 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (CS14⁻ ∷ []) (refl) ▸
       at 2 2 (CS12 ∷ CS14⁻ ∷ []) (lw0 c4 (CS14⁻ ∷ CS12 ∷ []) (CS12 ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 1 2 (CS12 ∷ Toff423 ∷ []) (lw0 c4 (Toff423 ∷ CS12 ∷ []) (CS12 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (CS14 ∷ []) (refl) ▸ done

  b1 : Chain (CS14 ∷ CS12 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ []) (CS12 ∷ Sb⁻0-1-23-4 ∷ [])
  b1 = at 0 2 (CS12 ∷ CS14 ∷ []) (lw0 c4 (CS14 ∷ CS12 ∷ []) (CS12 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Sb0-1-4-3 ∷ []) (refl) ▸
       at 1 5 (Sb⁻0-1-23-4 ∷ []) (refl) ▸ done


-- auto BOXd(0;1234) | CS01: 5 steps
lem-auto-BOXd⟨0·1234⟩-∣-CS01 : Complete 4 → ⟪ (Bx⁻0-1234 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ Bx⁻0-1234 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-CS01 c4 = run b0
  where
  b0 : Chain (Bx⁻0-1234 ∷ CS01 ∷ []) (CS01 ∷ Bx⁻0-1234 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ []) (lem-BOXd-BOX c4) ▸
       at 0 1 (Bx0-2134 ∷ []) (lem-sym12 c4) ▸
       at 0 2 (CS01 ∷ Bx0-2134 ∷ []) (sym (lem-CS20-beta-c-at1221 c4)) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym12-at1221 c4) ▸
       at 1 1 (Bx⁻0-1234 ∷ []) (sym (lem-BOXd-BOX c4)) ▸ done


-- auto SBOXd(0;1;23;4) | CS01: 11 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS01 : Complete 4 → ⟪ (Sb⁻0-1-23-4 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ Sb⁻0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS01 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb⁻0-1-23-4 ∷ CS01 ∷ []) (CS14 ∷ CS01 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ [])
  b0 = at 0 1 (Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ []) (refl) ▸
       at 4 2 (CS01 ∷ Bx⁻0-1234 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-CS01 c4) ▸
       at 3 2 (CS01 ∷ Toff423 ∷ []) (lem-auto-TOFF012-∣-CS34-at0412233041 c4) ▸
       at 2 1 (CS14⁻ ∷ []) (refl) ▸
       at 2 2 (CS01 ∷ CS14⁻ ∷ []) (pw2 c4 (CS14⁻ ∷ CS01 ∷ []) (CS01 ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 1 2 (CS01 ∷ Toff423 ∷ []) (lem-auto-TOFF012-∣-CS34-at0412233041 c4) ▸
       at 0 1 (CS14 ∷ []) (refl) ▸ done

  b1 : Chain (CS14 ∷ CS01 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ []) (CS01 ∷ Sb⁻0-1-23-4 ∷ [])
  b1 = at 0 2 (CS01 ∷ CS14 ∷ []) (pw2 c4 (CS14 ∷ CS01 ∷ []) (CS01 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Sb0-1-4-3 ∷ []) (refl) ▸
       at 1 5 (Sb⁻0-1-23-4 ∷ []) (refl) ▸ done


-- auto SBOXd(0;1;23;4) | CS21 @2332: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS21-at2332 : Complete 4 → ⟪ (Sb⁻0-1-32-4 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Sb⁻0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS21-at2332 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-32-4 ∷ CS13 ∷ []) (CS13 ∷ Sb⁻0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·32·4⟩ c4) ▸
       at 2 2 (CS12 ∷ Sw23 ∷ []) (lem-nat-2-CS13 c4) ▸
       at 1 2 (CS12 ∷ Sb⁻0-1-23-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS21 c4) ▸
       at 0 2 (CS13 ∷ Sw23 ∷ []) (lem-nat-2-CS12 c4) ▸
       at 1 2 (Sb⁻0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- F0d @0112203443: 5 steps
lem-F0d-at0112203443 : Complete 4 → ⟪ (Sb⁻0-1-32-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻4-1-32-0 ∷ []) ⟫ʷ
lem-F0d-at0112203443 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-32-4 ∷ []) (Sb⁻4-1-32-0 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻1-0-32-4 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨0·1·32·4⟩ c4) ▸
       at 1 1 (Sb⁻4-0-32-1 ∷ []) (lem-F0d-at12213443 c4) ▸
       at 0 2 (Sb⁻4-1-32-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨4·0·32·1⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- BOXd-BOX @0110: 5 steps
lem-BOXd-BOX-at0110 : Complete 4 → ⟪ (Bx⁻1-0234 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0234 ∷ []) ⟫ʷ
lem-BOXd-BOX-at0110 c4 = run b0
  where
  b0 : Chain (Bx⁻1-0234 ∷ []) (Bx1-0234 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx⁻0-1234 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨1·0234⟩ c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-BOXd-BOX c4) ▸
       at 0 2 (Bx1-0234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1234⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- BOXd-BOX @021021: 5 steps
lem-BOXd-BOX-at021021 : Complete 4 → ⟪ (Bx⁻2-0134 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ []) ⟫ʷ
lem-BOXd-BOX-at021021 c4 = run b0
  where
  b0 : Chain (Bx⁻2-0134 ∷ []) (Bx2-0134 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx⁻1-0234 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨2·0134⟩ c4) ▸
       at 1 1 (Bx1-0234 ∷ []) (lem-BOXd-BOX-at0110 c4) ▸
       at 0 2 (Bx2-0134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0234⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- BOXd-BOX @03102132: 5 steps
lem-BOXd-BOX-at03102132 : Complete 4 → ⟪ (Bx⁻3-0124 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ []) ⟫ʷ
lem-BOXd-BOX-at03102132 c4 = run b0
  where
  b0 : Chain (Bx⁻3-0124 ∷ []) (Bx3-0124 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx⁻2-0134 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨3·0124⟩ c4) ▸
       at 1 1 (Bx2-0134 ∷ []) (lem-BOXd-BOX-at021021 c4) ▸
       at 0 2 (Bx3-0124 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0134⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- BOXd-BOX @0410213243: 5 steps
lem-BOXd-BOX-at0410213243 : Complete 4 → ⟪ (Bx⁻4-0123 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0123 ∷ []) ⟫ʷ
lem-BOXd-BOX-at0410213243 c4 = run b0
  where
  b0 : Chain (Bx⁻4-0123 ∷ []) (Bx4-0123 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx⁻3-0124 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨4·0123⟩ c4) ▸
       at 1 1 (Bx3-0124 ∷ []) (lem-BOXd-BOX-at03102132 c4) ▸
       at 0 2 (Bx4-0123 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·0124⟩ c4) ▸
       at 1 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- BOXd-BOX @04103143: 5 steps
lem-BOXd-BOX-at04103143 : Complete 4 → ⟪ (Bx⁻4-0213 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0213 ∷ []) ⟫ʷ
lem-BOXd-BOX-at04103143 c4 = run b0
  where
  b0 : Chain (Bx⁻4-0213 ∷ []) (Bx4-0213 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx⁻4-0123 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨4·0213⟩ c4) ▸
       at 1 1 (Bx4-0123 ∷ []) (lem-BOXd-BOX-at0410213243 c4) ▸
       at 0 2 (Bx4-0213 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·0123⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- BOXd-BOX @0410233142: 5 steps
lem-BOXd-BOX-at0410233142 : Complete 4 → ⟪ (Bx⁻4-0312 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0312 ∷ []) ⟫ʷ
lem-BOXd-BOX-at0410233142 c4 = run b0
  where
  b0 : Chain (Bx⁻4-0312 ∷ []) (Bx4-0312 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx⁻4-0213 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨4·0312⟩ c4) ▸
       at 1 1 (Bx4-0213 ∷ []) (lem-BOXd-BOX-at04103143 c4) ▸
       at 0 2 (Bx4-0312 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·0213⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- BOXd-BOX @0410233241: 5 steps
lem-BOXd-BOX-at0410233241 : Complete 4 → ⟪ (Bx⁻4-0321 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0321 ∷ []) ⟫ʷ
lem-BOXd-BOX-at0410233241 c4 = run b0
  where
  b0 : Chain (Bx⁻4-0321 ∷ []) (Bx4-0321 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx⁻4-0312 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨4·0321⟩ c4) ▸
       at 1 1 (Bx4-0312 ∷ []) (lem-BOXd-BOX-at0410233142 c4) ▸
       at 0 2 (Bx4-0321 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·0312⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- BOXd-BOX @04233240: 5 steps
lem-BOXd-BOX-at04233240 : Complete 4 → ⟪ (Bx⁻4-1320 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1320 ∷ []) ⟫ʷ
lem-BOXd-BOX-at04233240 c4 = run b0
  where
  b0 : Chain (Bx⁻4-1320 ∷ []) (Bx4-1320 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx⁻4-0321 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨4·1320⟩ c4) ▸
       at 1 1 (Bx4-0321 ∷ []) (lem-BOXd-BOX-at0410233241 c4) ▸
       at 0 2 (Bx4-1320 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·0321⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- beta-T @04233240: 8 steps
lem-beta-T-at04233240 : Complete 4 → ⟪ (Bx4-1320 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ []) ⟫ʷ
lem-beta-T-at04233240 c4 = run b0
  where
  b0 : Chain (Bx4-1320 ∷ []) (Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx4-0321 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·1320⟩ c4) ▸
       at 1 1 (Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ []) (lem-beta-T-at0410233241 c4) ▸
       at 0 2 (Toff413 ∷ Sw01 ∷ []) (lem-nat-0-TOFF403 c4) ▸
       at 1 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 2 2 (Toff413 ∷ Sw01 ∷ []) (lem-nat-0-TOFF403 c4) ▸
       at 3 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 4 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;23;4) | CS01 @2332: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS01-at2332 : Complete 4 → ⟪ (Sb⁻0-1-32-4 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ Sb⁻0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS01-at2332 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-32-4 ∷ CS01 ∷ []) (CS01 ∷ Sb⁻0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·32·4⟩ c4) ▸
       at 2 2 (CS01 ∷ Sw23 ∷ []) (sym (c₂ (CS) (Swap))) ▸
       at 1 2 (CS01 ∷ Sb⁻0-1-23-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS01 c4) ▸
       at 0 2 (CS01 ∷ Sw23 ∷ []) (sym (c₂ (CS) (Swap))) ▸
       at 1 2 (Sb⁻0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;23;4) | CCZ103: 28 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ103 : Complete 4 → ⟪ (Sb⁻0-1-23-4 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ Sb⁻0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ103 c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (Sb⁻0-1-23-4 ∷ CCZ013 ∷ []) (CS13 ∷ Sb4-1-0-2 ∷ Toff023 ∷ Sb⁻4-1-0-2 ∷ Toff023 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CX03 ∷ CCZ024 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ [])
  b0 = at 1 1 (CS13 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ []) (lw4 c4 (CCZ013 ∷ []) (CS13 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb⁻0-1-32-4 ∷ []) (lem-SBsymd-at0113203442 c4) ▸
       at 0 2 (CS13 ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS21-at2332 c4) ▸
       at 1 1 (Sb⁻4-1-32-0 ∷ []) (lem-F0d-at0112203443 c4) ▸
       at 1 1 (Sb4-1-0-2 ∷ Toff023 ∷ Sb⁻4-1-0-2 ∷ Toff023 ∷ Bx⁻4-1320 ∷ []) (refl) ▸
       at 5 1 (Bx4-1320 ∷ []) (lem-BOXd-BOX-at04233240 c4) ▸
       at 5 1 (Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ []) (lem-beta-T-at04233240 c4) ▸
       at 8 2 (CX03 ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ CX03 ∷ []) (CX03 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CS13 ∷ Sb4-1-0-2 ∷ Toff023 ∷ Sb⁻4-1-0-2 ∷ Toff023 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CX03 ∷ CCZ024 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ []) (CS13 ∷ Sb4-1-0-2 ∷ Toff023 ∷ Sb⁻4-1-0-2 ∷ Toff023 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ Bx4-1320 ∷ CS01 ∷ [])
  b1 = at 9 2 (CS13⁻ ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CSd13 c4) ▸
       at 10 2 (CX03 ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ CX03 ∷ []) (CX03 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 7 4 (CX03 ∷ CS13⁻ ∷ CX03 ∷ Toff413 ∷ []) (pw2 c4 (Toff413 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ []) (CX03 ∷ CS13⁻ ∷ CX03 ∷ Toff413 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CX03 ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ CX03 ∷ []) (CX03 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CS13⁻ ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CSd13 c4) ▸
       at 8 2 (CX03 ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ CX03 ∷ []) (CX03 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 5 4 (CX03 ∷ CS13⁻ ∷ CX03 ∷ Toff413 ∷ []) (pw2 c4 (Toff413 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ []) (CX03 ∷ CS13⁻ ∷ CX03 ∷ Toff413 ∷ []) tt tt Eq.refl) ▸
       at 8 4 (Bx4-1320 ∷ []) (sym (lem-beta-T-at04233240 c4)) ▸ done

  b2 : Chain (CS13 ∷ Sb4-1-0-2 ∷ Toff023 ∷ Sb⁻4-1-0-2 ∷ Toff023 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ Bx4-1320 ∷ CS01 ∷ []) (CS13 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ Sb⁻4-1-32-0 ∷ CS01 ∷ [])
  b2 = at 8 1 (Bx⁻4-1320 ∷ []) (sym (lem-BOXd-BOX-at04233240 c4)) ▸
       at 3 1 (CS01⁻ ∷ []) (refl) ▸
       at 2 6 (CX03 ∷ CS13⁻ ∷ CX03 ∷ Toff023 ∷ CS01⁻ ∷ Toff023 ∷ []) (lw4 c4 (Toff023 ∷ CS01⁻ ∷ Toff023 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ []) (CX03 ∷ CS13⁻ ∷ CX03 ∷ Toff023 ∷ CS01⁻ ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Sb⁻4-1-0-2 ∷ []) (refl) ▸
       at 1 1 (CS01 ∷ []) (refl) ▸
       at 1 4 (CX03 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ []) (lw4 c4 (CS01 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ []) (CX03 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb4-1-0-2 ∷ []) (refl) ▸
       at 4 5 (Sb⁻4-1-32-0 ∷ []) (refl) ▸ done

  b3 : Chain (CS13 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ Sb⁻4-1-32-0 ∷ CS01 ∷ []) (CCZ013 ∷ Sb⁻0-1-23-4 ∷ [])
  b3 = at 4 1 (Sb⁻0-1-32-4 ∷ []) (sym (lem-F0d-at0112203443 c4)) ▸
       at 4 2 (CS01 ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS01-at2332 c4) ▸
       at 5 1 (Sb⁻0-1-23-4 ∷ []) (sym (lem-SBsymd-at0113203442 c4)) ▸
       at 0 5 (CCZ013 ∷ []) (lw4 c4 (CS13 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸ done


-- auto BOXd(0;1234) | CS41: 9 steps
lem-auto-BOXd⟨0·1234⟩-∣-CS41 : Complete 4 → ⟪ (Bx⁻0-1234 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ Bx⁻0-1234 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-CS41 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx⁻0-1234 ∷ CS14 ∷ []) (CS14 ∷ Bx0-1234 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ []) (lem-BOXd-BOX c4) ▸
       at 1 1 (CS14 ∷ []) (lw0 c4 (CS14 ∷ []) (CS14 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx0-1243 ∷ []) (lem-sym34 c4) ▸
       at 0 1 (Bx0-1423 ∷ []) (lem-sym23-at3443 c4) ▸
       at 0 2 (CS14 ∷ Bx0-1423 ∷ []) (sym (lem-CS12-beta-at243243 c4)) ▸
       at 1 1 (Bx0-1243 ∷ []) (lem-sym23-at243243 c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym34-at3443 c4) ▸
       at 0 1 (CS14 ∷ []) (lw0 c4 (CS14 ∷ []) (CS14 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CS14 ∷ Bx0-1234 ∷ []) (CS14 ∷ Bx⁻0-1234 ∷ [])
  b1 = at 1 1 (Bx⁻0-1234 ∷ []) (sym (lem-BOXd-BOX c4)) ▸ done


-- auto SBOXd(0;1;23;4) | CS41: 9 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS41 : Complete 4 → ⟪ (Sb⁻0-1-23-4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ Sb⁻0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS41 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb⁻0-1-23-4 ∷ CS14 ∷ []) (CS14 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ [])
  b0 = at 0 1 (Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ []) (refl) ▸
       at 4 2 (CS14 ∷ Bx⁻0-1234 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-CS41 c4) ▸
       at 2 1 (CS14⁻ ∷ []) (refl) ▸
       at 1 4 (CS14 ∷ Toff423 ∷ CS14⁻ ∷ Toff423 ∷ []) (lw0 c4 (Toff423 ∷ CS14⁻ ∷ Toff423 ∷ CS14 ∷ []) (CS14 ∷ Toff423 ∷ CS14⁻ ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 0 1 (CS14 ∷ []) (refl) ▸
       at 0 2 (CS14 ∷ CS14 ∷ []) (lw0 c4 (CS14 ∷ CS14 ∷ []) (CS14 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Sb0-1-4-3 ∷ []) (refl) ▸ done

  b1 : Chain (CS14 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ []) (CS14 ∷ Sb⁻0-1-23-4 ∷ [])
  b1 = at 1 5 (Sb⁻0-1-23-4 ∷ []) (refl) ▸ done


-- auto BOXd(0;1234) | CCZ104: 9 steps
lem-auto-BOXd⟨0·1234⟩-∣-CCZ104 : Complete 4 → ⟪ (Bx⁻0-1234 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ Bx⁻0-1234 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-CCZ104 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx⁻0-1234 ∷ CCZ014 ∷ []) (CCZ014 ∷ Bx0-1234 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ []) (lem-BOXd-BOX c4) ▸
       at 1 1 (CCZ014 ∷ []) (pw2 c4 (CCZ014 ∷ []) (CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx0-1243 ∷ []) (lem-sym34 c4) ▸
       at 0 1 (Bx0-1423 ∷ []) (lem-sym23-at3443 c4) ▸
       at 0 2 (CCZ014 ∷ Bx0-1423 ∷ []) (sym (lem-Cz-beta-at243243 c4)) ▸
       at 1 1 (Bx0-1243 ∷ []) (lem-sym23-at243243 c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym34-at3443 c4) ▸
       at 0 1 (CCZ014 ∷ []) (pw2 c4 (CCZ014 ∷ []) (CCZ014 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CCZ014 ∷ Bx0-1234 ∷ []) (CCZ014 ∷ Bx⁻0-1234 ∷ [])
  b1 = at 1 1 (Bx⁻0-1234 ∷ []) (sym (lem-BOXd-BOX c4)) ▸ done


-- auto BOXd(0;1234) | CCZ140: 9 steps
lem-auto-BOXd⟨0·1234⟩-∣-CCZ140 : Complete 4 → ⟪ (Bx⁻0-1234 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ Bx⁻0-1234 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-CCZ140 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx⁻0-1234 ∷ CCZ014 ∷ []) (CCZ014 ∷ Bx0-1234 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ []) (lem-BOXd-BOX c4) ▸
       at 1 1 (CCZ014 ∷ []) (pw2 c4 (CCZ014 ∷ []) (CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx0-1243 ∷ []) (lem-sym34 c4) ▸
       at 0 1 (Bx0-1423 ∷ []) (lem-sym23-at3443 c4) ▸
       at 0 2 (CCZ014 ∷ Bx0-1423 ∷ []) (sym (lem-Cz-beta-at243243 c4)) ▸
       at 1 1 (Bx0-1243 ∷ []) (lem-sym23-at243243 c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym34-at3443 c4) ▸
       at 0 1 (CCZ014 ∷ []) (pw2 c4 (CCZ014 ∷ []) (CCZ014 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CCZ014 ∷ Bx0-1234 ∷ []) (CCZ014 ∷ Bx⁻0-1234 ∷ [])
  b1 = at 1 1 (Bx⁻0-1234 ∷ []) (sym (lem-BOXd-BOX c4)) ▸ done


-- auto TOFF012 | CCZ341: 19 steps
lem-auto-TOFF012-∣-CCZ341 : Complete 4 → ⟪ (Toff012 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Toff012 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-CCZ341 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Toff012 ∷ CCZ134 ∷ []) (CS13 ∷ K0 ∷ CS02 ∷ CX12 ∷ CX41 ∷ CS02⁻ ∷ CS13⁻ ∷ CX41 ∷ CX12 ∷ CS01 ∷ K0⁻ ∷ CS34 ∷ [])
  b0 = at 1 1 (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ []) (lw0 c4 (CCZ134 ∷ []) (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (CS13 ∷ Toff012 ∷ []) (lw4 c4 (Toff012 ∷ CS13 ∷ []) (CS13 ∷ Toff012 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (lw4 c4 (Toff012 ∷ []) (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 4 (CX41 ∷ CS13⁻ ∷ CX41 ∷ K0⁻ ∷ []) (pw2 c4 (K0⁻ ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ []) (CX41 ∷ CS13⁻ ∷ CX41 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 1 (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 6 4 (CX41 ∷ CS13⁻ ∷ CX41 ∷ CS01 ∷ []) (pw2 c4 (CS01 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ []) (CX41 ∷ CS13⁻ ∷ CX41 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 5 4 (CX41 ∷ CS13⁻ ∷ CX41 ∷ CX12 ∷ []) (lw0 c4 (CX12 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ []) (CX41 ∷ CS13⁻ ∷ CX41 ∷ CX12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CX41 ∷ CS02⁻ ∷ []) (pw3 c4 (CS02⁻ ∷ CX41 ∷ []) (CX41 ∷ CS02⁻ ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CS13 ∷ K0 ∷ CS02 ∷ CX12 ∷ CX41 ∷ CS02⁻ ∷ CS13⁻ ∷ CX41 ∷ CX12 ∷ CS01 ∷ K0⁻ ∷ CS34 ∷ []) (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ K0 ∷ CCZ012 ∷ K0⁻ ∷ CS34 ∷ [])
  b1 = at 5 2 (CS13⁻ ∷ CS02⁻ ∷ []) (lw4 c4 (CS02⁻ ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CS02⁻ ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CX41 ∷ CS02⁻ ∷ []) (pw3 c4 (CS02⁻ ∷ CX41 ∷ []) (CX41 ∷ CS02⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 4 (CX41 ∷ CS13⁻ ∷ CX41 ∷ CX12 ∷ []) (lw0 c4 (CX12 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ []) (CX41 ∷ CS13⁻ ∷ CX41 ∷ CX12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CX41 ∷ CS02 ∷ []) (pw3 c4 (CS02 ∷ CX41 ∷ []) (CX41 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CS13⁻ ∷ CS02 ∷ []) (lw4 c4 (CS02 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CX41 ∷ CS02 ∷ []) (pw3 c4 (CS02 ∷ CX41 ∷ []) (CX41 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 5 5 (CCZ012 ∷ []) (lw4 c4 (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 1 4 (CX41 ∷ CS13⁻ ∷ CX41 ∷ K0 ∷ []) (pw2 c4 (K0 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ []) (CX41 ∷ CS13⁻ ∷ CX41 ∷ K0 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ K0 ∷ CCZ012 ∷ K0⁻ ∷ CS34 ∷ []) (CCZ134 ∷ Toff012 ∷ [])
  b2 = at 4 3 (Toff012 ∷ []) (lw4 c4 (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (Toff012 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CS34 ∷ Toff012 ∷ []) (lem-auto-TOFF012-∣-CS34-at3443 c4) ▸
       at 0 5 (CCZ134 ∷ []) (lw0 c4 (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl) ▸ done


-- auto TOFF012 | TOFF341: 5 steps
lem-auto-TOFF012-∣-TOFF341 : Complete 4 → ⟪ (Toff012 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ Toff012 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-TOFF341 c4 = run b0
  where
  b0 : Chain (Toff012 ∷ Toff314 ∷ []) (Toff314 ∷ Toff012 ∷ [])
  b0 = at 1 1 (K3 ∷ CCZ134 ∷ K3⁻ ∷ []) (lw0 c4 (Toff314 ∷ []) (K3 ∷ CCZ134 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 0 2 (K3 ∷ Toff012 ∷ []) (lw4 c4 (Toff012 ∷ K3 ∷ []) (K3 ∷ Toff012 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ134 ∷ Toff012 ∷ []) (lem-auto-TOFF012-∣-CCZ341 c4) ▸
       at 2 2 (K3⁻ ∷ Toff012 ∷ []) (lw4 c4 (Toff012 ∷ K3⁻ ∷ []) (K3⁻ ∷ Toff012 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Toff314 ∷ []) (lw0 c4 (K3 ∷ CCZ134 ∷ K3⁻ ∷ []) (Toff314 ∷ []) tt tt Eq.refl) ▸ done


-- auto BOXd(0;1234) | CS31: 7 steps
lem-auto-BOXd⟨0·1234⟩-∣-CS31 : Complete 4 → ⟪ (Bx⁻0-1234 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Bx⁻0-1234 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-CS31 c4 = run b0
  where
  b0 : Chain (Bx⁻0-1234 ∷ CS13 ∷ []) (CS13 ∷ Bx⁻0-1234 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ []) (lem-BOXd-BOX c4) ▸
       at 1 1 (CS13 ∷ []) (lw4 c4 (CS13 ∷ []) (CS13 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx0-1324 ∷ []) (lem-sym23 c4) ▸
       at 0 2 (CS13 ∷ Bx0-1324 ∷ []) (sym (lem-CS12-beta-at2332 c4)) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym23-at2332 c4) ▸
       at 0 1 (CS13 ∷ []) (lw4 c4 (CS13 ∷ []) (CS13 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Bx⁻0-1234 ∷ []) (sym (lem-BOXd-BOX c4)) ▸ done


-- auto SBOXd(0;1;23;4) | CS31: 11 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS31 : Complete 4 → ⟪ (Sb⁻0-1-23-4 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Sb⁻0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS31 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb⁻0-1-23-4 ∷ CS13 ∷ []) (CS14 ∷ CS13 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ [])
  b0 = at 0 1 (Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ []) (refl) ▸
       at 4 2 (CS13 ∷ Bx⁻0-1234 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-CS31 c4) ▸
       at 3 2 (CS13 ∷ Toff423 ∷ []) (lw0 c4 (Toff423 ∷ CS13 ∷ []) (CS13 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (CS14⁻ ∷ []) (refl) ▸
       at 2 2 (CS13 ∷ CS14⁻ ∷ []) (lw0 c4 (CS14⁻ ∷ CS13 ∷ []) (CS13 ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 1 2 (CS13 ∷ Toff423 ∷ []) (lw0 c4 (Toff423 ∷ CS13 ∷ []) (CS13 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (CS14 ∷ []) (refl) ▸ done

  b1 : Chain (CS14 ∷ CS13 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ []) (CS13 ∷ Sb⁻0-1-23-4 ∷ [])
  b1 = at 0 2 (CS13 ∷ CS14 ∷ []) (lw0 c4 (CS14 ∷ CS13 ∷ []) (CS13 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Sb0-1-4-3 ∷ []) (refl) ▸
       at 1 5 (Sb⁻0-1-23-4 ∷ []) (refl) ▸ done


-- auto SBOXd(0;1;23;4) | CS31 @2332: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS31-at2332 : Complete 4 → ⟪ (Sb⁻0-1-32-4 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ Sb⁻0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS31-at2332 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-32-4 ∷ CS12 ∷ []) (CS12 ∷ Sb⁻0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·32·4⟩ c4) ▸
       at 2 2 (CS13 ∷ Sw23 ∷ []) (lem-nat-2-CS12 c4) ▸
       at 1 2 (CS13 ∷ Sb⁻0-1-23-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS31 c4) ▸
       at 0 2 (CS12 ∷ Sw23 ∷ []) (lem-nat-2-CS13 c4) ▸
       at 1 2 (Sb⁻0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;23;4) | CCZ102: 28 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ102 : Complete 4 → ⟪ (Sb⁻0-1-23-4 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Sb⁻0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ102 c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (Sb⁻0-1-23-4 ∷ CCZ012 ∷ []) (CS12 ∷ Sb4-1-0-2 ∷ Toff023 ∷ Sb⁻4-1-0-2 ∷ Toff023 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CCZ024 ∷ CS01 ∷ [])
  b0 = at 1 1 (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb⁻0-1-32-4 ∷ []) (lem-SBsymd-at0113203442 c4) ▸
       at 0 2 (CS12 ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS31-at2332 c4) ▸
       at 1 1 (Sb⁻4-1-32-0 ∷ []) (lem-F0d-at0112203443 c4) ▸
       at 1 1 (Sb4-1-0-2 ∷ Toff023 ∷ Sb⁻4-1-0-2 ∷ Toff023 ∷ Bx⁻4-1320 ∷ []) (refl) ▸
       at 5 1 (Bx4-1320 ∷ []) (lem-BOXd-BOX-at04233240 c4) ▸
       at 5 1 (Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ []) (lem-beta-T-at04233240 c4) ▸
       at 8 4 (CX02 ∷ CS12⁻ ∷ CX02 ∷ CCZ024 ∷ []) (pw3 c4 (CCZ024 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ []) (CX02 ∷ CS12⁻ ∷ CX02 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CS12 ∷ Sb4-1-0-2 ∷ Toff023 ∷ Sb⁻4-1-0-2 ∷ Toff023 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CCZ024 ∷ CS01 ∷ []) (CS12 ∷ Sb4-1-0-2 ∷ Toff023 ∷ Sb⁻4-1-0-2 ∷ Toff023 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ Bx4-1320 ∷ CS01 ∷ [])
  b1 = at 7 2 (CX02 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CX02 c4) ▸
       at 8 2 (CS12⁻ ∷ Toff413 ∷ []) (lw0 c4 (Toff413 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ Toff413 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CX02 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CX02 c4) ▸
       at 6 4 (CX02 ∷ CS12⁻ ∷ CX02 ∷ CCZ024 ∷ []) (pw3 c4 (CCZ024 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ []) (CX02 ∷ CS12⁻ ∷ CX02 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CX02 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CX02 c4) ▸
       at 6 2 (CS12⁻ ∷ Toff413 ∷ []) (lw0 c4 (Toff413 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ Toff413 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CX02 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CX02 c4) ▸
       at 8 4 (Bx4-1320 ∷ []) (sym (lem-beta-T-at04233240 c4)) ▸ done

  b2 : Chain (CS12 ∷ Sb4-1-0-2 ∷ Toff023 ∷ Sb⁻4-1-0-2 ∷ Toff023 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ Bx4-1320 ∷ CS01 ∷ []) (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ Sb⁻4-1-32-0 ∷ CS01 ∷ [])
  b2 = at 8 1 (Bx⁻4-1320 ∷ []) (sym (lem-BOXd-BOX-at04233240 c4)) ▸
       at 3 1 (CS01⁻ ∷ []) (refl) ▸
       at 2 6 (CX02 ∷ CS12⁻ ∷ CX02 ∷ Toff023 ∷ CS01⁻ ∷ Toff023 ∷ []) (lw4 c4 (Toff023 ∷ CS01⁻ ∷ Toff023 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ []) (CX02 ∷ CS12⁻ ∷ CX02 ∷ Toff023 ∷ CS01⁻ ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Sb⁻4-1-0-2 ∷ []) (refl) ▸
       at 1 1 (CS01 ∷ []) (refl) ▸
       at 1 4 (CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ []) (lw4 c4 (CS01 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ []) (CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sb4-1-0-2 ∷ []) (refl) ▸
       at 4 5 (Sb⁻4-1-32-0 ∷ []) (refl) ▸ done

  b3 : Chain (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ Sb⁻4-1-32-0 ∷ CS01 ∷ []) (CCZ012 ∷ Sb⁻0-1-23-4 ∷ [])
  b3 = at 4 1 (Sb⁻0-1-32-4 ∷ []) (sym (lem-F0d-at0112203443 c4)) ▸
       at 4 2 (CS01 ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS01-at2332 c4) ▸
       at 5 1 (Sb⁻0-1-23-4 ∷ []) (sym (lem-SBsymd-at0113203442 c4)) ▸
       at 0 5 (CCZ012 ∷ []) (lw4 c4 (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;23;4) | CS24 CS24: 6 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS24-CS24 : Complete 4 → ⟪ (Sb⁻0-1-23-4 ∷ CS24 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CS24 ∷ Sb⁻0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS24-CS24 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-23-4 ∷ CS24 ∷ CS24 ∷ []) (CS24 ∷ CS24 ∷ Sb⁻0-1-23-4 ∷ [])
  b0 = at 0 1 (Sb⁻0-1-32-4 ∷ []) (lem-SBsymd-at0113203442 c4) ▸
       at 0 2 (CS24 ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS34-at2332 c4) ▸
       at 1 1 (Sb⁻0-1-23-4 ∷ []) (sym (lem-SBsymd-at0113203442 c4)) ▸
       at 1 1 (Sb⁻0-1-32-4 ∷ []) (lem-SBsymd-at0113203442 c4) ▸
       at 1 2 (CS24 ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS34-at2332 c4) ▸
       at 2 1 (Sb⁻0-1-23-4 ∷ []) (sym (lem-SBsymd-at0113203442 c4)) ▸ done


-- auto SBOXd(0;1;23;4) | CS24 CS24 @2332: 9 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS24-CS24-at2332 : Complete 4 → ⟪ (Sb⁻0-1-32-4 ∷ CS34 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ CS34 ∷ Sb⁻0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS24-CS24-at2332 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb⁻0-1-32-4 ∷ CS34 ∷ CS34 ∷ []) (CS34 ∷ CS34 ∷ Sb⁻0-1-32-4 ∷ Sw23 ∷ Sw23 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·32·4⟩ c4) ▸
       at 2 2 (CS24 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS34 ∷ []) (CS24 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CS24 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS34 ∷ []) (CS24 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (CS24 ∷ CS24 ∷ Sb⁻0-1-23-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS24-CS24 c4) ▸
       at 0 2 (CS34 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS24 ∷ []) (CS34 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS34 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS24 ∷ []) (CS34 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb⁻0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·23·4⟩ c4) ▸ done

  b1 : Chain (CS34 ∷ CS34 ∷ Sb⁻0-1-32-4 ∷ Sw23 ∷ Sw23 ∷ []) (CS34 ∷ CS34 ∷ Sb⁻0-1-32-4 ∷ [])
  b1 = at 3 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;23;4) | CZ34: 5 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CZ34 : Complete 4 → ⟪ (Sb⁻0-1-23-4 ∷ CZ34 ∷ []) ⟫ʷ ≈ ⟪ (CZ34 ∷ Sb⁻0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CZ34 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-23-4 ∷ CZ34 ∷ []) (CZ34 ∷ Sb⁻0-1-23-4 ∷ [])
  b0 = at 1 1 (CS34 ∷ CS34 ∷ []) (lw0 c4 (CZ34 ∷ []) (CS34 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb⁻0-1-32-4 ∷ []) (lem-SBsymd-at0113203442 c4) ▸
       at 0 3 (CS34 ∷ CS34 ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS24-CS24-at2332 c4) ▸
       at 2 1 (Sb⁻0-1-23-4 ∷ []) (sym (lem-SBsymd-at0113203442 c4)) ▸
       at 0 2 (CZ34 ∷ []) (lw0 c4 (CS34 ∷ CS34 ∷ []) (CZ34 ∷ []) tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;23;4) | CZ34 @2332: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CZ34-at2332 : Complete 4 → ⟪ (Sb⁻0-1-32-4 ∷ CZ24 ∷ []) ⟫ʷ ≈ ⟪ (CZ24 ∷ Sb⁻0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CZ34-at2332 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-32-4 ∷ CZ24 ∷ []) (CZ24 ∷ Sb⁻0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·32·4⟩ c4) ▸
       at 2 2 (CZ34 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CZ24 ∷ []) (CZ34 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CZ34 ∷ Sb⁻0-1-23-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CZ34 c4) ▸
       at 0 2 (CZ24 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CZ34 ∷ []) (CZ24 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;23;4) | CX24: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CX24 : Complete 4 → ⟪ (Sb⁻0-1-23-4 ∷ CX24 ∷ []) ⟫ʷ ≈ ⟪ (CX24 ∷ Sb⁻0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CX24 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-23-4 ∷ CX24 ∷ []) (CX24 ∷ Sb⁻0-1-23-4 ∷ [])
  b0 = at 1 1 (K4 ∷ CZ24 ∷ K4⁻ ∷ []) (lw0 c4 (CX24 ∷ []) (K4 ∷ CZ24 ∷ K4⁻ ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb⁻0-1-32-4 ∷ []) (lem-SBsymd-at0113203442 c4) ▸
       at 0 2 (K4 ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-K4-at2332 c4) ▸
       at 1 2 (CZ24 ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CZ34-at2332 c4) ▸
       at 2 2 (K4⁻ ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-Kd4-at2332 c4) ▸
       at 3 1 (Sb⁻0-1-23-4 ∷ []) (sym (lem-SBsymd-at0113203442 c4)) ▸
       at 0 3 (CX24 ∷ []) (lw0 c4 (K4 ∷ CZ24 ∷ K4⁻ ∷ []) (CX24 ∷ []) tt tt Eq.refl) ▸ done


-- auto BOXd(0;1234) | CSd41: 9 steps
lem-auto-BOXd⟨0·1234⟩-∣-CSd41 : Complete 4 → ⟪ (Bx⁻0-1234 ∷ CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS14⁻ ∷ Bx⁻0-1234 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-CSd41 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx⁻0-1234 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ Bx0-1234 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ []) (lem-BOXd-BOX c4) ▸
       at 1 1 (CS14⁻ ∷ []) (lw0 c4 (CS14⁻ ∷ []) (CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx0-1243 ∷ []) (lem-sym34 c4) ▸
       at 0 1 (Bx0-1423 ∷ []) (lem-sym23-at3443 c4) ▸
       at 0 2 (CS14⁻ ∷ Bx0-1423 ∷ []) (sym (lem-CSd12-beta-at243243 c4)) ▸
       at 1 1 (Bx0-1243 ∷ []) (lem-sym23-at243243 c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym34-at3443 c4) ▸
       at 0 1 (CS14⁻ ∷ []) (lw0 c4 (CS14⁻ ∷ []) (CS14⁻ ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CS14⁻ ∷ Bx0-1234 ∷ []) (CS14⁻ ∷ Bx⁻0-1234 ∷ [])
  b1 = at 1 1 (Bx⁻0-1234 ∷ []) (sym (lem-BOXd-BOX c4)) ▸ done


-- auto SBOXd(0;1;23;4) | CSd41: 9 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CSd41 : Complete 4 → ⟪ (Sb⁻0-1-23-4 ∷ CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS14⁻ ∷ Sb⁻0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CSd41 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb⁻0-1-23-4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ [])
  b0 = at 0 1 (Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ []) (refl) ▸
       at 4 2 (CS14⁻ ∷ Bx⁻0-1234 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-CSd41 c4) ▸
       at 2 1 (CS14⁻ ∷ []) (refl) ▸
       at 1 4 (CS14⁻ ∷ Toff423 ∷ CS14⁻ ∷ Toff423 ∷ []) (lw0 c4 (Toff423 ∷ CS14⁻ ∷ Toff423 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ Toff423 ∷ CS14⁻ ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 0 1 (CS14 ∷ []) (refl) ▸
       at 0 2 (CS14⁻ ∷ CS14 ∷ []) (lw0 c4 (CS14 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Sb0-1-4-3 ∷ []) (refl) ▸ done

  b1 : Chain (CS14⁻ ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ []) (CS14⁻ ∷ Sb⁻0-1-23-4 ∷ [])
  b1 = at 1 5 (Sb⁻0-1-23-4 ∷ []) (refl) ▸ done


-- auto SBOXd(0;1;23;4) | CS41 @2332: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS41-at2332 : Complete 4 → ⟪ (Sb⁻0-1-32-4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ Sb⁻0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS41-at2332 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-32-4 ∷ CS14 ∷ []) (CS14 ∷ Sb⁻0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·32·4⟩ c4) ▸
       at 2 2 (CS14 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS14 ∷ []) (CS14 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS14 ∷ Sb⁻0-1-23-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS41 c4) ▸
       at 0 2 (CS14 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS14 ∷ []) (CS14 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;23;4) | CX24 @2332: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CX24-at2332 : Complete 4 → ⟪ (Sb⁻0-1-32-4 ∷ CX34 ∷ []) ⟫ʷ ≈ ⟪ (CX34 ∷ Sb⁻0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CX24-at2332 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-32-4 ∷ CX34 ∷ []) (CX34 ∷ Sb⁻0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·32·4⟩ c4) ▸
       at 2 2 (CX24 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CX34 ∷ []) (CX24 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CX24 ∷ Sb⁻0-1-23-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CX24 c4) ▸
       at 0 2 (CX34 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CX24 ∷ []) (CX34 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;23;4) | CSd41 @2332: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CSd41-at2332 : Complete 4 → ⟪ (Sb⁻0-1-32-4 ∷ CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS14⁻ ∷ Sb⁻0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CSd41-at2332 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-32-4 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ Sb⁻0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·32·4⟩ c4) ▸
       at 2 2 (CS14⁻ ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS14⁻ ∷ Sb⁻0-1-23-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CSd41 c4) ▸
       at 0 2 (CS14⁻ ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;23;4) | CCZ134: 9 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ134 : Complete 4 → ⟪ (Sb⁻0-1-23-4 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Sb⁻0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ134 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb⁻0-1-23-4 ∷ CCZ134 ∷ []) (CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ Sb⁻0-1-23-4 ∷ [])
  b0 = at 1 1 (CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ []) (lw0 c4 (CCZ134 ∷ []) (CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb⁻0-1-32-4 ∷ []) (lem-SBsymd-at0113203442 c4) ▸
       at 0 2 (CS14 ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS41-at2332 c4) ▸
       at 1 2 (CX34 ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CX24-at2332 c4) ▸
       at 2 2 (CS14⁻ ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CSd41-at2332 c4) ▸
       at 3 2 (CX34 ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CX24-at2332 c4) ▸
       at 4 2 (CS13 ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS21-at2332 c4) ▸
       at 5 1 (Sb⁻0-1-23-4 ∷ []) (sym (lem-SBsymd-at0113203442 c4)) ▸ done

  b1 : Chain (CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ Sb⁻0-1-23-4 ∷ []) (CCZ134 ∷ Sb⁻0-1-23-4 ∷ [])
  b1 = at 0 5 (CCZ134 ∷ []) (lw0 c4 (CS14 ∷ CX34 ∷ CS14⁻ ∷ CX34 ∷ CS13 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl) ▸ done


-- auto TOFF012 | CCZ314: 7 steps
lem-auto-TOFF012-∣-CCZ314 : Complete 4 → ⟪ (Toff012 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Toff012 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-CCZ314 c4 = run b0
  where
  b0 : Chain (Toff012 ∷ CCZ134 ∷ []) (CCZ134 ∷ Toff012 ∷ [])
  b0 = at 1 1 (CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ []) (lw0 c4 (CCZ134 ∷ []) (CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (CS34 ∷ Toff012 ∷ []) (c₃ (Toff) (CS)) ▸
       at 1 2 (CX14 ∷ Toff012 ∷ []) (pw3 c4 (Toff012 ∷ CX14 ∷ []) (CX14 ∷ Toff012 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CS34⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (CS • CS • CS)) ▸
       at 3 2 (CX14 ∷ Toff012 ∷ []) (pw3 c4 (Toff012 ∷ CX14 ∷ []) (CX14 ∷ Toff012 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CS13 ∷ Toff012 ∷ []) (lw4 c4 (Toff012 ∷ CS13 ∷ []) (CS13 ∷ Toff012 ∷ []) tt tt Eq.refl) ▸
       at 0 5 (CCZ134 ∷ []) (lw0 c4 (CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl) ▸ done


-- auto TOFF012 | TOFF314: 5 steps
lem-auto-TOFF012-∣-TOFF314 : Complete 4 → ⟪ (Toff012 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ Toff012 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-TOFF314 c4 = run b0
  where
  b0 : Chain (Toff012 ∷ Toff314 ∷ []) (Toff314 ∷ Toff012 ∷ [])
  b0 = at 1 1 (K3 ∷ CCZ134 ∷ K3⁻ ∷ []) (lw0 c4 (Toff314 ∷ []) (K3 ∷ CCZ134 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 0 2 (K3 ∷ Toff012 ∷ []) (lw4 c4 (Toff012 ∷ K3 ∷ []) (K3 ∷ Toff012 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ134 ∷ Toff012 ∷ []) (lem-auto-TOFF012-∣-CCZ314 c4) ▸
       at 2 2 (K3⁻ ∷ Toff012 ∷ []) (lw4 c4 (Toff012 ∷ K3⁻ ∷ []) (K3⁻ ∷ Toff012 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Toff314 ∷ []) (lw0 c4 (K3 ∷ CCZ134 ∷ K3⁻ ∷ []) (Toff314 ∷ []) tt tt Eq.refl) ▸ done

