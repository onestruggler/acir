{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D187 where

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
open import Examples.Groups.Clifford+CS.Five.D.D006 using (lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at243243 ; lem-auto-BOX⟨0·1234⟩-∣-CS13-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D145 using (lem-T312-beta-at14233241 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at2442 ; lem-auto-BOX⟨0·1234⟩-∣-CS14-at2442 ; lem-auto-BOX⟨0·1234⟩-∣-CSd14-at2442 ; lem-sym34-at14233142 ; lem-sym34-at14233241)
open import Examples.Groups.Clifford+CS.Five.D.D146 using (lem-beta-inv-at2442)
open import Examples.Groups.Clifford+CS.Five.D.D154 using (lem-X1-beta-at01142042 ; lem-sym12-at01102442 ; lem-sym12-at01142042)
open import Examples.Groups.Clifford+CS.Five.D.D156 using (lem-beta-T-at01102442)
open import Examples.Groups.Clifford+CS.Five.D.D163 using (lem-sym23-at01142042 ; lem-sym23-at0114233042)
open import Examples.Groups.Clifford+CS.Five.D.D169 using (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ143-at243243 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at243243 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D174 using (lem-auto-CS01-∣-SBOX⟨2·0·31·4⟩-at12213443)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-1-TOFF104)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-0-CCZ034 ; lem-nat-0-CCZ134)
open import Examples.Groups.Clifford+CS.Five.D.R013 using (lem-nat-2-CS12 ; lem-nat-2-CS13)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-nat-0-SBOX⟨0·1·3·2⟩ ; lem-nat-0-SBOX⟨1·0·3·2⟩ ; lem-nat-0-SBOXd⟨0·1·3·2⟩ ; lem-nat-0-SBOXd⟨1·0·3·2⟩ ; lem-nat-2-BOX⟨0·1432⟩ ; lem-nat-2-CS02 ; lem-nat-2-SBOX⟨1·0·2·3⟩ ; lem-nat-2-SBOX⟨1·0·43·2⟩ ; lem-nat-2-SBOXd⟨1·0·2·3⟩)
open import Examples.Groups.Clifford+CS.Five.D.R019 using (lem-nat-2-BOX⟨0·1423⟩ ; lem-nat-2-CS03)
open import Examples.Groups.Clifford+CS.Five.D.R020 using (lem-nat-2-SBOX⟨0·1·42·3⟩ ; lem-nat-2-SBOX⟨0·1·43·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R021 using (lem-nat-0-BOX⟨0·1432⟩)
open import Examples.Groups.Clifford+CS.Five.D.R022 using (lem-nat-0-BOX⟨1·0432⟩ ; lem-nat-1-BOX⟨2·0431⟩ ; lem-nat-2-SBOX⟨1·0·3·2⟩ ; lem-nat-2-SBOXd⟨1·0·3·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R023 using (lem-nat-2-SBOX⟨1·0·42·3⟩)
open import Examples.Groups.Clifford+CS.Five.D.R033 using (lem-nat-0-SBOX⟨0·1·43·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R034 using (lem-nat-0-SBOX⟨1·0·43·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R036 using (lem-nat-0-BOX⟨0·4312⟩ ; lem-nat-0-BOX⟨1·4302⟩)
open import Examples.Groups.Clifford+CS.Five.D.R039 using (lem-nat-0-BOX⟨0·4321⟩)
open import Examples.Groups.Clifford+CS.Five.D.R040 using (lem-nat-0-BOX⟨1·4320⟩)
-- auto BOX(0;1234) | CS13 @2442: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS13-at2442 : Complete 4 → ⟪ (Bx0-1432 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Bx0-1432 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS13-at2442 c4 = run b0
  where
  b0 : Chain (Bx0-1432 ∷ CS13 ∷ []) (CS13 ∷ Bx0-1432 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1423 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1432⟩ c4) ▸
       at 2 2 (CS12 ∷ Sw23 ∷ []) (lem-nat-2-CS13 c4) ▸
       at 1 2 (CS12 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS13-at243243 c4) ▸
       at 0 2 (CS13 ∷ Sw23 ∷ []) (lem-nat-2-CS12 c4) ▸
       at 1 2 (Bx0-1432 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1423⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CS13 @01102442: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS13-at01102442 : Complete 4 → ⟪ (Bx1-0432 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Bx1-0432 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS13-at01102442 c4 = run b0
  where
  b0 : Chain (Bx1-0432 ∷ CS03 ∷ []) (CS03 ∷ Bx1-0432 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1432 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0432⟩ c4) ▸
       at 2 2 (CS13 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS03 ∷ []) (CS13 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS13 ∷ Bx0-1432 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS13-at2442 c4) ▸
       at 0 2 (CS03 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS13 ∷ []) (CS03 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-0432 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1432⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ134 @2442: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at2442 : Complete 4 → ⟪ (Bx0-1432 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Bx0-1432 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at2442 c4 = run b0
  where
  b0 : Chain (Bx0-1432 ∷ CCZ123 ∷ []) (CCZ123 ∷ Bx0-1432 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1423 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1432⟩ c4) ▸
       at 2 2 (CCZ123 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ123 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at243243 c4) ▸
       at 0 2 (CCZ123 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1432 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1423⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ134 @01102442: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at01102442 : Complete 4 → ⟪ (Bx1-0432 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ Bx1-0432 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at01102442 c4 = run b0
  where
  b0 : Chain (Bx1-0432 ∷ CCZ023 ∷ []) (CCZ023 ∷ Bx1-0432 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1432 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0432⟩ c4) ▸
       at 2 2 (CCZ123 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ023 ∷ []) (CCZ123 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ123 ∷ Bx0-1432 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at2442 c4) ▸
       at 0 2 (CCZ023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ123 ∷ []) (CCZ023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-0432 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1432⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CS14 @01102442: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS14-at01102442 : Complete 4 → ⟪ (Bx1-0432 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ Bx1-0432 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS14-at01102442 c4 = run b0
  where
  b0 : Chain (Bx1-0432 ∷ CS02 ∷ []) (CS02 ∷ Bx1-0432 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1432 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0432⟩ c4) ▸
       at 2 2 (CS12 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS02 ∷ []) (CS12 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS12 ∷ Bx0-1432 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS14-at2442 c4) ▸
       at 0 2 (CS02 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-0432 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1432⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym34 @0114233042: 5 steps
lem-sym34-at0114233042 : Complete 4 → ⟪ (Bx1-4302 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-4320 ∷ []) ⟫ʷ
lem-sym34-at0114233042 c4 = run b0
  where
  b0 : Chain (Bx1-4302 ∷ []) (Bx1-4320 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-4312 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·4302⟩ c4) ▸
       at 1 1 (Bx0-4321 ∷ []) (lem-sym34-at14233142 c4) ▸
       at 0 2 (Bx1-4320 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·4321⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- T312-beta @0114233240: 8 steps
lem-T312-beta-at0114233240 : Complete 4 → ⟪ (Toff234 ∷ Bx1-4320 ∷ Toff234 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-4320 ∷ CCZ034 ∷ []) ⟫ʷ
lem-T312-beta-at0114233240 c4 = run b0
  where
  b0 : Chain (Toff234 ∷ Bx1-4320 ∷ Toff234 ∷ []) (Bx1-4320 ∷ CCZ034 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff234 ∷ Sw01 ∷ []) (c₂ (Swap) (Toff)) ▸
       at 2 2 (Bx0-4321 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·4320⟩ c4) ▸
       at 3 2 (Toff234 ∷ Sw01 ∷ []) (c₂ (Swap) (Toff)) ▸
       at 1 3 (Bx0-4321 ∷ CCZ134 ∷ []) (lem-T312-beta-at14233241 c4) ▸
       at 0 2 (Bx1-4320 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·4321⟩ c4) ▸
       at 1 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym34 @0114233240: 5 steps
lem-sym34-at0114233240 : Complete 4 → ⟪ (Bx1-4320 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-4302 ∷ []) ⟫ʷ
lem-sym34-at0114233240 c4 = run b0
  where
  b0 : Chain (Bx1-4320 ∷ []) (Bx1-4302 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-4321 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·4320⟩ c4) ▸
       at 1 1 (Bx0-4312 ∷ []) (lem-sym34-at14233241 c4) ▸
       at 0 2 (Bx1-4302 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·4312⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ231 @01102442: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at01102442 : Complete 4 → ⟪ (Bx1-0432 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Bx1-0432 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at01102442 c4 = run b0
  where
  b0 : Chain (Bx1-0432 ∷ CCZ034 ∷ []) (CCZ034 ∷ Bx1-0432 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1432 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0432⟩ c4) ▸
       at 2 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4) ▸
       at 1 2 (CCZ134 ∷ Bx0-1432 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at2442 c4) ▸
       at 0 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 1 2 (Bx1-0432 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1432⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CSd14 @01102442: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd14-at01102442 : Complete 4 → ⟪ (Bx1-0432 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ Bx1-0432 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd14-at01102442 c4 = run b0
  where
  b0 : Chain (Bx1-0432 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ Bx1-0432 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1432 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0432⟩ c4) ▸
       at 2 2 (CS12⁻ ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS02⁻ ∷ []) (CS12⁻ ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS12⁻ ∷ Bx0-1432 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd14-at2442 c4) ▸
       at 0 2 (CS02⁻ ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS12⁻ ∷ []) (CS02⁻ ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-0432 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1432⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- beta-inv @01102442: 5 steps
lem-beta-inv-at01102442 : Complete 4 → ⟪ (Bx1-0432 ∷ Bx1-0432 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-beta-inv-at01102442 c4 = run b0
  where
  b0 : Chain (Bx1-0432 ∷ Bx1-0432 ∷ []) []
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1432 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0432⟩ c4) ▸
       at 2 2 (Bx0-1432 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0432⟩ c4) ▸
       at 1 2 [] (lem-beta-inv-at2442 c4) ▸
       at 0 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- F5 CS03: 38 steps
lem-F5-CS03 : Complete 4 → ⟪ (X4 ∷ Sb1-0-43-2 ∷ X4 ∷ Sb1-0-43-2 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ []) ⟫ʷ
lem-F5-CS03 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (run b4))))
  where
  b0 : Chain (X4 ∷ Sb1-0-43-2 ∷ X4 ∷ Sb1-0-43-2 ∷ []) (CCZ023 ∷ Bx1-0432 ∷ X4 ∷ Toff234 ∷ CS02 ∷ Toff234 ∷ CS02⁻ ∷ X4 ∷ Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ [])
  b0 = at 1 1 (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (refl) ▸
       at 3 1 (CS02 ∷ []) (refl) ▸
       at 5 1 (CS02⁻ ∷ []) (refl) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (lw0 c4 [] (X4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Bx1-4032 ∷ []) (lem-sym12-at01102442 c4) ▸
       at 0 3 (CCZ023 ∷ Bx1-4032 ∷ []) (lem-X1-beta-at01142042 c4) ▸
       at 1 1 (Bx1-0432 ∷ []) (lem-sym12-at01142042 c4) ▸
       at 8 1 (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ023 ∷ Bx1-0432 ∷ X4 ∷ Toff234 ∷ CS02 ∷ Toff234 ∷ CS02⁻ ∷ X4 ∷ Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (CCZ023 ∷ CS03 ∷ CCZ023 ∷ CS02 ∷ Toff234 ∷ Toff234 ∷ Bx1-4032 ∷ Toff234 ∷ CS02⁻ ∷ Toff234 ∷ Bx1-0432 ∷ Toff234 ∷ CS02 ∷ Toff234 ∷ CS02⁻ ∷ [])
  b1 = at 10 1 (CS02 ∷ []) (refl) ▸
       at 12 1 (CS02⁻ ∷ []) (refl) ▸
       at 2 6 (CS03 ∷ CCZ023 ∷ CS02 ∷ Toff234 ∷ CS02⁻ ∷ Toff234 ∷ []) (pw1 c4 (X4 ∷ Toff234 ∷ CS02 ∷ Toff234 ∷ CS02⁻ ∷ X4 ∷ []) (CS03 ∷ CCZ023 ∷ CS02 ∷ Toff234 ∷ CS02⁻ ∷ Toff234 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS03 ∷ Bx1-0432 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS13-at01102442 c4) ▸
       at 2 2 (CCZ023 ∷ Bx1-0432 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ134-at01102442 c4) ▸
       at 3 2 (CS02 ∷ Bx1-0432 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS14-at01102442 c4) ▸
       at 4 0 (Toff234 ∷ Toff234 ∷ []) (lw0 c4 [] (Toff234 ∷ Toff234 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Bx1-4032 ∷ []) (lem-sym12-at01102442 c4) ▸ done

  b2 : Chain (CCZ023 ∷ CS03 ∷ CCZ023 ∷ CS02 ∷ Toff234 ∷ Toff234 ∷ Bx1-4032 ∷ Toff234 ∷ CS02⁻ ∷ Toff234 ∷ Bx1-0432 ∷ Toff234 ∷ CS02 ∷ Toff234 ∷ CS02⁻ ∷ []) (CCZ023 ∷ CS03 ∷ CCZ023 ∷ CS02 ∷ Toff234 ∷ CCZ034 ∷ CS02⁻ ∷ Bx1-0432 ∷ Toff234 ∷ Bx1-0432 ∷ Toff234 ∷ CS02 ∷ Toff234 ∷ CS02⁻ ∷ [])
  b2 = at 6 1 (Bx1-4302 ∷ []) (lem-sym23-at01142042 c4) ▸
       at 6 1 (Bx1-4320 ∷ []) (lem-sym34-at0114233042 c4) ▸
       at 5 3 (Bx1-4320 ∷ CCZ034 ∷ []) (lem-T312-beta-at0114233240 c4) ▸
       at 5 1 (Bx1-4302 ∷ []) (lem-sym34-at0114233240 c4) ▸
       at 5 1 (Bx1-4032 ∷ []) (lem-sym23-at0114233042 c4) ▸
       at 5 1 (Bx1-0432 ∷ []) (lem-sym12-at01142042 c4) ▸
       at 5 2 (CCZ034 ∷ Bx1-0432 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at01102442 c4) ▸
       at 6 2 (CS02⁻ ∷ Bx1-0432 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd14-at01102442 c4) ▸ done

  b3 : Chain (CCZ023 ∷ CS03 ∷ CCZ023 ∷ CS02 ∷ Toff234 ∷ CCZ034 ∷ CS02⁻ ∷ Bx1-0432 ∷ Toff234 ∷ Bx1-0432 ∷ Toff234 ∷ CS02 ∷ Toff234 ∷ CS02⁻ ∷ []) (CCZ023 ∷ CS03 ∷ CCZ023 ∷ CS02 ∷ Toff234 ∷ CCZ034 ∷ CS02⁻ ∷ Toff234 ∷ Bx1-0432 ∷ CCZ034 ∷ Bx1-0432 ∷ Toff234 ∷ CS02 ∷ Toff234 ∷ CS02⁻ ∷ [])
  b3 = at 7 0 (Toff234 ∷ Toff234 ∷ []) (lw0 c4 [] (Toff234 ∷ Toff234 ∷ []) tt tt Eq.refl) ▸
       at 9 1 (Bx1-4032 ∷ []) (lem-sym12-at01102442 c4) ▸
       at 9 1 (Bx1-4302 ∷ []) (lem-sym23-at01142042 c4) ▸
       at 9 1 (Bx1-4320 ∷ []) (lem-sym34-at0114233042 c4) ▸
       at 8 3 (Bx1-4320 ∷ CCZ034 ∷ []) (lem-T312-beta-at0114233240 c4) ▸
       at 8 1 (Bx1-4302 ∷ []) (lem-sym34-at0114233240 c4) ▸
       at 8 1 (Bx1-4032 ∷ []) (lem-sym23-at0114233042 c4) ▸
       at 8 1 (Bx1-0432 ∷ []) (lem-sym12-at01142042 c4) ▸ done

  b4 : Chain (CCZ023 ∷ CS03 ∷ CCZ023 ∷ CS02 ∷ Toff234 ∷ CCZ034 ∷ CS02⁻ ∷ Toff234 ∷ Bx1-0432 ∷ CCZ034 ∷ Bx1-0432 ∷ Toff234 ∷ CS02 ∷ Toff234 ∷ CS02⁻ ∷ []) (CS03 ∷ [])
  b4 = at 8 2 (CCZ034 ∷ Bx1-0432 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at01102442 c4) ▸
       at 1 5 (CCZ034 ∷ CS03 ∷ CCZ023 ∷ CS02 ∷ Toff234 ∷ []) (pw1 c4 (CS03 ∷ CCZ023 ∷ CS02 ∷ Toff234 ∷ CCZ034 ∷ []) (CCZ034 ∷ CS03 ∷ CCZ023 ∷ CS02 ∷ Toff234 ∷ []) tt tt Eq.refl) ▸
       at 2 7 (CCZ034 ∷ CS03 ∷ CCZ023 ∷ CS02 ∷ Toff234 ∷ CS02⁻ ∷ Toff234 ∷ []) (pw1 c4 (CS03 ∷ CCZ023 ∷ CS02 ∷ Toff234 ∷ CS02⁻ ∷ Toff234 ∷ CCZ034 ∷ []) (CCZ034 ∷ CS03 ∷ CCZ023 ∷ CS02 ∷ Toff234 ∷ CS02⁻ ∷ Toff234 ∷ []) tt tt Eq.refl) ▸
       at 1 2 [] (pw1 c4 (CCZ034 ∷ CCZ034 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 [] (lem-beta-inv-at01102442 c4) ▸
       at 0 11 (CS03 ∷ []) (pw1 c4 (CCZ023 ∷ CS03 ∷ CCZ023 ∷ CS02 ∷ Toff234 ∷ CS02⁻ ∷ Toff234 ∷ Toff234 ∷ CS02 ∷ Toff234 ∷ CS02⁻ ∷ []) (CS03 ∷ []) tt tt Eq.refl) ▸ done


-- auto CS01 | SBOX(2;0;31;4) @13213442: 7 steps
lem-auto-CS01-∣-SBOX⟨2·0·31·4⟩-at13213442 : Complete 4 → ⟪ (CS03 ∷ Sb1-0-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-43-2 ∷ CS03 ∷ []) ⟫ʷ
lem-auto-CS01-∣-SBOX⟨2·0·31·4⟩-at13213442 c4 = run b0
  where
  b0 : Chain (CS03 ∷ Sb1-0-43-2 ∷ []) (Sb1-0-43-2 ∷ CS03 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS02 ∷ Sw23 ∷ []) (lem-nat-2-CS03 c4) ▸
       at 2 2 (Sb1-0-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·43·2⟩ c4) ▸
       at 1 2 (Sb1-0-42-3 ∷ CS02 ∷ []) (lem-auto-CS01-∣-SBOX⟨2·0·31·4⟩-at12213443 c4) ▸
       at 0 2 (Sb1-0-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·42·3⟩ c4) ▸
       at 1 2 (CS03 ∷ Sw23 ∷ []) (lem-nat-2-CS02 c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- F4 CS03^0|CS03^1: 63 steps
lem-F4-CS03ᵖ0∣CS03ᵖ1 : Complete 4 → ⟪ (X4 ∷ Sb1-0-43-2 ∷ X4 ∷ Sb1-0-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-43-2 ∷ X4 ∷ Sb1-0-43-2 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS03ᵖ0∣CS03ᵖ1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (run b7)))))))
  where
  b0 : Chain (X4 ∷ Sb1-0-43-2 ∷ X4 ∷ Sb1-0-43-2 ∷ []) (CS03 ∷ CCZ014 ∷ Toff104 ∷ Bx0-132 ∷ Bx⁻1-02 ∷ CCZ013 ∷ Toff013 ∷ CZ02 ∷ Toff013 ∷ CCZ013 ∷ Toff104 ∷ CCZ014 ∷ [])
  b0 = at 0 4 (CS03 ∷ []) (lem-F5-CS03 c4) ▸
       at 1 0 (CCZ014 ∷ CCZ014 ∷ []) (pw2 c4 [] (CCZ014 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 2 0 (Toff104 ∷ Toff104 ∷ []) (pw2 c4 [] (Toff104 ∷ Toff104 ∷ []) tt tt Eq.refl) ▸
       at 3 0 (CCZ013 ∷ Toff013 ∷ CZ02 ∷ Toff013 ∷ CCZ013 ∷ CZ02 ∷ CZ02 ∷ CCZ013 ∷ Toff013 ∷ CZ02 ∷ Toff013 ∷ CCZ013 ∷ []) (lw4 c4 [] (CCZ013 ∷ Toff013 ∷ CZ02 ∷ Toff013 ∷ CCZ013 ∷ CZ02 ∷ CZ02 ∷ CCZ013 ∷ Toff013 ∷ CZ02 ∷ Toff013 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Bx1-02 ∷ []) (refl) ▸
       at 8 1 (Bx1-02 ∷ []) (refl) ▸
       at 3 6 (Bx0-132 ∷ []) (refl) ▸
       at 4 1 (Bx⁻1-02 ∷ []) (refl) ▸ done

  b1 : Chain (CS03 ∷ CCZ014 ∷ Toff104 ∷ Bx0-132 ∷ Bx⁻1-02 ∷ CCZ013 ∷ Toff013 ∷ CZ02 ∷ Toff013 ∷ CCZ013 ∷ Toff104 ∷ CCZ014 ∷ []) (CS03 ∷ CCZ014 ∷ Toff104 ∷ Bx0-132 ∷ Toff104 ∷ CCZ014 ∷ Bx0-132 ∷ CZ02 ∷ CCZ013 ∷ Toff013 ∷ CZ02 ∷ Toff013 ∷ CCZ013 ∷ CCZ014 ∷ Toff104 ∷ Bx⁻0-132 ∷ Toff104 ∷ CCZ014 ∷ [])
  b1 = at 7 1 (Bx⁻1-02 ∷ []) (refl) ▸
       at 4 6 (Bx⁻0-132 ∷ []) (refl) ▸
       at 4 0 (Toff104 ∷ Toff104 ∷ []) (pw2 c4 [] (Toff104 ∷ Toff104 ∷ []) tt tt Eq.refl) ▸
       at 5 0 (CCZ014 ∷ CCZ014 ∷ []) (pw2 c4 [] (CCZ014 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 6 0 (CCZ013 ∷ Toff013 ∷ CZ02 ∷ Toff013 ∷ CCZ013 ∷ CZ02 ∷ CZ02 ∷ CCZ013 ∷ Toff013 ∷ CZ02 ∷ Toff013 ∷ CCZ013 ∷ []) (lw4 c4 [] (CCZ013 ∷ Toff013 ∷ CZ02 ∷ Toff013 ∷ CCZ013 ∷ CZ02 ∷ CZ02 ∷ CCZ013 ∷ Toff013 ∷ CZ02 ∷ Toff013 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 8 1 (Bx1-02 ∷ []) (refl) ▸
       at 11 1 (Bx1-02 ∷ []) (refl) ▸
       at 6 6 (Bx0-132 ∷ []) (refl) ▸ done

  b2 : Chain (CS03 ∷ CCZ014 ∷ Toff104 ∷ Bx0-132 ∷ Toff104 ∷ CCZ014 ∷ Bx0-132 ∷ CZ02 ∷ CCZ013 ∷ Toff013 ∷ CZ02 ∷ Toff013 ∷ CCZ013 ∷ CCZ014 ∷ Toff104 ∷ Bx⁻0-132 ∷ Toff104 ∷ CCZ014 ∷ []) (CS03 ∷ Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ CS02⁻ ∷ Toff234 ∷ Bx⁻1-0432 ∷ [])
  b2 = at 7 1 (Bx⁻1-02 ∷ []) (refl) ▸
       at 10 1 (Bx⁻1-02 ∷ []) (refl) ▸
       at 7 6 (Bx⁻0-132 ∷ []) (refl) ▸
       at 1 6 (Bx1-0432 ∷ []) (refl) ▸
       at 2 6 (Bx⁻1-0432 ∷ []) (refl) ▸
       at 2 0 (Toff234 ∷ Toff234 ∷ []) (lw0 c4 [] (Toff234 ∷ Toff234 ∷ []) tt tt Eq.refl) ▸
       at 3 0 (CS02 ∷ CS02⁻ ∷ []) (lw4 c4 [] (CS02 ∷ CS02⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Sb1-0-2-3 ∷ []) (refl) ▸ done

  b3 : Chain (CS03 ∷ Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ CS02⁻ ∷ Toff234 ∷ Bx⁻1-0432 ∷ []) (Sb1-0-43-2 ∷ CS03 ∷ Sb⁻1-0-43-2 ∷ [])
  b3 = at 4 1 (Sb⁻1-0-2-3 ∷ []) (refl) ▸
       at 4 0 (Toff234 ∷ Toff234 ∷ []) (lw0 c4 [] (Toff234 ∷ Toff234 ∷ []) tt tt Eq.refl) ▸
       at 5 0 (CS02⁻ ∷ CS02 ∷ []) (lw4 c4 [] (CS02⁻ ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Sb⁻1-0-2-3 ∷ []) (refl) ▸
       at 6 1 (Sb1-0-2-3 ∷ []) (refl) ▸
       at 1 5 (Sb1-0-43-2 ∷ []) (refl) ▸
       at 2 5 (Sb⁻1-0-43-2 ∷ []) (refl) ▸
       at 0 2 (Sb1-0-43-2 ∷ CS03 ∷ []) (lem-auto-CS01-∣-SBOX⟨2·0·31·4⟩-at13213442 c4) ▸ done

  b4 : Chain (Sb1-0-43-2 ∷ CS03 ∷ Sb⁻1-0-43-2 ∷ []) (Sb1-0-43-2 ∷ X4 ∷ Sb1-0-43-2 ∷ X4 ∷ Bx1-0432 ∷ Toff234 ∷ CS02 ∷ Sb⁻1-0-2-3 ∷ Toff234 ∷ Bx⁻1-0432 ∷ [])
  b4 = at 1 1 (X4 ∷ Sb1-0-43-2 ∷ X4 ∷ Sb1-0-43-2 ∷ []) (sym (lem-F5-CS03 c4)) ▸
       at 5 1 (Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ Toff234 ∷ Bx⁻1-0432 ∷ []) (refl) ▸
       at 4 1 (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (refl) ▸
       at 8 1 (CS02⁻ ∷ []) (refl) ▸
       at 9 1 (CS02 ∷ []) (refl) ▸
       at 8 2 [] (lw4 c4 (CS02⁻ ∷ CS02 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 [] (lw0 c4 (Toff234 ∷ Toff234 ∷ []) [] tt tt Eq.refl) ▸
       at 6 1 (CS02 ∷ []) (refl) ▸ done

  b5 : Chain (Sb1-0-43-2 ∷ X4 ∷ Sb1-0-43-2 ∷ X4 ∷ Bx1-0432 ∷ Toff234 ∷ CS02 ∷ Sb⁻1-0-2-3 ∷ Toff234 ∷ Bx⁻1-0432 ∷ []) (Sb1-0-43-2 ∷ X4 ∷ Sb1-0-43-2 ∷ X4 ∷ CCZ014 ∷ Toff104 ∷ Bx0-132 ∷ Toff104 ∷ CCZ014 ∷ CCZ013 ∷ Toff013 ∷ CZ02 ∷ Toff013 ∷ CCZ013 ∷ CZ02 ∷ Bx⁻0-132 ∷ CCZ014 ∷ Toff104 ∷ Bx⁻0-132 ∷ Toff104 ∷ CCZ014 ∷ [])
  b5 = at 7 1 (CS02⁻ ∷ []) (refl) ▸
       at 6 2 [] (lw4 c4 (CS02 ∷ CS02⁻ ∷ []) [] tt tt Eq.refl) ▸
       at 5 2 [] (lw0 c4 (Toff234 ∷ Toff234 ∷ []) [] tt tt Eq.refl) ▸
       at 5 1 (Bx⁻0-132 ∷ CCZ014 ∷ Toff104 ∷ Bx⁻0-132 ∷ Toff104 ∷ CCZ014 ∷ []) (refl) ▸
       at 4 1 (CCZ014 ∷ Toff104 ∷ Bx0-132 ∷ Toff104 ∷ CCZ014 ∷ Bx0-132 ∷ []) (refl) ▸
       at 9 1 (CCZ013 ∷ Toff013 ∷ Bx1-02 ∷ Toff013 ∷ CCZ013 ∷ Bx1-02 ∷ []) (refl) ▸
       at 11 1 (CZ02 ∷ []) (refl) ▸
       at 14 1 (CZ02 ∷ []) (refl) ▸ done

  b6 : Chain (Sb1-0-43-2 ∷ X4 ∷ Sb1-0-43-2 ∷ X4 ∷ CCZ014 ∷ Toff104 ∷ Bx0-132 ∷ Toff104 ∷ CCZ014 ∷ CCZ013 ∷ Toff013 ∷ CZ02 ∷ Toff013 ∷ CCZ013 ∷ CZ02 ∷ Bx⁻0-132 ∷ CCZ014 ∷ Toff104 ∷ Bx⁻0-132 ∷ Toff104 ∷ CCZ014 ∷ []) (Sb1-0-43-2 ∷ X4 ∷ Sb1-0-43-2 ∷ X4 ∷ CCZ014 ∷ Toff104 ∷ CCZ013 ∷ Toff013 ∷ CZ02 ∷ Toff013 ∷ CCZ013 ∷ Bx1-02 ∷ Bx⁻0-132 ∷ Toff104 ∷ CCZ014 ∷ [])
  b6 = at 15 1 (Bx⁻1-02 ∷ CCZ013 ∷ Toff013 ∷ Bx⁻1-02 ∷ Toff013 ∷ CCZ013 ∷ []) (refl) ▸
       at 15 1 (CZ02 ∷ []) (refl) ▸
       at 18 1 (CZ02 ∷ []) (refl) ▸
       at 9 12 [] (lw4 c4 (CCZ013 ∷ Toff013 ∷ CZ02 ∷ Toff013 ∷ CCZ013 ∷ CZ02 ∷ CZ02 ∷ CCZ013 ∷ Toff013 ∷ CZ02 ∷ Toff013 ∷ CCZ013 ∷ []) [] tt tt Eq.refl) ▸
       at 8 2 [] (pw2 c4 (CCZ014 ∷ CCZ014 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 [] (pw2 c4 (Toff104 ∷ Toff104 ∷ []) [] tt tt Eq.refl) ▸
       at 6 1 (CCZ013 ∷ Toff013 ∷ Bx1-02 ∷ Toff013 ∷ CCZ013 ∷ Bx1-02 ∷ []) (refl) ▸
       at 8 1 (CZ02 ∷ []) (refl) ▸ done

  b7 : Chain (Sb1-0-43-2 ∷ X4 ∷ Sb1-0-43-2 ∷ X4 ∷ CCZ014 ∷ Toff104 ∷ CCZ013 ∷ Toff013 ∷ CZ02 ∷ Toff013 ∷ CCZ013 ∷ Bx1-02 ∷ Bx⁻0-132 ∷ Toff104 ∷ CCZ014 ∷ []) (Sb1-0-43-2 ∷ X4 ∷ Sb1-0-43-2 ∷ X4 ∷ [])
  b7 = at 11 1 (CZ02 ∷ []) (refl) ▸
       at 12 1 (Bx⁻1-02 ∷ CCZ013 ∷ Toff013 ∷ Bx⁻1-02 ∷ Toff013 ∷ CCZ013 ∷ []) (refl) ▸
       at 12 1 (CZ02 ∷ []) (refl) ▸
       at 15 1 (CZ02 ∷ []) (refl) ▸
       at 6 12 [] (lw4 c4 (CCZ013 ∷ Toff013 ∷ CZ02 ∷ Toff013 ∷ CCZ013 ∷ CZ02 ∷ CZ02 ∷ CCZ013 ∷ Toff013 ∷ CZ02 ∷ Toff013 ∷ CCZ013 ∷ []) [] tt tt Eq.refl) ▸
       at 5 2 [] (pw2 c4 (Toff104 ∷ Toff104 ∷ []) [] tt tt Eq.refl) ▸
       at 4 2 [] (pw2 c4 (CCZ014 ∷ CCZ014 ∷ []) [] tt tt Eq.refl) ▸ done


-- beta-T @02102441: 8 steps
lem-beta-T-at02102441 : Complete 4 → ⟪ (Bx2-0431 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) ⟫ʷ
lem-beta-T-at02102441 c4 = run b0
  where
  b0 : Chain (Bx2-0431 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-0432 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0431⟩ c4) ▸
       at 1 1 (Toff104 ∷ CCZ123 ∷ Toff104 ∷ CCZ123 ∷ []) (lem-beta-T-at01102442 c4) ▸
       at 0 2 (Toff204 ∷ Sw12 ∷ []) (lem-nat-1-TOFF104 c4) ▸
       at 1 2 (CCZ123 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff204 ∷ Sw12 ∷ []) (lem-nat-1-TOFF104 c4) ▸
       at 3 2 (CCZ123 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CCZ143 @2442: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ143-at2442 : Complete 4 → ⟪ (Sb0-1-43-2 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ143-at2442 c4 = run b0
  where
  b0 : Chain (Sb0-1-43-2 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sb0-1-43-2 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·43·2⟩ c4) ▸
       at 2 2 (CCZ123 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ123 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ143-at243243 c4) ▸
       at 0 2 (CCZ123 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·42·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CCZ143 @01102442: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ143-at01102442 : Complete 4 → ⟪ (Sb1-0-43-2 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ Sb1-0-43-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ143-at01102442 c4 = run b0
  where
  b0 : Chain (Sb1-0-43-2 ∷ CCZ023 ∷ []) (CCZ023 ∷ Sb1-0-43-2 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-43-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·43·2⟩ c4) ▸
       at 2 2 (CCZ123 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ023 ∷ []) (CCZ123 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ123 ∷ Sb0-1-43-2 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ143-at2442 c4) ▸
       at 0 2 (CCZ023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ123 ∷ []) (CCZ023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb1-0-43-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·43·2⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | SBOX(1;0;3;4) @2442: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at2442 : Complete 4 → ⟪ (Sb0-1-43-2 ∷ Sb1-0-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-3-2 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at2442 c4 = run b0
  where
  b0 : Chain (Sb0-1-43-2 ∷ Sb1-0-3-2 ∷ []) (Sb1-0-3-2 ∷ Sb0-1-43-2 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·43·2⟩ c4) ▸
       at 2 2 (Sb1-0-2-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·3·2⟩ c4) ▸
       at 1 2 (Sb1-0-2-3 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at243243 c4) ▸
       at 0 2 (Sb1-0-3-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·2·3⟩ c4) ▸
       at 1 2 (Sb0-1-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·42·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | SBOX(1;0;3;4) @01102442: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at01102442 : Complete 4 → ⟪ (Sb1-0-43-2 ∷ Sb0-1-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-3-2 ∷ Sb1-0-43-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at01102442 c4 = run b0
  where
  b0 : Chain (Sb1-0-43-2 ∷ Sb0-1-3-2 ∷ []) (Sb0-1-3-2 ∷ Sb1-0-43-2 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-43-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·43·2⟩ c4) ▸
       at 2 2 (Sb1-0-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·3·2⟩ c4) ▸
       at 1 2 (Sb1-0-3-2 ∷ Sb0-1-43-2 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOX⟨1·0·3·4⟩-at2442 c4) ▸
       at 0 2 (Sb0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·3·2⟩ c4) ▸
       at 1 2 (Sb1-0-43-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·43·2⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | SBOXd(1;0;3;4) @2442: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at2442 : Complete 4 → ⟪ (Sb0-1-43-2 ∷ Sb⁻1-0-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-3-2 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at2442 c4 = run b0
  where
  b0 : Chain (Sb0-1-43-2 ∷ Sb⁻1-0-3-2 ∷ []) (Sb⁻1-0-3-2 ∷ Sb0-1-43-2 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·43·2⟩ c4) ▸
       at 2 2 (Sb⁻1-0-2-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·0·3·2⟩ c4) ▸
       at 1 2 (Sb⁻1-0-2-3 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at243243 c4) ▸
       at 0 2 (Sb⁻1-0-3-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·0·2·3⟩ c4) ▸
       at 1 2 (Sb0-1-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·42·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | SBOXd(1;0;3;4) @01102442: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at01102442 : Complete 4 → ⟪ (Sb1-0-43-2 ∷ Sb⁻0-1-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-3-2 ∷ Sb1-0-43-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at01102442 c4 = run b0
  where
  b0 : Chain (Sb1-0-43-2 ∷ Sb⁻0-1-3-2 ∷ []) (Sb⁻0-1-3-2 ∷ Sb1-0-43-2 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-43-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·43·2⟩ c4) ▸
       at 2 2 (Sb⁻1-0-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨0·1·3·2⟩ c4) ▸
       at 1 2 (Sb⁻1-0-3-2 ∷ Sb0-1-43-2 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-SBOXd⟨1·0·3·4⟩-at2442 c4) ▸
       at 0 2 (Sb⁻0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·3·2⟩ c4) ▸
       at 1 2 (Sb1-0-43-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·43·2⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done

