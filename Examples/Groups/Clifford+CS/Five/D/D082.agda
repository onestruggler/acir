{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D082 where

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
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-auto-CCZ012-∣-CCZ314-at12243143)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-sym23-at0310213442)
open import Examples.Groups.Clifford+CS.Five.D.D010 using (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ023-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D011 using (lem-beta-T-at0210213443)
open import Examples.Groups.Clifford+CS.Five.D.D080 using (lem-auto-CCZ012-∣-BOX⟨3·4012⟩ ; lem-auto-CCZ012-∣-SBOX⟨3·4·01·2⟩ ; lem-auto-CSd01-∣-BOX⟨2·0134⟩ ; lem-auto-S0-∣-BOX⟨1·0234⟩ ; lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF423 ; lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ023)
open import Examples.Groups.Clifford+CS.Five.D.D081 using (lem-sym34-at0310243142)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-1-CCZ024 ; lem-nat-1-CCZ034 ; lem-nat-2-CCZ012 ; lem-nat-2-CCZ013 ; lem-nat-2-CCZ024 ; lem-nat-2-CCZ034 ; lem-nat-3-CCZ014 ; lem-nat-3-CCZ024)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-1-CCZ014 ; lem-nat-2-TOFF201 ; lem-nat-3-CCZ013 ; lem-nat-3-CCZ023)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-0-CCZ024 ; lem-nat-0-CCZ124 ; lem-nat-1-TOFF301)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-0-BOX⟨3·4102⟩ ; lem-nat-0-CCZ034 ; lem-nat-0-CCZ134)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-0-BOX⟨3·4012⟩ ; lem-nat-1-BOX⟨1·0423⟩)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-nat-1-BOX⟨1·0234⟩ ; lem-nat-1-BOX⟨2·0134⟩ ; lem-nat-1-BOX⟨2·0413⟩ ; lem-nat-2-BOX⟨3·0142⟩)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-nat-0-BOX⟨2·0413⟩ ; lem-nat-0-BOX⟨2·1403⟩ ; lem-nat-0-SBOX⟨0·1·42·3⟩ ; lem-nat-0-SBOX⟨1·0·42·3⟩ ; lem-nat-1-BOX⟨3·0412⟩ ; lem-nat-1-CSd02 ; lem-nat-1-SBOX⟨1·0·42·3⟩ ; lem-nat-1-SBOX⟨2·0·41·3⟩ ; lem-nat-2-CSd02 ; lem-nat-2-SBOX⟨0·1·23·4⟩ ; lem-nat-2-SBOX⟨0·1·32·4⟩ ; lem-nat-3-SBOX⟨0·1·32·4⟩ ; lem-nat-3-SBOX⟨0·1·42·3⟩)
open import Examples.Groups.Clifford+CS.Five.D.R015 using (lem-nat-1-CSd01)
open import Examples.Groups.Clifford+CS.Five.D.R016 using (lem-nat-1-CSd04 ; lem-nat-3-CSd04)
open import Examples.Groups.Clifford+CS.Five.D.R017 using (lem-nat-2-BOX⟨1·0234⟩ ; lem-nat-3-CSd03)
open import Examples.Groups.Clifford+CS.Five.D.R018 using (lem-nat-2-SBOXd⟨0·1·23·4⟩ ; lem-nat-2-SBOXd⟨0·1·32·4⟩)
open import Examples.Groups.Clifford+CS.Five.D.R019 using (lem-nat-2-CSd03)
open import Examples.Groups.Clifford+CS.Five.D.R022 using (lem-nat-0-SBOXd⟨0·1·42·3⟩ ; lem-nat-0-SBOXd⟨1·0·42·3⟩ ; lem-nat-1-SBOXd⟨1·0·42·3⟩ ; lem-nat-1-SBOXd⟨2·0·41·3⟩ ; lem-nat-3-SBOXd⟨0·1·32·4⟩ ; lem-nat-3-SBOXd⟨0·1·42·3⟩)
open import Examples.Groups.Clifford+CS.Five.D.R023 using (lem-nat-1-BOX⟨3·0241⟩)
open import Examples.Groups.Clifford+CS.Five.D.R024 using (lem-nat-0-SBOX⟨2·1·40·3⟩ ; lem-nat-1-BOX⟨1·2403⟩ ; lem-nat-1-BOX⟨2·1403⟩ ; lem-nat-1-SBOX⟨1·2·40·3⟩ ; lem-nat-2-BOX⟨1·3402⟩ ; lem-nat-2-SBOX⟨1·3·40·2⟩ ; lem-nat-3-BOX⟨2·3401⟩ ; lem-nat-3-SBOX⟨2·3·40·1⟩)
open import Examples.Groups.Clifford+CS.Five.D.R025 using (lem-nat-1-BOX⟨1·3402⟩ ; lem-nat-1-BOX⟨2·3401⟩ ; lem-nat-2-BOX⟨3·4201⟩ ; lem-nat-2-SBOX⟨3·4·20·1⟩)
open import Examples.Groups.Clifford+CS.Five.D.R027 using (lem-nat-0-SBOX⟨2·0·41·3⟩ ; lem-nat-1-SBOX⟨1·3·40·2⟩ ; lem-nat-1-SBOX⟨2·1·40·3⟩ ; lem-nat-1-SBOX⟨2·3·40·1⟩ ; lem-nat-2-BOX⟨1·2403⟩ ; lem-nat-2-SBOX⟨1·2·40·3⟩)
open import Examples.Groups.Clifford+CS.Five.D.R028 using (lem-nat-0-SBOX⟨3·4·01·2⟩ ; lem-nat-0-SBOX⟨3·4·10·2⟩ ; lem-nat-1-BOX⟨3·0421⟩ ; lem-nat-1-BOX⟨3·4102⟩ ; lem-nat-1-BOX⟨3·4201⟩ ; lem-nat-1-SBOX⟨3·4·10·2⟩ ; lem-nat-1-SBOX⟨3·4·20·1⟩ ; lem-nat-2-BOX⟨1·0324⟩ ; lem-nat-2-BOX⟨2·4301⟩ ; lem-nat-2-SBOX⟨2·4·30·1⟩ ; lem-nat-3-BOX⟨1·0423⟩ ; lem-nat-3-BOX⟨2·4301⟩ ; lem-nat-3-SBOX⟨2·4·30·1⟩)
open import Examples.Groups.Clifford+CS.Five.D.R029 using (lem-nat-3-BOX⟨1·0324⟩)
-- beta-T @0310213442: 8 steps
lem-beta-T-at0310213442 : Complete 4 → ⟪ (Bx3-0142 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ []) ⟫ʷ
lem-beta-T-at0310213442 c4 = run b0
  where
  b0 : Chain (Bx3-0142 ∷ []) (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx2-0143 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0142⟩ c4) ▸
       at 1 1 (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-beta-T-at0210213443 c4) ▸
       at 0 2 (Toff301 ∷ Sw23 ∷ []) (lem-nat-2-TOFF201 c4) ▸
       at 1 2 (CCZ234 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff301 ∷ Sw23 ∷ []) (lem-nat-2-TOFF201 c4) ▸
       at 3 2 (CCZ234 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- beta-T @03103441: 8 steps
lem-beta-T-at03103441 : Complete 4 → ⟪ (Bx3-0241 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ []) ⟫ʷ
lem-beta-T-at03103441 c4 = run b0
  where
  b0 : Chain (Bx3-0241 ∷ []) (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-0142 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0241⟩ c4) ▸
       at 1 1 (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ []) (lem-beta-T-at0310213442 c4) ▸
       at 0 2 (Toff302 ∷ Sw12 ∷ []) (lem-nat-1-TOFF301 c4) ▸
       at 1 2 (CCZ134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ234 ∷ []) (CCZ134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff302 ∷ Sw12 ∷ []) (lem-nat-1-TOFF301 c4) ▸
       at 3 2 (CCZ134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ234 ∷ []) (CCZ134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym23 @03103441: 5 steps
lem-sym23-at03103441 : Complete 4 → ⟪ (Bx3-0241 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0421 ∷ []) ⟫ʷ
lem-sym23-at03103441 c4 = run b0
  where
  b0 : Chain (Bx3-0241 ∷ []) (Bx3-0421 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-0142 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0241⟩ c4) ▸
       at 1 1 (Bx3-0412 ∷ []) (lem-sym23-at0310213442 c4) ▸
       at 0 2 (Bx3-0421 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0412⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym34 @0310243241: 5 steps
lem-sym34-at0310243241 : Complete 4 → ⟪ (Bx3-0421 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ []) ⟫ʷ
lem-sym34-at0310243241 c4 = run b0
  where
  b0 : Chain (Bx3-0421 ∷ []) (Bx3-0412 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-0412 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0421⟩ c4) ▸
       at 1 1 (Bx3-0421 ∷ []) (lem-sym34-at0310243142 c4) ▸
       at 0 2 (Bx3-0412 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0421⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;23;4) | CCZ023 @2332: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ023-at2332 : Complete 4 → ⟪ (Sb⁻0-1-32-4 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ Sb⁻0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ023-at2332 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-32-4 ∷ CCZ023 ∷ []) (CCZ023 ∷ Sb⁻0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·32·4⟩ c4) ▸
       at 2 2 (CCZ023 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ023 ∷ []) (CCZ023 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ023 ∷ Sb⁻0-1-23-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ023 c4) ▸
       at 0 2 (CCZ023 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ023 ∷ []) (CCZ023 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;23;4) | CCZ023 @243243: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ023-at243243 : Complete 4 → ⟪ (Sb⁻0-1-42-3 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Sb⁻0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ023-at243243 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-42-3 ∷ CCZ024 ∷ []) (CCZ024 ∷ Sb⁻0-1-42-3 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·42·3⟩ c4) ▸
       at 2 2 (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 c4) ▸
       at 1 2 (CCZ023 ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ023-at2332 c4) ▸
       at 0 2 (CCZ024 ∷ Sw34 ∷ []) (lem-nat-3-CCZ023 c4) ▸
       at 1 2 (Sb⁻0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·32·4⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;23;4) | CCZ023 @0110243243: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ023-at0110243243 : Complete 4 → ⟪ (Sb⁻1-0-42-3 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Sb⁻1-0-42-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ023-at0110243243 c4 = run b0
  where
  b0 : Chain (Sb⁻1-0-42-3 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sb⁻1-0-42-3 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·42·3⟩ c4) ▸
       at 2 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 1 2 (CCZ024 ∷ Sb⁻0-1-42-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ023-at243243 c4) ▸
       at 0 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 1 2 (Sb⁻1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨0·1·42·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;23;4) | CCZ023 @0210243143: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ023-at0210243143 : Complete 4 → ⟪ (Sb⁻2-0-41-3 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Sb⁻2-0-41-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ023-at0210243143 c4 = run b0
  where
  b0 : Chain (Sb⁻2-0-41-3 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sb⁻2-0-41-3 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·41·3⟩ c4) ▸
       at 2 2 (CCZ124 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ124 ∷ Sb⁻1-0-42-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CCZ023-at0110243243 c4) ▸
       at 0 2 (CCZ124 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·0·42·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | BOX(3;4012) @0110: 7 steps
lem-auto-CCZ012-∣-BOX⟨3·4012⟩-at0110 : Complete 4 → ⟪ (CCZ012 ∷ Bx3-4102 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4102 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·4012⟩-at0110 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Bx3-4102 ∷ []) (Bx3-4102 ∷ CCZ012 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx3-4012 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·4102⟩ c4) ▸
       at 1 2 (Bx3-4012 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·4012⟩ c4) ▸
       at 0 2 (Bx3-4102 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·4012⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | BOX(3;4012) @021021: 7 steps
lem-auto-CCZ012-∣-BOX⟨3·4012⟩-at021021 : Complete 4 → ⟪ (CCZ012 ∷ Bx3-4201 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4201 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·4012⟩-at021021 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Bx3-4201 ∷ []) (Bx3-4201 ∷ CCZ012 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx3-4102 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·4201⟩ c4) ▸
       at 1 2 (Bx3-4102 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·4012⟩-at0110 c4) ▸
       at 0 2 (Bx3-4201 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·4102⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | BOX(3;4012) @03102132: 7 steps
lem-auto-CCZ012-∣-BOX⟨3·4012⟩-at03102132 : Complete 4 → ⟪ (CCZ013 ∷ Bx2-4301 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4301 ∷ CCZ013 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·4012⟩-at03102132 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ Bx2-4301 ∷ []) (Bx2-4301 ∷ CCZ013 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 2 2 (Bx3-4201 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·4301⟩ c4) ▸
       at 1 2 (Bx3-4201 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·4012⟩-at021021 c4) ▸
       at 0 2 (Bx2-4301 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·4201⟩ c4) ▸
       at 1 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | BOX(3;4012) @0410213243: 7 steps
lem-auto-CCZ012-∣-BOX⟨3·4012⟩-at0410213243 : Complete 4 → ⟪ (CCZ014 ∷ Bx2-3401 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3401 ∷ CCZ014 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·4012⟩-at0410213243 c4 = run b0
  where
  b0 : Chain (CCZ014 ∷ Bx2-3401 ∷ []) (Bx2-3401 ∷ CCZ014 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4) ▸
       at 2 2 (Bx2-4301 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·3401⟩ c4) ▸
       at 1 2 (Bx2-4301 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·4012⟩-at03102132 c4) ▸
       at 0 2 (Bx2-3401 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·4301⟩ c4) ▸
       at 1 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | BOX(3;4012) @04103143: 7 steps
lem-auto-CCZ012-∣-BOX⟨3·4012⟩-at04103143 : Complete 4 → ⟪ (CCZ024 ∷ Bx1-3402 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3402 ∷ CCZ024 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·4012⟩-at04103143 c4 = run b0
  where
  b0 : Chain (CCZ024 ∷ Bx1-3402 ∷ []) (Bx1-3402 ∷ CCZ024 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 2 2 (Bx2-3401 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·3402⟩ c4) ▸
       at 1 2 (Bx2-3401 ∷ CCZ014 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·4012⟩-at0410213243 c4) ▸
       at 0 2 (Bx1-3402 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·3401⟩ c4) ▸
       at 1 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | BOX(3;4012) @0410233142: 7 steps
lem-auto-CCZ012-∣-BOX⟨3·4012⟩-at0410233142 : Complete 4 → ⟪ (CCZ034 ∷ Bx1-2403 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2403 ∷ CCZ034 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·4012⟩-at0410233142 c4 = run b0
  where
  b0 : Chain (CCZ034 ∷ Bx1-2403 ∷ []) (Bx1-2403 ∷ CCZ034 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 2 2 (Bx1-3402 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·2403⟩ c4) ▸
       at 1 2 (Bx1-3402 ∷ CCZ024 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·4012⟩-at04103143 c4) ▸
       at 0 2 (Bx1-2403 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·3402⟩ c4) ▸
       at 1 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | BOX(3;4012) @0410233241: 7 steps
lem-auto-CCZ012-∣-BOX⟨3·4012⟩-at0410233241 : Complete 4 → ⟪ (CCZ034 ∷ Bx2-1403 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1403 ∷ CCZ034 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·4012⟩-at0410233241 c4 = run b0
  where
  b0 : Chain (CCZ034 ∷ Bx2-1403 ∷ []) (Bx2-1403 ∷ CCZ034 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 2 2 (Bx1-2403 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·1403⟩ c4) ▸
       at 1 2 (Bx1-2403 ∷ CCZ034 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·4012⟩-at0410233142 c4) ▸
       at 0 2 (Bx2-1403 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·2403⟩ c4) ▸
       at 1 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | BOX(3;4012) @04233240: 7 steps
lem-auto-CCZ012-∣-BOX⟨3·4012⟩-at04233240 : Complete 4 → ⟪ (CCZ134 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ CCZ134 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·4012⟩-at04233240 c4 = run b0
  where
  b0 : Chain (CCZ134 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ CCZ134 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 2 2 (Bx2-1403 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·0413⟩ c4) ▸
       at 1 2 (Bx2-1403 ∷ CCZ034 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·4012⟩-at0410233241 c4) ▸
       at 0 2 (Bx2-0413 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·1403⟩ c4) ▸
       at 1 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | SBOX(3;4;01;2) @0110: 7 steps
lem-auto-CCZ012-∣-SBOX⟨3·4·01·2⟩-at0110 : Complete 4 → ⟪ (CCZ012 ∷ Sb3-4-10-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-4-10-2 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨3·4·01·2⟩-at0110 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Sb3-4-10-2 ∷ []) (Sb3-4-10-2 ∷ CCZ012 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb3-4-01-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·4·10·2⟩ c4) ▸
       at 1 2 (Sb3-4-01-2 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨3·4·01·2⟩ c4) ▸
       at 0 2 (Sb3-4-10-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·4·01·2⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | SBOX(3;4;01;2) @021021: 7 steps
lem-auto-CCZ012-∣-SBOX⟨3·4·01·2⟩-at021021 : Complete 4 → ⟪ (CCZ012 ∷ Sb3-4-20-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-4-20-1 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨3·4·01·2⟩-at021021 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Sb3-4-20-1 ∷ []) (Sb3-4-20-1 ∷ CCZ012 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb3-4-10-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·4·20·1⟩ c4) ▸
       at 1 2 (Sb3-4-10-2 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨3·4·01·2⟩-at0110 c4) ▸
       at 0 2 (Sb3-4-20-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·4·10·2⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | SBOX(3;4;01;2) @03102132: 7 steps
lem-auto-CCZ012-∣-SBOX⟨3·4·01·2⟩-at03102132 : Complete 4 → ⟪ (CCZ013 ∷ Sb2-4-30-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-30-1 ∷ CCZ013 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨3·4·01·2⟩-at03102132 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ Sb2-4-30-1 ∷ []) (Sb2-4-30-1 ∷ CCZ013 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 2 2 (Sb3-4-20-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨2·4·30·1⟩ c4) ▸
       at 1 2 (Sb3-4-20-1 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨3·4·01·2⟩-at021021 c4) ▸
       at 0 2 (Sb2-4-30-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·4·20·1⟩ c4) ▸
       at 1 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | SBOX(3;4;01;2) @0410213243: 7 steps
lem-auto-CCZ012-∣-SBOX⟨3·4·01·2⟩-at0410213243 : Complete 4 → ⟪ (CCZ014 ∷ Sb2-3-40-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-3-40-1 ∷ CCZ014 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨3·4·01·2⟩-at0410213243 c4 = run b0
  where
  b0 : Chain (CCZ014 ∷ Sb2-3-40-1 ∷ []) (Sb2-3-40-1 ∷ CCZ014 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4) ▸
       at 2 2 (Sb2-4-30-1 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨2·3·40·1⟩ c4) ▸
       at 1 2 (Sb2-4-30-1 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨3·4·01·2⟩-at03102132 c4) ▸
       at 0 2 (Sb2-3-40-1 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨2·4·30·1⟩ c4) ▸
       at 1 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | SBOX(3;4;01;2) @04103143: 7 steps
lem-auto-CCZ012-∣-SBOX⟨3·4·01·2⟩-at04103143 : Complete 4 → ⟪ (CCZ024 ∷ Sb1-3-40-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-3-40-2 ∷ CCZ024 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨3·4·01·2⟩-at04103143 c4 = run b0
  where
  b0 : Chain (CCZ024 ∷ Sb1-3-40-2 ∷ []) (Sb1-3-40-2 ∷ CCZ024 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 2 2 (Sb2-3-40-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·3·40·2⟩ c4) ▸
       at 1 2 (Sb2-3-40-1 ∷ CCZ014 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨3·4·01·2⟩-at0410213243 c4) ▸
       at 0 2 (Sb1-3-40-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·3·40·1⟩ c4) ▸
       at 1 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | SBOX(3;4;01;2) @0410233142: 7 steps
lem-auto-CCZ012-∣-SBOX⟨3·4·01·2⟩-at0410233142 : Complete 4 → ⟪ (CCZ034 ∷ Sb1-2-40-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-40-3 ∷ CCZ034 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨3·4·01·2⟩-at0410233142 c4 = run b0
  where
  b0 : Chain (CCZ034 ∷ Sb1-2-40-3 ∷ []) (Sb1-2-40-3 ∷ CCZ034 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 2 2 (Sb1-3-40-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·2·40·3⟩ c4) ▸
       at 1 2 (Sb1-3-40-2 ∷ CCZ024 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨3·4·01·2⟩-at04103143 c4) ▸
       at 0 2 (Sb1-2-40-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·3·40·2⟩ c4) ▸
       at 1 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | SBOX(3;4;01;2) @0410233241: 7 steps
lem-auto-CCZ012-∣-SBOX⟨3·4·01·2⟩-at0410233241 : Complete 4 → ⟪ (CCZ034 ∷ Sb2-1-40-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-1-40-3 ∷ CCZ034 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨3·4·01·2⟩-at0410233241 c4 = run b0
  where
  b0 : Chain (CCZ034 ∷ Sb2-1-40-3 ∷ []) (Sb2-1-40-3 ∷ CCZ034 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 2 2 (Sb1-2-40-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·1·40·3⟩ c4) ▸
       at 1 2 (Sb1-2-40-3 ∷ CCZ034 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨3·4·01·2⟩-at0410233142 c4) ▸
       at 0 2 (Sb2-1-40-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·2·40·3⟩ c4) ▸
       at 1 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | SBOX(3;4;01;2) @04233240: 7 steps
lem-auto-CCZ012-∣-SBOX⟨3·4·01·2⟩-at04233240 : Complete 4 → ⟪ (CCZ134 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ CCZ134 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-SBOX⟨3·4·01·2⟩-at04233240 c4 = run b0
  where
  b0 : Chain (CCZ134 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ CCZ134 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 2 2 (Sb2-1-40-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·0·41·3⟩ c4) ▸
       at 1 2 (Sb2-1-40-3 ∷ CCZ034 ∷ []) (lem-auto-CCZ012-∣-SBOX⟨3·4·01·2⟩-at0410233241 c4) ▸
       at 0 2 (Sb2-0-41-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·1·40·3⟩ c4) ▸
       at 1 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | TOFF423 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF423-at2332 : Complete 4 → ⟪ (Sb0-1-32-4 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF423-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ Toff423 ∷ []) (Toff423 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 (Toff423 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ Toff423 ∷ []) (Toff423 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff423 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF423 c4) ▸
       at 0 2 (Toff423 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ Toff423 ∷ []) (Toff423 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | TOFF423 @243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF423-at243243 : Complete 4 → ⟪ (Sb0-1-42-3 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF423-at243243 c4 = run b0
  where
  b0 : Chain (Sb0-1-42-3 ∷ Toff324 ∷ []) (Toff324 ∷ Sb0-1-42-3 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·42·3⟩ c4) ▸
       at 2 2 (Toff423 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ Toff324 ∷ []) (Toff423 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff423 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF423-at2332 c4) ▸
       at 0 2 (Toff324 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ Toff423 ∷ []) (Toff324 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | TOFF423 @0110243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF423-at0110243243 : Complete 4 → ⟪ (Sb1-0-42-3 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF423-at0110243243 c4 = run b0
  where
  b0 : Chain (Sb1-0-42-3 ∷ Toff324 ∷ []) (Toff324 ∷ Sb1-0-42-3 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·42·3⟩ c4) ▸
       at 2 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 1 2 (Toff324 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF423-at243243 c4) ▸
       at 0 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | TOFF423 @0210243143: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF423-at0210243143 : Complete 4 → ⟪ (Sb2-0-41-3 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF423-at0210243143 c4 = run b0
  where
  b0 : Chain (Sb2-0-41-3 ∷ Toff314 ∷ []) (Toff314 ∷ Sb2-0-41-3 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·41·3⟩ c4) ▸
       at 2 2 (Toff324 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff314 ∷ []) (Toff324 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff324 ∷ Sb1-0-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-TOFF423-at0110243243 c4) ▸
       at 0 2 (Toff314 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff324 ∷ []) (Toff314 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CSd01 | BOX(2;0134) @1221: 7 steps
lem-auto-CSd01-∣-BOX⟨2·0134⟩-at1221 : Complete 4 → ⟪ (CS02⁻ ∷ Bx1-0234 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0234 ∷ CS02⁻ ∷ []) ⟫ʷ
lem-auto-CSd01-∣-BOX⟨2·0134⟩-at1221 c4 = run b0
  where
  b0 : Chain (CS02⁻ ∷ Bx1-0234 ∷ []) (Bx1-0234 ∷ CS02⁻ ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS01⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd02 c4) ▸
       at 2 2 (Bx2-0134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0234⟩ c4) ▸
       at 1 2 (Bx2-0134 ∷ CS01⁻ ∷ []) (lem-auto-CSd01-∣-BOX⟨2·0134⟩ c4) ▸
       at 0 2 (Bx1-0234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0134⟩ c4) ▸
       at 1 2 (CS02⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd01 c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CSd01 | BOX(2;0134) @132132: 7 steps
lem-auto-CSd01-∣-BOX⟨2·0134⟩-at132132 : Complete 4 → ⟪ (CS03⁻ ∷ Bx1-0324 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0324 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-auto-CSd01-∣-BOX⟨2·0134⟩-at132132 c4 = run b0
  where
  b0 : Chain (CS03⁻ ∷ Bx1-0324 ∷ []) (Bx1-0324 ∷ CS03⁻ ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS02⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd03 c4) ▸
       at 2 2 (Bx1-0234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·0324⟩ c4) ▸
       at 1 2 (Bx1-0234 ∷ CS02⁻ ∷ []) (lem-auto-CSd01-∣-BOX⟨2·0134⟩-at1221 c4) ▸
       at 0 2 (Bx1-0324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·0234⟩ c4) ▸
       at 1 2 (CS03⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd02 c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CSd01 | BOX(2;0134) @14213243: 7 steps
lem-auto-CSd01-∣-BOX⟨2·0134⟩-at14213243 : Complete 4 → ⟪ (CS04⁻ ∷ Bx1-0423 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0423 ∷ CS04⁻ ∷ []) ⟫ʷ
lem-auto-CSd01-∣-BOX⟨2·0134⟩-at14213243 c4 = run b0
  where
  b0 : Chain (CS04⁻ ∷ Bx1-0423 ∷ []) (Bx1-0423 ∷ CS04⁻ ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS03⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd04 c4) ▸
       at 2 2 (Bx1-0324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·0423⟩ c4) ▸
       at 1 2 (Bx1-0324 ∷ CS03⁻ ∷ []) (lem-auto-CSd01-∣-BOX⟨2·0134⟩-at132132 c4) ▸
       at 0 2 (Bx1-0423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·0324⟩ c4) ▸
       at 1 2 (CS04⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd03 c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CSd01 | BOX(2;0134) @143143: 7 steps
lem-auto-CSd01-∣-BOX⟨2·0134⟩-at143143 : Complete 4 → ⟪ (CS04⁻ ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ CS04⁻ ∷ []) ⟫ʷ
lem-auto-CSd01-∣-BOX⟨2·0134⟩-at143143 c4 = run b0
  where
  b0 : Chain (CS04⁻ ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ CS04⁻ ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS04⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd04 c4) ▸
       at 2 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ c4) ▸
       at 1 2 (Bx1-0423 ∷ CS04⁻ ∷ []) (lem-auto-CSd01-∣-BOX⟨2·0134⟩-at14213243 c4) ▸
       at 0 2 (Bx2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0423⟩ c4) ▸
       at 1 2 (CS04⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd04 c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto S0 | BOX(1;0234) @2332: 7 steps
lem-auto-S0-∣-BOX⟨1·0234⟩-at2332 : Complete 4 → ⟪ (S0 ∷ Bx1-0324 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0324 ∷ S0 ∷ []) ⟫ʷ
lem-auto-S0-∣-BOX⟨1·0234⟩-at2332 c4 = run b0
  where
  b0 : Chain (S0 ∷ Bx1-0324 ∷ []) (Bx1-0324 ∷ S0 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (S0 ∷ Sw23 ∷ []) (sym (c₁ (S) (Swap ↑))) ▸
       at 2 2 (Bx1-0234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·0324⟩ c4) ▸
       at 1 2 (Bx1-0234 ∷ S0 ∷ []) (lem-auto-S0-∣-BOX⟨1·0234⟩ c4) ▸
       at 0 2 (Bx1-0324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·0234⟩ c4) ▸
       at 1 2 (S0 ∷ Sw23 ∷ []) (sym (c₁ (S) (Swap ↑))) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto S0 | BOX(1;0234) @243243: 7 steps
lem-auto-S0-∣-BOX⟨1·0234⟩-at243243 : Complete 4 → ⟪ (S0 ∷ Bx1-0423 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0423 ∷ S0 ∷ []) ⟫ʷ
lem-auto-S0-∣-BOX⟨1·0234⟩-at243243 c4 = run b0
  where
  b0 : Chain (S0 ∷ Bx1-0423 ∷ []) (Bx1-0423 ∷ S0 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (S0 ∷ Sw34 ∷ []) (sym (c₁ (S) (Swap ↑ ↑))) ▸
       at 2 2 (Bx1-0324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·0423⟩ c4) ▸
       at 1 2 (Bx1-0324 ∷ S0 ∷ []) (lem-auto-S0-∣-BOX⟨1·0234⟩-at2332 c4) ▸
       at 0 2 (Bx1-0423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·0324⟩ c4) ▸
       at 1 2 (S0 ∷ Sw34 ∷ []) (sym (c₁ (S) (Swap ↑ ↑))) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto S0 | BOX(1;0234) @12243143: 7 steps
lem-auto-S0-∣-BOX⟨1·0234⟩-at12243143 : Complete 4 → ⟪ (S0 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ S0 ∷ []) ⟫ʷ
lem-auto-S0-∣-BOX⟨1·0234⟩-at12243143 c4 = run b0
  where
  b0 : Chain (S0 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ S0 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (S0 ∷ Sw12 ∷ []) (sym (c₁ (S) (Swap))) ▸
       at 2 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ c4) ▸
       at 1 2 (Bx1-0423 ∷ S0 ∷ []) (lem-auto-S0-∣-BOX⟨1·0234⟩-at243243 c4) ▸
       at 0 2 (Bx2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0423⟩ c4) ▸
       at 1 2 (S0 ∷ Sw12 ∷ []) (sym (c₁ (S) (Swap))) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | CCZ314 @0112243043: 7 steps
lem-auto-CCZ012-∣-CCZ314-at0112243043 : Complete 4 → ⟪ (CCZ124 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ CCZ124 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-CCZ314-at0112243043 c4 = run b0
  where
  b0 : Chain (CCZ124 ∷ CCZ023 ∷ []) (CCZ023 ∷ CCZ124 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 2 2 (CCZ123 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ023 ∷ []) (CCZ123 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ123 ∷ CCZ024 ∷ []) (lem-auto-CCZ012-∣-CCZ314-at12243143 c4) ▸
       at 0 2 (CCZ023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ123 ∷ []) (CCZ023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CCZ023 @243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ023-at243243 : Complete 4 → ⟪ (Sb0-1-42-3 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ023-at243243 c4 = run b0
  where
  b0 : Chain (Sb0-1-42-3 ∷ CCZ024 ∷ []) (CCZ024 ∷ Sb0-1-42-3 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·42·3⟩ c4) ▸
       at 2 2 (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 c4) ▸
       at 1 2 (CCZ023 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ023-at2332 c4) ▸
       at 0 2 (CCZ024 ∷ Sw34 ∷ []) (lem-nat-3-CCZ023 c4) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CCZ023 @0110243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ023-at0110243243 : Complete 4 → ⟪ (Sb1-0-42-3 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ023-at0110243243 c4 = run b0
  where
  b0 : Chain (Sb1-0-42-3 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sb1-0-42-3 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·42·3⟩ c4) ▸
       at 2 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 1 2 (CCZ024 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ023-at243243 c4) ▸
       at 0 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CCZ023 @0210243143: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ023-at0210243143 : Complete 4 → ⟪ (Sb2-0-41-3 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ023-at0210243143 c4 = run b0
  where
  b0 : Chain (Sb2-0-41-3 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sb2-0-41-3 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·41·3⟩ c4) ▸
       at 2 2 (CCZ124 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ124 ∷ Sb1-0-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ023-at0110243243 c4) ▸
       at 0 2 (CCZ124 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done

