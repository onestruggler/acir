{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D146 where

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
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-Cz-beta)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-T312-beta-at14213243 ; lem-beta-inv-at243243 ; lem-sym12-at14213243 ; lem-sym23-at14213243)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-sym23-at243243 ; lem-sym34-at3443)
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-sym12-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at243243 ; lem-auto-BOX⟨0·1234⟩-∣-CS14-at243243 ; lem-auto-BOX⟨0·1234⟩-∣-CSd14-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D006 using (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D137 using (lem-auto-CCZ012-∣-CS34-at3443)
open import Examples.Groups.Clifford+CS.Five.D.D138 using (lem-auto-BOX⟨0·1234⟩-∣-CCZ241-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D139 using (lem-auto-BOX⟨0·1234⟩-∣-CCZ123-at243243 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D140 using (lem-auto-BOX⟨0·1234⟩-∣-CCZ214-at243243 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ234-at243243 ; lem-auto-BOX⟨0·1234⟩-∣-CS43-at243243 ; lem-auto-BOX⟨0·1234⟩-∣-CSd43-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D142 using (lem-T312-beta-at2442)
open import Examples.Groups.Clifford+CS.Five.D.D145 using (lem-T312-beta-at14233142 ; lem-T312-beta-at14233241 ; lem-T312-beta-at1441 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at122441 ; lem-auto-BOX⟨0·1234⟩-∣-CS14-at122441 ; lem-auto-BOX⟨0·1234⟩-∣-CSd14-at2442 ; lem-boxify-9-nf-of-rhs ; lem-sym12-at122441 ; lem-sym12-at1441 ; lem-sym23-at14233241 ; lem-sym23-at143143 ; lem-sym23-at1441 ; lem-sym34-at14233142 ; lem-sym34-at14233241 ; lem-sym34-at143143 ; lem-sym34-at1441)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-2-CCZ124 ; lem-nat-2-CCZ134)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-nat-2-BOX⟨0·1432⟩)
open import Examples.Groups.Clifford+CS.Five.D.R019 using (lem-nat-2-BOX⟨0·1423⟩)
open import Examples.Groups.Clifford+CS.Five.D.R021 using (lem-nat-1-BOX⟨0·1432⟩ ; lem-nat-1-BOX⟨0·2431⟩)
-- auto BOX(0;1234) | CSd14 @122441: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd14-at122441 : Complete 4 → ⟪ (Bx0-2431 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ Bx0-2431 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd14-at122441 c4 = run b0
  where
  b0 : Chain (Bx0-2431 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ Bx0-2431 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1432 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2431⟩ c4) ▸
       at 2 2 (CS12⁻ ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS12⁻ ∷ Bx0-1432 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd14-at2442 c4) ▸
       at 0 2 (CS12⁻ ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-2431 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1432⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ243 @2442: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at2442 : Complete 4 → ⟪ (Bx0-1432 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Bx0-1432 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at2442 c4 = run b0
  where
  b0 : Chain (Bx0-1432 ∷ CCZ234 ∷ []) (CCZ234 ∷ Bx0-1432 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1423 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1432⟩ c4) ▸
       at 2 2 (CCZ234 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ234 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at243243 c4) ▸
       at 0 2 (CCZ234 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1432 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1423⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ243 @122441: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at122441 : Complete 4 → ⟪ (Bx0-2431 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Bx0-2431 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at122441 c4 = run b0
  where
  b0 : Chain (Bx0-2431 ∷ CCZ134 ∷ []) (CCZ134 ∷ Bx0-2431 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1432 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2431⟩ c4) ▸
       at 2 2 (CCZ234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ134 ∷ []) (CCZ234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ234 ∷ Bx0-1432 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at2442 c4) ▸
       at 0 2 (CCZ134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ234 ∷ []) (CCZ134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-2431 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1432⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- T312-beta @122441: 8 steps
lem-T312-beta-at122441 : Complete 4 → ⟪ (Toff324 ∷ Bx0-2431 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ CCZ124 ∷ []) ⟫ʷ
lem-T312-beta-at122441 c4 = run b0
  where
  b0 : Chain (Toff324 ∷ Bx0-2431 ∷ Toff324 ∷ []) (Bx0-2431 ∷ CCZ124 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff314 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff324 ∷ []) (Toff314 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-1432 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2431⟩ c4) ▸
       at 3 2 (Toff314 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff324 ∷ []) (Toff314 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Bx0-1432 ∷ CCZ124 ∷ []) (lem-T312-beta-at2442 c4) ▸
       at 0 2 (Bx0-2431 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1432⟩ c4) ▸
       at 1 2 (CCZ124 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ124 @2442: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at2442 : Complete 4 → ⟪ (Bx0-1432 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Bx0-1432 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at2442 c4 = run b0
  where
  b0 : Chain (Bx0-1432 ∷ CCZ124 ∷ []) (CCZ124 ∷ Bx0-1432 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1423 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1432⟩ c4) ▸
       at 2 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 1 2 (CCZ134 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at243243 c4) ▸
       at 0 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 1 2 (Bx0-1432 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1423⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ124 @122441: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at122441 : Complete 4 → ⟪ (Bx0-2431 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Bx0-2431 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at122441 c4 = run b0
  where
  b0 : Chain (Bx0-2431 ∷ CCZ124 ∷ []) (CCZ124 ∷ Bx0-2431 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1432 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2431⟩ c4) ▸
       at 2 2 (CCZ124 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ124 ∷ Bx0-1432 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at2442 c4) ▸
       at 0 2 (CCZ124 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-2431 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1432⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ234 @2442: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ234-at2442 : Complete 4 → ⟪ (Bx0-1432 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Bx0-1432 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ234-at2442 c4 = run b0
  where
  b0 : Chain (Bx0-1432 ∷ CCZ234 ∷ []) (CCZ234 ∷ Bx0-1432 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1423 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1432⟩ c4) ▸
       at 2 2 (CCZ234 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ234 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ234-at243243 c4) ▸
       at 0 2 (CCZ234 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1432 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1423⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ234 @122441: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ234-at122441 : Complete 4 → ⟪ (Bx0-2431 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Bx0-2431 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ234-at122441 c4 = run b0
  where
  b0 : Chain (Bx0-2431 ∷ CCZ134 ∷ []) (CCZ134 ∷ Bx0-2431 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1432 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2431⟩ c4) ▸
       at 2 2 (CCZ234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ134 ∷ []) (CCZ234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ234 ∷ Bx0-1432 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ234-at2442 c4) ▸
       at 0 2 (CCZ134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ234 ∷ []) (CCZ134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-2431 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1432⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ214 @2442: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ214-at2442 : Complete 4 → ⟪ (Bx0-1432 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Bx0-1432 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ214-at2442 c4 = run b0
  where
  b0 : Chain (Bx0-1432 ∷ CCZ124 ∷ []) (CCZ124 ∷ Bx0-1432 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1423 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1432⟩ c4) ▸
       at 2 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 1 2 (CCZ134 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ214-at243243 c4) ▸
       at 0 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 1 2 (Bx0-1432 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1423⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ214 @122441: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ214-at122441 : Complete 4 → ⟪ (Bx0-2431 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Bx0-2431 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ214-at122441 c4 = run b0
  where
  b0 : Chain (Bx0-2431 ∷ CCZ124 ∷ []) (CCZ124 ∷ Bx0-2431 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1432 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2431⟩ c4) ▸
       at 2 2 (CCZ124 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ124 ∷ Bx0-1432 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ214-at2442 c4) ▸
       at 0 2 (CCZ124 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-2431 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1432⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CS43 @2442: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS43-at2442 : Complete 4 → ⟪ (Bx0-1432 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ Bx0-1432 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS43-at2442 c4 = run b0
  where
  b0 : Chain (Bx0-1432 ∷ CS23 ∷ []) (CS23 ∷ Bx0-1432 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1423 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1432⟩ c4) ▸
       at 2 2 (CS23 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CS23 ∷ []) (CS23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS23 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS43-at243243 c4) ▸
       at 0 2 (CS23 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CS23 ∷ []) (CS23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1432 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1423⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CS43 @122441: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS43-at122441 : Complete 4 → ⟪ (Bx0-2431 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Bx0-2431 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS43-at122441 c4 = run b0
  where
  b0 : Chain (Bx0-2431 ∷ CS13 ∷ []) (CS13 ∷ Bx0-2431 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1432 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2431⟩ c4) ▸
       at 2 2 (CS23 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS13 ∷ []) (CS23 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS23 ∷ Bx0-1432 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS43-at2442 c4) ▸
       at 0 2 (CS13 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS23 ∷ []) (CS13 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-2431 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1432⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CSd43 @2442: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd43-at2442 : Complete 4 → ⟪ (Bx0-1432 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ Bx0-1432 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd43-at2442 c4 = run b0
  where
  b0 : Chain (Bx0-1432 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Bx0-1432 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1423 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1432⟩ c4) ▸
       at 2 2 (CS23⁻ ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS23⁻ ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd43-at243243 c4) ▸
       at 0 2 (CS23⁻ ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1432 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1423⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CSd43 @122441: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd43-at122441 : Complete 4 → ⟪ (Bx0-2431 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ Bx0-2431 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd43-at122441 c4 = run b0
  where
  b0 : Chain (Bx0-2431 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ Bx0-2431 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1432 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2431⟩ c4) ▸
       at 2 2 (CS23⁻ ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS13⁻ ∷ []) (CS23⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS23⁻ ∷ Bx0-1432 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd43-at2442 c4) ▸
       at 0 2 (CS13⁻ ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS23⁻ ∷ []) (CS13⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-2431 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1432⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ123 @2442: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ123-at2442 : Complete 4 → ⟪ (Bx0-1432 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Bx0-1432 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ123-at2442 c4 = run b0
  where
  b0 : Chain (Bx0-1432 ∷ CCZ134 ∷ []) (CCZ134 ∷ Bx0-1432 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1423 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1432⟩ c4) ▸
       at 2 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 1 2 (CCZ124 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ123-at243243 c4) ▸
       at 0 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 1 2 (Bx0-1432 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1423⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ123 @122441: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ123-at122441 : Complete 4 → ⟪ (Bx0-2431 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Bx0-2431 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ123-at122441 c4 = run b0
  where
  b0 : Chain (Bx0-2431 ∷ CCZ234 ∷ []) (CCZ234 ∷ Bx0-2431 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1432 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2431⟩ c4) ▸
       at 2 2 (CCZ134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ234 ∷ []) (CCZ134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ134 ∷ Bx0-1432 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ123-at2442 c4) ▸
       at 0 2 (CCZ234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ134 ∷ []) (CCZ234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-2431 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1432⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- beta-inv @2442: 5 steps
lem-beta-inv-at2442 : Complete 4 → ⟪ (Bx0-1432 ∷ Bx0-1432 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-beta-inv-at2442 c4 = run b0
  where
  b0 : Chain (Bx0-1432 ∷ Bx0-1432 ∷ []) []
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1423 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1432⟩ c4) ▸
       at 2 2 (Bx0-1423 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1432⟩ c4) ▸
       at 1 2 [] (lem-beta-inv-at243243 c4) ▸
       at 0 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- beta-inv @122441: 5 steps
lem-beta-inv-at122441 : Complete 4 → ⟪ (Bx0-2431 ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-beta-inv-at122441 c4 = run b0
  where
  b0 : Chain (Bx0-2431 ∷ Bx0-2431 ∷ []) []
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1432 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2431⟩ c4) ▸
       at 2 2 (Bx0-1432 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2431⟩ c4) ▸
       at 1 2 [] (lem-beta-inv-at2442 c4) ▸
       at 0 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- boxify-9: 331 steps
lem-boxify-9 : Complete 4 → ⟪ (Sb0-2-43-1 ∷ Toff214 ∷ CCZ234 ∷ Sb0-2-43-1 ∷ Toff214 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Sb0-1-42-3 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-boxify-9 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (trans (run b35) (trans (run b36) (trans (run b37) (trans (run b38) (trans (run b39) (trans (run b40) (run b41)))))))))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (Sb0-2-43-1 ∷ Toff214 ∷ CCZ234 ∷ Sb0-2-43-1 ∷ Toff214 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Sb0-1-42-3 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ234 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ [])
  b0 = at 0 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 2 1 (CS12 ∷ []) (refl) ▸
       at 4 1 (CS12⁻ ∷ []) (refl) ▸
       at 7 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 9 1 (CS12 ∷ []) (refl) ▸
       at 11 1 (CS12⁻ ∷ []) (refl) ▸
       at 16 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 18 1 (CS13 ∷ []) (refl) ▸ done

  b1 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ234 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ234 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ Bx0-4123 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ [])
  b1 = at 20 1 (CS13⁻ ∷ []) (refl) ▸
       at 16 0 (Toff324 ∷ Toff324 ∷ []) (lw0 c4 [] (Toff324 ∷ Toff324 ∷ []) tt tt Eq.refl) ▸
       at 18 1 (Bx0-4123 ∷ []) (lem-sym12-at243243 c4) ▸
       at 18 1 (Bx0-4213 ∷ []) (lem-sym23-at14213243 c4) ▸
       at 18 1 (Bx0-4231 ∷ []) (lem-sym34-at143143 c4) ▸
       at 17 3 (Bx0-4231 ∷ CCZ124 ∷ []) (lem-T312-beta-at1441 c4) ▸
       at 17 1 (Bx0-4213 ∷ []) (lem-sym34-at1441 c4) ▸
       at 17 1 (Bx0-4123 ∷ []) (lem-sym23-at143143 c4) ▸ done

  b2 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ234 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ Bx0-4123 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ234 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ Bx0-4231 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ [])
  b2 = at 17 1 (Bx0-1423 ∷ []) (lem-sym12-at14213243 c4) ▸
       at 17 2 (CCZ124 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at243243 c4) ▸
       at 18 2 (CS13 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS14-at243243 c4) ▸
       at 19 0 (Toff324 ∷ Toff324 ∷ []) (lw0 c4 [] (Toff324 ∷ Toff324 ∷ []) tt tt Eq.refl) ▸
       at 21 1 (Bx0-4123 ∷ []) (lem-sym12-at243243 c4) ▸
       at 21 1 (Bx0-4213 ∷ []) (lem-sym23-at14213243 c4) ▸
       at 21 1 (Bx0-4231 ∷ []) (lem-sym34-at143143 c4) ▸
       at 20 3 (Bx0-4231 ∷ CCZ124 ∷ []) (lem-T312-beta-at1441 c4) ▸ done

  b3 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ234 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ Bx0-4231 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ234 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ Toff324 ∷ Bx0-4213 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ [])
  b3 = at 20 1 (Bx0-4213 ∷ []) (lem-sym34-at1441 c4) ▸
       at 20 1 (Bx0-4123 ∷ []) (lem-sym23-at143143 c4) ▸
       at 20 1 (Bx0-1423 ∷ []) (lem-sym12-at14213243 c4) ▸
       at 20 2 (CCZ124 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at243243 c4) ▸
       at 21 2 (CS13⁻ ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd14-at243243 c4) ▸
       at 22 0 (Toff324 ∷ Toff324 ∷ []) (lw0 c4 [] (Toff324 ∷ Toff324 ∷ []) tt tt Eq.refl) ▸
       at 24 1 (Bx0-4123 ∷ []) (lem-sym12-at243243 c4) ▸
       at 24 1 (Bx0-4213 ∷ []) (lem-sym23-at14213243 c4) ▸ done

  b4 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ234 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ Toff324 ∷ Bx0-4213 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ234 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ Toff234 ∷ Bx0-4123 ∷ Toff234 ∷ Toff324 ∷ [])
  b4 = at 24 1 (Bx0-4231 ∷ []) (lem-sym34-at143143 c4) ▸
       at 23 3 (Bx0-4231 ∷ CCZ124 ∷ []) (lem-T312-beta-at1441 c4) ▸
       at 23 1 (Bx0-4213 ∷ []) (lem-sym34-at1441 c4) ▸
       at 23 1 (Bx0-4123 ∷ []) (lem-sym23-at143143 c4) ▸
       at 23 1 (Bx0-1423 ∷ []) (lem-sym12-at14213243 c4) ▸
       at 23 2 (CCZ124 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at243243 c4) ▸
       at 24 0 (Toff234 ∷ Toff234 ∷ []) (lw0 c4 [] (Toff234 ∷ Toff234 ∷ []) tt tt Eq.refl) ▸
       at 26 1 (Bx0-4123 ∷ []) (lem-sym12-at243243 c4) ▸ done

  b5 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ234 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ Toff234 ∷ Bx0-4123 ∷ Toff234 ∷ Toff324 ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ234 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ Bx0-1423 ∷ CCZ134 ∷ Toff324 ∷ [])
  b5 = at 26 1 (Bx0-4213 ∷ []) (lem-sym23-at14213243 c4) ▸
       at 26 1 (Bx0-4231 ∷ []) (lem-sym34-at143143 c4) ▸
       at 26 1 (Bx0-4321 ∷ []) (lem-sym23-at1441 c4) ▸
       at 25 3 (Bx0-4321 ∷ CCZ134 ∷ []) (lem-T312-beta-at14233241 c4) ▸
       at 25 1 (Bx0-4231 ∷ []) (lem-sym23-at14233241 c4) ▸
       at 25 1 (Bx0-4213 ∷ []) (lem-sym34-at1441 c4) ▸
       at 25 1 (Bx0-4123 ∷ []) (lem-sym23-at143143 c4) ▸
       at 25 1 (Bx0-1423 ∷ []) (lem-sym12-at14213243 c4) ▸ done

  b6 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ234 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ Bx0-1423 ∷ CCZ134 ∷ Toff324 ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ234 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ Bx0-4123 ∷ CCZ124 ∷ [])
  b6 = at 25 2 (CCZ134 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ241-at243243 c4) ▸
       at 26 0 (Toff324 ∷ Toff324 ∷ []) (lw0 c4 [] (Toff324 ∷ Toff324 ∷ []) tt tt Eq.refl) ▸
       at 28 1 (Bx0-4123 ∷ []) (lem-sym12-at243243 c4) ▸
       at 28 1 (Bx0-4213 ∷ []) (lem-sym23-at14213243 c4) ▸
       at 28 1 (Bx0-4231 ∷ []) (lem-sym34-at143143 c4) ▸
       at 27 3 (Bx0-4231 ∷ CCZ124 ∷ []) (lem-T312-beta-at1441 c4) ▸
       at 27 1 (Bx0-4213 ∷ []) (lem-sym34-at1441 c4) ▸
       at 27 1 (Bx0-4123 ∷ []) (lem-sym23-at143143 c4) ▸ done

  b7 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ234 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ Bx0-4123 ∷ CCZ124 ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ234 ∷ Toff134 ∷ Bx0-4321 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Bx0-1423 ∷ [])
  b7 = at 27 1 (Bx0-1423 ∷ []) (lem-sym12-at14213243 c4) ▸
       at 27 2 (CCZ124 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at243243 c4) ▸
       at 7 0 (Toff134 ∷ Toff134 ∷ []) (lw0 c4 [] (Toff134 ∷ Toff134 ∷ []) tt tt Eq.refl) ▸
       at 9 1 (Bx0-4231 ∷ []) (lem-sym12-at122441 c4) ▸
       at 9 1 (Bx0-4321 ∷ []) (lem-sym23-at1441 c4) ▸
       at 9 1 (Bx0-4312 ∷ []) (lem-sym34-at14233241 c4) ▸
       at 8 3 (Bx0-4312 ∷ CCZ234 ∷ []) (lem-T312-beta-at14233142 c4) ▸
       at 8 1 (Bx0-4321 ∷ []) (lem-sym34-at14233142 c4) ▸ done

  b8 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ234 ∷ Toff134 ∷ Bx0-4321 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Bx0-1423 ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ Toff134 ∷ Bx0-4312 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Bx0-1423 ∷ [])
  b8 = at 8 1 (Bx0-4231 ∷ []) (lem-sym23-at14233241 c4) ▸
       at 8 1 (Bx0-2431 ∷ []) (lem-sym12-at1441 c4) ▸
       at 8 2 (CCZ234 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at122441 c4) ▸
       at 9 2 (CS12 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS14-at122441 c4) ▸
       at 10 0 (Toff134 ∷ Toff134 ∷ []) (lw0 c4 [] (Toff134 ∷ Toff134 ∷ []) tt tt Eq.refl) ▸
       at 12 1 (Bx0-4231 ∷ []) (lem-sym12-at122441 c4) ▸
       at 12 1 (Bx0-4321 ∷ []) (lem-sym23-at1441 c4) ▸
       at 12 1 (Bx0-4312 ∷ []) (lem-sym34-at14233241 c4) ▸ done

  b9 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ Toff134 ∷ Bx0-4312 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Bx0-1423 ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ Toff214 ∷ Bx0-4231 ∷ Toff214 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Bx0-1423 ∷ [])
  b9 = at 11 3 (Bx0-4312 ∷ CCZ234 ∷ []) (lem-T312-beta-at14233142 c4) ▸
       at 11 1 (Bx0-4321 ∷ []) (lem-sym34-at14233142 c4) ▸
       at 11 1 (Bx0-4231 ∷ []) (lem-sym23-at14233241 c4) ▸
       at 11 1 (Bx0-2431 ∷ []) (lem-sym12-at1441 c4) ▸
       at 11 2 (CCZ234 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at122441 c4) ▸
       at 12 2 (CS12⁻ ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd14-at122441 c4) ▸
       at 13 0 (Toff214 ∷ Toff214 ∷ []) (lw0 c4 [] (Toff214 ∷ Toff214 ∷ []) tt tt Eq.refl) ▸
       at 15 1 (Bx0-4231 ∷ []) (lem-sym12-at122441 c4) ▸ done

  b10 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ Toff214 ∷ Bx0-4231 ∷ Toff214 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Bx0-1423 ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ Toff324 ∷ Toff324 ∷ Bx0-2431 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Bx0-1423 ∷ [])
  b10 = at 15 1 (Bx0-4213 ∷ []) (lem-sym34-at1441 c4) ▸
       at 15 1 (Bx0-4123 ∷ []) (lem-sym23-at143143 c4) ▸
       at 14 3 (Bx0-4123 ∷ CCZ134 ∷ []) (lem-T312-beta-at14213243 c4) ▸
       at 14 1 (Bx0-4213 ∷ []) (lem-sym23-at14213243 c4) ▸
       at 14 1 (Bx0-4231 ∷ []) (lem-sym34-at143143 c4) ▸
       at 14 1 (Bx0-2431 ∷ []) (lem-sym12-at1441 c4) ▸
       at 14 2 (CCZ134 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at122441 c4) ▸
       at 15 0 (Toff324 ∷ Toff324 ∷ []) (lw0 c4 [] (Toff324 ∷ Toff324 ∷ []) tt tt Eq.refl) ▸ done

  b11 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ Toff324 ∷ Toff324 ∷ Bx0-2431 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Bx0-1423 ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ Bx0-4321 ∷ CCZ134 ∷ Toff324 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Bx0-1423 ∷ [])
  b11 = at 16 1 (Toff324 ∷ []) (lw0 c4 (Toff324 ∷ []) (Toff324 ∷ []) tt tt Eq.refl) ▸
       at 18 1 (Toff324 ∷ []) (lw0 c4 (Toff324 ∷ []) (Toff324 ∷ []) tt tt Eq.refl) ▸
       at 16 3 (Bx0-2431 ∷ CCZ124 ∷ []) (lem-T312-beta-at122441 c4) ▸
       at 16 2 (CCZ124 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at122441 c4) ▸
       at 17 0 (Toff234 ∷ Toff234 ∷ []) (lw0 c4 [] (Toff234 ∷ Toff234 ∷ []) tt tt Eq.refl) ▸
       at 19 1 (Bx0-4231 ∷ []) (lem-sym12-at122441 c4) ▸
       at 19 1 (Bx0-4321 ∷ []) (lem-sym23-at1441 c4) ▸
       at 18 3 (Bx0-4321 ∷ CCZ134 ∷ []) (lem-T312-beta-at14233241 c4) ▸ done

  b12 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ Bx0-4321 ∷ CCZ134 ∷ Toff324 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Bx0-1423 ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Bx0-2431 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Bx0-1423 ∷ [])
  b12 = at 18 1 (Bx0-4231 ∷ []) (lem-sym23-at14233241 c4) ▸
       at 18 1 (Bx0-2431 ∷ []) (lem-sym12-at1441 c4) ▸
       at 18 2 (CCZ134 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ234-at122441 c4) ▸
       at 19 0 (Toff324 ∷ Toff324 ∷ []) (lw0 c4 [] (Toff324 ∷ Toff324 ∷ []) tt tt Eq.refl) ▸
       at 20 1 (Toff324 ∷ []) (lw0 c4 (Toff324 ∷ []) (Toff324 ∷ []) tt tt Eq.refl) ▸
       at 22 1 (Toff324 ∷ []) (lw0 c4 (Toff324 ∷ []) (Toff324 ∷ []) tt tt Eq.refl) ▸
       at 20 3 (Bx0-2431 ∷ CCZ124 ∷ []) (lem-T312-beta-at122441 c4) ▸
       at 20 2 (CCZ124 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at122441 c4) ▸ done

  b13 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Bx0-2431 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Bx0-1423 ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ Toff324 ∷ Bx0-2431 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Bx0-1423 ∷ [])
  b13 = at 21 0 (Toff324 ∷ Toff324 ∷ []) (lw0 c4 [] (Toff324 ∷ Toff324 ∷ []) tt tt Eq.refl) ▸
       at 22 1 (Toff324 ∷ []) (lw0 c4 (Toff324 ∷ []) (Toff324 ∷ []) tt tt Eq.refl) ▸
       at 24 1 (Toff324 ∷ []) (lw0 c4 (Toff324 ∷ []) (Toff324 ∷ []) tt tt Eq.refl) ▸
       at 22 3 (Bx0-2431 ∷ CCZ124 ∷ []) (lem-T312-beta-at122441 c4) ▸
       at 22 2 (CCZ124 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at122441 c4) ▸
       at 23 2 (CCZ124 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ214-at122441 c4) ▸
       at 24 2 (CS13 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS43-at122441 c4) ▸
       at 25 0 (Toff324 ∷ Toff324 ∷ []) (lw0 c4 [] (Toff324 ∷ Toff324 ∷ []) tt tt Eq.refl) ▸ done

  b14 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ Toff324 ∷ Bx0-2431 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Bx0-1423 ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ Toff324 ∷ Bx0-2431 ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Bx0-1423 ∷ [])
  b14 = at 26 1 (Toff324 ∷ []) (lw0 c4 (Toff324 ∷ []) (Toff324 ∷ []) tt tt Eq.refl) ▸
       at 28 1 (Toff324 ∷ []) (lw0 c4 (Toff324 ∷ []) (Toff324 ∷ []) tt tt Eq.refl) ▸
       at 26 3 (Bx0-2431 ∷ CCZ124 ∷ []) (lem-T312-beta-at122441 c4) ▸
       at 26 2 (CCZ124 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at122441 c4) ▸
       at 27 2 (CCZ124 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ214-at122441 c4) ▸
       at 28 2 (CS13⁻ ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd43-at122441 c4) ▸
       at 29 0 (Toff324 ∷ Toff324 ∷ []) (lw0 c4 [] (Toff324 ∷ Toff324 ∷ []) tt tt Eq.refl) ▸
       at 30 1 (Toff324 ∷ []) (lw0 c4 (Toff324 ∷ []) (Toff324 ∷ []) tt tt Eq.refl) ▸ done

  b15 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ Toff324 ∷ Bx0-2431 ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Bx0-1423 ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ Bx0-4321 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Bx0-1423 ∷ [])
  b15 = at 32 1 (Toff324 ∷ []) (lw0 c4 (Toff324 ∷ []) (Toff324 ∷ []) tt tt Eq.refl) ▸
       at 30 3 (Bx0-2431 ∷ CCZ124 ∷ []) (lem-T312-beta-at122441 c4) ▸
       at 30 2 (CCZ124 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at122441 c4) ▸
       at 31 2 (CCZ124 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ214-at122441 c4) ▸
       at 32 0 (Toff234 ∷ Toff234 ∷ []) (lw0 c4 [] (Toff234 ∷ Toff234 ∷ []) tt tt Eq.refl) ▸
       at 34 1 (Bx0-4231 ∷ []) (lem-sym12-at122441 c4) ▸
       at 34 1 (Bx0-4321 ∷ []) (lem-sym23-at1441 c4) ▸
       at 33 3 (Bx0-4321 ∷ CCZ134 ∷ []) (lem-T312-beta-at14233241 c4) ▸ done

  b16 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ Bx0-4321 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Bx0-1423 ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ Bx0-2431 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-1423 ∷ [])
  b16 = at 33 1 (Bx0-4231 ∷ []) (lem-sym23-at14233241 c4) ▸
       at 33 1 (Bx0-2431 ∷ []) (lem-sym12-at1441 c4) ▸
       at 33 2 (CCZ134 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ234-at122441 c4) ▸
       at 34 2 (CCZ134 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ234-at122441 c4) ▸
       at 35 0 (Toff324 ∷ Toff324 ∷ []) (lw0 c4 [] (Toff324 ∷ Toff324 ∷ []) tt tt Eq.refl) ▸
       at 36 1 (Toff324 ∷ []) (lw0 c4 (Toff324 ∷ []) (Toff324 ∷ []) tt tt Eq.refl) ▸
       at 38 1 (Toff324 ∷ []) (lw0 c4 (Toff324 ∷ []) (Toff324 ∷ []) tt tt Eq.refl) ▸
       at 36 3 (Bx0-2431 ∷ CCZ124 ∷ []) (lem-T312-beta-at122441 c4) ▸ done

  b17 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ Bx0-2431 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-1423 ∷ []) (Toff134 ∷ Bx0-4321 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-2431 ∷ Bx0-1423 ∷ [])
  b17 = at 36 2 (CCZ124 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at122441 c4) ▸
       at 37 2 (CCZ124 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ214-at122441 c4) ▸
       at 0 0 (Toff134 ∷ Toff134 ∷ []) (lw0 c4 [] (Toff134 ∷ Toff134 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Bx0-4231 ∷ []) (lem-sym12-at122441 c4) ▸
       at 2 1 (Bx0-4321 ∷ []) (lem-sym23-at1441 c4) ▸
       at 2 1 (Bx0-4312 ∷ []) (lem-sym34-at14233241 c4) ▸
       at 1 3 (Bx0-4312 ∷ CCZ234 ∷ []) (lem-T312-beta-at14233142 c4) ▸
       at 1 1 (Bx0-4321 ∷ []) (lem-sym34-at14233142 c4) ▸ done

  b18 : Chain (Toff134 ∷ Bx0-4321 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-2431 ∷ Bx0-1423 ∷ []) (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ Toff134 ∷ Bx0-4312 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-2431 ∷ Bx0-1423 ∷ [])
  b18 = at 1 1 (Bx0-4231 ∷ []) (lem-sym23-at14233241 c4) ▸
       at 1 1 (Bx0-2431 ∷ []) (lem-sym12-at1441 c4) ▸
       at 1 2 (CCZ234 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at122441 c4) ▸
       at 2 2 (CS12 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS14-at122441 c4) ▸
       at 3 0 (Toff134 ∷ Toff134 ∷ []) (lw0 c4 [] (Toff134 ∷ Toff134 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Bx0-4231 ∷ []) (lem-sym12-at122441 c4) ▸
       at 5 1 (Bx0-4321 ∷ []) (lem-sym23-at1441 c4) ▸
       at 5 1 (Bx0-4312 ∷ []) (lem-sym34-at14233241 c4) ▸ done

  b19 : Chain (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ Toff134 ∷ Bx0-4312 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-2431 ∷ Bx0-1423 ∷ []) (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ Toff214 ∷ Bx0-4231 ∷ Toff214 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-2431 ∷ Bx0-1423 ∷ [])
  b19 = at 4 3 (Bx0-4312 ∷ CCZ234 ∷ []) (lem-T312-beta-at14233142 c4) ▸
       at 4 1 (Bx0-4321 ∷ []) (lem-sym34-at14233142 c4) ▸
       at 4 1 (Bx0-4231 ∷ []) (lem-sym23-at14233241 c4) ▸
       at 4 1 (Bx0-2431 ∷ []) (lem-sym12-at1441 c4) ▸
       at 4 2 (CCZ234 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at122441 c4) ▸
       at 5 2 (CS12⁻ ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd14-at122441 c4) ▸
       at 6 0 (Toff214 ∷ Toff214 ∷ []) (lw0 c4 [] (Toff214 ∷ Toff214 ∷ []) tt tt Eq.refl) ▸
       at 8 1 (Bx0-4231 ∷ []) (lem-sym12-at122441 c4) ▸ done

  b20 : Chain (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ Toff214 ∷ Bx0-4231 ∷ Toff214 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-2431 ∷ Bx0-1423 ∷ []) (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ Bx0-2431 ∷ Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-2431 ∷ Bx0-1423 ∷ [])
  b20 = at 8 1 (Bx0-4213 ∷ []) (lem-sym34-at1441 c4) ▸
       at 8 1 (Bx0-4123 ∷ []) (lem-sym23-at143143 c4) ▸
       at 7 3 (Bx0-4123 ∷ CCZ134 ∷ []) (lem-T312-beta-at14213243 c4) ▸
       at 7 1 (Bx0-4213 ∷ []) (lem-sym23-at14213243 c4) ▸
       at 7 1 (Bx0-4231 ∷ []) (lem-sym34-at143143 c4) ▸
       at 7 1 (Bx0-2431 ∷ []) (lem-sym12-at1441 c4) ▸
       at 7 2 (CCZ134 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at122441 c4) ▸
       at 8 2 (CCZ234 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ123-at122441 c4) ▸ done

  b21 : Chain (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ Bx0-2431 ∷ Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-2431 ∷ Bx0-1423 ∷ []) (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ Toff134 ∷ Bx0-2431 ∷ CCZ234 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-2431 ∷ Bx0-1423 ∷ [])
  b21 = at 9 0 (Toff134 ∷ Toff134 ∷ []) (lw0 c4 [] (Toff134 ∷ Toff134 ∷ []) tt tt Eq.refl) ▸
       at 11 1 (Bx0-4231 ∷ []) (lem-sym12-at122441 c4) ▸
       at 11 1 (Bx0-4321 ∷ []) (lem-sym23-at1441 c4) ▸
       at 11 1 (Bx0-4312 ∷ []) (lem-sym34-at14233241 c4) ▸
       at 10 3 (Bx0-4312 ∷ CCZ234 ∷ []) (lem-T312-beta-at14233142 c4) ▸
       at 10 1 (Bx0-4321 ∷ []) (lem-sym34-at14233142 c4) ▸
       at 10 1 (Bx0-4231 ∷ []) (lem-sym23-at14233241 c4) ▸
       at 10 1 (Bx0-2431 ∷ []) (lem-sym12-at1441 c4) ▸ done

  b22 : Chain (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ Toff134 ∷ Bx0-2431 ∷ CCZ234 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-2431 ∷ Bx0-1423 ∷ []) (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ Bx0-4312 ∷ CCZ234 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-2431 ∷ Bx0-1423 ∷ [])
  b22 = at 10 2 (CCZ234 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at122441 c4) ▸
       at 11 2 (CCZ234 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at122441 c4) ▸
       at 12 2 (CS12 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS14-at122441 c4) ▸
       at 13 0 (Toff134 ∷ Toff134 ∷ []) (lw0 c4 [] (Toff134 ∷ Toff134 ∷ []) tt tt Eq.refl) ▸
       at 15 1 (Bx0-4231 ∷ []) (lem-sym12-at122441 c4) ▸
       at 15 1 (Bx0-4321 ∷ []) (lem-sym23-at1441 c4) ▸
       at 15 1 (Bx0-4312 ∷ []) (lem-sym34-at14233241 c4) ▸
       at 14 3 (Bx0-4312 ∷ CCZ234 ∷ []) (lem-T312-beta-at14233142 c4) ▸ done

  b23 : Chain (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ Bx0-4312 ∷ CCZ234 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-2431 ∷ Bx0-1423 ∷ []) (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ Toff214 ∷ Bx0-4231 ∷ Toff214 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-2431 ∷ Bx0-1423 ∷ [])
  b23 = at 14 1 (Bx0-4321 ∷ []) (lem-sym34-at14233142 c4) ▸
       at 14 1 (Bx0-4231 ∷ []) (lem-sym23-at14233241 c4) ▸
       at 14 1 (Bx0-2431 ∷ []) (lem-sym12-at1441 c4) ▸
       at 14 2 (CCZ234 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at122441 c4) ▸
       at 15 2 (CCZ234 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at122441 c4) ▸
       at 16 2 (CS12⁻ ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd14-at122441 c4) ▸
       at 17 0 (Toff214 ∷ Toff214 ∷ []) (lw0 c4 [] (Toff214 ∷ Toff214 ∷ []) tt tt Eq.refl) ▸
       at 19 1 (Bx0-4231 ∷ []) (lem-sym12-at122441 c4) ▸ done

  b24 : Chain (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ Toff214 ∷ Bx0-4231 ∷ Toff214 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-2431 ∷ Bx0-1423 ∷ []) (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Bx0-2431 ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-2431 ∷ Bx0-1423 ∷ [])
  b24 = at 19 1 (Bx0-4213 ∷ []) (lem-sym34-at1441 c4) ▸
       at 19 1 (Bx0-4123 ∷ []) (lem-sym23-at143143 c4) ▸
       at 18 3 (Bx0-4123 ∷ CCZ134 ∷ []) (lem-T312-beta-at14213243 c4) ▸
       at 18 1 (Bx0-4213 ∷ []) (lem-sym23-at14213243 c4) ▸
       at 18 1 (Bx0-4231 ∷ []) (lem-sym34-at143143 c4) ▸
       at 18 1 (Bx0-2431 ∷ []) (lem-sym12-at1441 c4) ▸
       at 18 2 (CCZ134 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at122441 c4) ▸
       at 19 2 (CCZ134 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at122441 c4) ▸ done

  b25 : Chain (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Bx0-2431 ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-2431 ∷ Bx0-1423 ∷ []) (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ Toff234 ∷ Bx0-4231 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-2431 ∷ Bx0-1423 ∷ [])
  b25 = at 20 0 (Toff324 ∷ Toff324 ∷ []) (lw0 c4 [] (Toff324 ∷ Toff324 ∷ []) tt tt Eq.refl) ▸
       at 21 1 (Toff324 ∷ []) (lw0 c4 (Toff324 ∷ []) (Toff324 ∷ []) tt tt Eq.refl) ▸
       at 23 1 (Toff324 ∷ []) (lw0 c4 (Toff324 ∷ []) (Toff324 ∷ []) tt tt Eq.refl) ▸
       at 21 3 (Bx0-2431 ∷ CCZ124 ∷ []) (lem-T312-beta-at122441 c4) ▸
       at 21 2 (CCZ124 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at122441 c4) ▸
       at 22 2 (CCZ124 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at122441 c4) ▸
       at 23 0 (Toff234 ∷ Toff234 ∷ []) (lw0 c4 [] (Toff234 ∷ Toff234 ∷ []) tt tt Eq.refl) ▸
       at 25 1 (Bx0-4231 ∷ []) (lem-sym12-at122441 c4) ▸ done

  b26 : Chain (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ Toff234 ∷ Bx0-4231 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-2431 ∷ Bx0-1423 ∷ []) (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ Toff324 ∷ Bx0-2431 ∷ Toff324 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-2431 ∷ Bx0-1423 ∷ [])
  b26 = at 25 1 (Bx0-4321 ∷ []) (lem-sym23-at1441 c4) ▸
       at 24 3 (Bx0-4321 ∷ CCZ134 ∷ []) (lem-T312-beta-at14233241 c4) ▸
       at 24 1 (Bx0-4231 ∷ []) (lem-sym23-at14233241 c4) ▸
       at 24 1 (Bx0-2431 ∷ []) (lem-sym12-at1441 c4) ▸
       at 24 2 (CCZ134 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ234-at122441 c4) ▸
       at 25 2 (CCZ134 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ234-at122441 c4) ▸
       at 26 0 (Toff324 ∷ Toff324 ∷ []) (lw0 c4 [] (Toff324 ∷ Toff324 ∷ []) tt tt Eq.refl) ▸
       at 27 1 (Toff324 ∷ []) (lw0 c4 (Toff324 ∷ []) (Toff324 ∷ []) tt tt Eq.refl) ▸ done

  b27 : Chain (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ Toff324 ∷ Bx0-2431 ∷ Toff324 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-2431 ∷ Bx0-1423 ∷ []) (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ Bx0-2431 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-2431 ∷ Bx0-1423 ∷ [])
  b27 = at 29 1 (Toff324 ∷ []) (lw0 c4 (Toff324 ∷ []) (Toff324 ∷ []) tt tt Eq.refl) ▸
       at 27 3 (Bx0-2431 ∷ CCZ124 ∷ []) (lem-T312-beta-at122441 c4) ▸
       at 27 2 (CCZ124 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at122441 c4) ▸
       at 28 2 (CCZ124 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at122441 c4) ▸
       at 29 0 (Toff324 ∷ Toff324 ∷ []) (lw0 c4 [] (Toff324 ∷ Toff324 ∷ []) tt tt Eq.refl) ▸
       at 30 1 (Toff324 ∷ []) (lw0 c4 (Toff324 ∷ []) (Toff324 ∷ []) tt tt Eq.refl) ▸
       at 32 1 (Toff324 ∷ []) (lw0 c4 (Toff324 ∷ []) (Toff324 ∷ []) tt tt Eq.refl) ▸
       at 30 3 (Bx0-2431 ∷ CCZ124 ∷ []) (lem-T312-beta-at122441 c4) ▸ done

  b28 : Chain (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ Bx0-2431 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-2431 ∷ Bx0-1423 ∷ []) (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ Bx0-2431 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-2431 ∷ Bx0-1423 ∷ [])
  b28 = at 30 2 (CCZ124 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at122441 c4) ▸
       at 31 2 (CCZ124 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at122441 c4) ▸
       at 32 2 (CCZ124 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ214-at122441 c4) ▸
       at 33 2 (CS13 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS43-at122441 c4) ▸
       at 34 0 (Toff324 ∷ Toff324 ∷ []) (lw0 c4 [] (Toff324 ∷ Toff324 ∷ []) tt tt Eq.refl) ▸
       at 35 1 (Toff324 ∷ []) (lw0 c4 (Toff324 ∷ []) (Toff324 ∷ []) tt tt Eq.refl) ▸
       at 37 1 (Toff324 ∷ []) (lw0 c4 (Toff324 ∷ []) (Toff324 ∷ []) tt tt Eq.refl) ▸
       at 35 3 (Bx0-2431 ∷ CCZ124 ∷ []) (lem-T312-beta-at122441 c4) ▸ done

  b29 : Chain (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ Bx0-2431 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-2431 ∷ Bx0-1423 ∷ []) (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ Bx0-2431 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-2431 ∷ Bx0-1423 ∷ [])
  b29 = at 35 2 (CCZ124 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at122441 c4) ▸
       at 36 2 (CCZ124 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at122441 c4) ▸
       at 37 2 (CCZ124 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ214-at122441 c4) ▸
       at 38 2 (CS13⁻ ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd43-at122441 c4) ▸
       at 39 0 (Toff324 ∷ Toff324 ∷ []) (lw0 c4 [] (Toff324 ∷ Toff324 ∷ []) tt tt Eq.refl) ▸
       at 40 1 (Toff324 ∷ []) (lw0 c4 (Toff324 ∷ []) (Toff324 ∷ []) tt tt Eq.refl) ▸
       at 42 1 (Toff324 ∷ []) (lw0 c4 (Toff324 ∷ []) (Toff324 ∷ []) tt tt Eq.refl) ▸
       at 40 3 (Bx0-2431 ∷ CCZ124 ∷ []) (lem-T312-beta-at122441 c4) ▸ done

  b30 : Chain (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ Bx0-2431 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-2431 ∷ Bx0-1423 ∷ []) (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ Bx0-4231 ∷ CCZ134 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-2431 ∷ Bx0-1423 ∷ [])
  b30 = at 40 2 (CCZ124 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at122441 c4) ▸
       at 41 2 (CCZ124 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at122441 c4) ▸
       at 42 2 (CCZ124 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ214-at122441 c4) ▸
       at 43 0 (Toff234 ∷ Toff234 ∷ []) (lw0 c4 [] (Toff234 ∷ Toff234 ∷ []) tt tt Eq.refl) ▸
       at 45 1 (Bx0-4231 ∷ []) (lem-sym12-at122441 c4) ▸
       at 45 1 (Bx0-4321 ∷ []) (lem-sym23-at1441 c4) ▸
       at 44 3 (Bx0-4321 ∷ CCZ134 ∷ []) (lem-T312-beta-at14233241 c4) ▸
       at 44 1 (Bx0-4231 ∷ []) (lem-sym23-at14233241 c4) ▸ done

  b31 : Chain (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ Bx0-4231 ∷ CCZ134 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-2431 ∷ Bx0-1423 ∷ []) (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ Bx0-2431 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-2431 ∷ Bx0-1423 ∷ [])
  b31 = at 44 1 (Bx0-2431 ∷ []) (lem-sym12-at1441 c4) ▸
       at 44 2 (CCZ134 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ234-at122441 c4) ▸
       at 45 2 (CCZ134 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ234-at122441 c4) ▸
       at 46 2 (CCZ134 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ234-at122441 c4) ▸
       at 47 0 (Toff324 ∷ Toff324 ∷ []) (lw0 c4 [] (Toff324 ∷ Toff324 ∷ []) tt tt Eq.refl) ▸
       at 48 1 (Toff324 ∷ []) (lw0 c4 (Toff324 ∷ []) (Toff324 ∷ []) tt tt Eq.refl) ▸
       at 50 1 (Toff324 ∷ []) (lw0 c4 (Toff324 ∷ []) (Toff324 ∷ []) tt tt Eq.refl) ▸
       at 48 3 (Bx0-2431 ∷ CCZ124 ∷ []) (lem-T312-beta-at122441 c4) ▸ done

  b32 : Chain (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ Bx0-2431 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-2431 ∷ Bx0-1423 ∷ []) (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-1234 ∷ [])
  b32 = at 48 2 (CCZ124 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at122441 c4) ▸
       at 49 2 (CCZ124 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ124-at122441 c4) ▸
       at 50 2 (CCZ124 ∷ Bx0-2431 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ214-at122441 c4) ▸
       at 51 2 [] (lem-beta-inv-at122441 c4) ▸
       at 51 1 (Bx0-1243 ∷ []) (lem-sym23-at243243 c4) ▸
       at 51 1 (Bx0-1234 ∷ []) (lem-sym34-at3443 c4) ▸
       at 46 2 (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) (lw0 c4 (CCZ134 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 45 2 (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) (lw0 c4 (CCZ134 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸ done

  b33 : Chain (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-1234 ∷ []) (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ Toff234 ∷ CCZ124 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-1234 ∷ [])
  b33 = at 44 2 (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) (lw0 c4 (CCZ134 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 42 2 (Toff234 ∷ CCZ124 ∷ CCZ134 ∷ []) (lw0 c4 (CCZ124 ∷ Toff234 ∷ []) (Toff234 ∷ CCZ124 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 44 2 (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) (lw0 c4 (CCZ134 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 43 2 (Toff324 ∷ CCZ124 ∷ []) (lw0 c4 (CCZ124 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 41 2 (Toff234 ∷ CCZ124 ∷ CCZ134 ∷ []) (lw0 c4 (CCZ124 ∷ Toff234 ∷ []) (Toff234 ∷ CCZ124 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 43 2 (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) (lw0 c4 (CCZ134 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 42 2 (Toff324 ∷ CCZ124 ∷ []) (lw0 c4 (CCZ124 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 40 2 (Toff234 ∷ CCZ124 ∷ CCZ134 ∷ []) (lw0 c4 (CCZ124 ∷ Toff234 ∷ []) (Toff234 ∷ CCZ124 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸ done

  b34 : Chain (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ Toff234 ∷ CCZ124 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-1234 ∷ []) (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-1234 ∷ [])
  b34 = at 42 2 (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) (lw0 c4 (CCZ134 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 41 2 (Toff324 ∷ CCZ124 ∷ []) (lw0 c4 (CCZ124 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 28 2 (Toff324 ∷ CCZ124 ∷ []) (lw0 c4 (CCZ124 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 27 2 (Toff324 ∷ CCZ124 ∷ []) (lw0 c4 (CCZ124 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 25 2 (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) (lw0 c4 (CCZ134 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 27 2 (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) (lw0 c4 (CCZ134 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 26 2 (Toff324 ∷ CCZ124 ∷ []) (lw0 c4 (CCZ124 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 24 2 (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) (lw0 c4 (CCZ134 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸ done

  b35 : Chain (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff234 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-1234 ∷ []) (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-1234 ∷ [])
  b35 = at 26 2 (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) (lw0 c4 (CCZ134 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 25 2 (Toff324 ∷ CCZ124 ∷ []) (lw0 c4 (CCZ124 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 22 2 (Toff234 ∷ CCZ124 ∷ CCZ134 ∷ []) (lw0 c4 (CCZ124 ∷ Toff234 ∷ []) (Toff234 ∷ CCZ124 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 24 2 (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) (lw0 c4 (CCZ134 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 26 2 (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) (lw0 c4 (CCZ134 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 25 2 (Toff324 ∷ CCZ124 ∷ []) (lw0 c4 (CCZ124 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 23 2 (Toff324 ∷ CCZ124 ∷ []) (lw0 c4 (CCZ124 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 24 2 (Toff324 ∷ CCZ124 ∷ []) (lw0 c4 (CCZ124 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸ done

  b36 : Chain (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-1234 ∷ []) (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-1234 ∷ [])
  b36 = at 21 2 (Toff234 ∷ CCZ124 ∷ CCZ134 ∷ []) (lw0 c4 (CCZ124 ∷ Toff234 ∷ []) (Toff234 ∷ CCZ124 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 23 2 (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) (lw0 c4 (CCZ134 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 25 2 (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) (lw0 c4 (CCZ134 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 24 2 (Toff324 ∷ CCZ124 ∷ []) (lw0 c4 (CCZ124 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 22 2 (Toff324 ∷ CCZ124 ∷ []) (lw0 c4 (CCZ124 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 23 2 (Toff324 ∷ CCZ124 ∷ []) (lw0 c4 (CCZ124 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 19 2 (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) (lw0 c4 (CCZ134 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 21 2 (Toff234 ∷ CCZ134 ∷ []) (lw0 c4 (CCZ134 ∷ Toff234 ∷ []) (Toff234 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸ done

  b37 : Chain (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-1234 ∷ []) (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-1234 ∷ [])
  b37 = at 22 2 (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) (lw0 c4 (CCZ134 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 24 2 (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) (lw0 c4 (CCZ134 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 23 2 (Toff324 ∷ CCZ124 ∷ []) (lw0 c4 (CCZ124 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 20 2 (Toff234 ∷ CCZ124 ∷ CCZ134 ∷ []) (lw0 c4 (CCZ124 ∷ Toff234 ∷ []) (Toff234 ∷ CCZ124 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 22 2 (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) (lw0 c4 (CCZ134 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 24 2 (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) (lw0 c4 (CCZ134 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 23 2 (Toff324 ∷ CCZ124 ∷ []) (lw0 c4 (CCZ124 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 21 2 (Toff324 ∷ CCZ124 ∷ []) (lw0 c4 (CCZ124 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸ done

  b38 : Chain (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-1234 ∷ []) (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ Toff324 ∷ Toff234 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-1234 ∷ [])
  b38 = at 22 2 (Toff324 ∷ CCZ124 ∷ []) (lw0 c4 (CCZ124 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 18 2 (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) (lw0 c4 (CCZ134 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 20 2 (Toff234 ∷ CCZ134 ∷ []) (lw0 c4 (CCZ134 ∷ Toff234 ∷ []) (Toff234 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 21 2 (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) (lw0 c4 (CCZ134 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 23 2 (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) (lw0 c4 (CCZ134 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 22 2 (Toff324 ∷ CCZ124 ∷ []) (lw0 c4 (CCZ124 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 19 2 (Toff234 ∷ CCZ124 ∷ CCZ134 ∷ []) (lw0 c4 (CCZ124 ∷ Toff234 ∷ []) (Toff234 ∷ CCZ124 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 21 2 (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) (lw0 c4 (CCZ134 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸ done

  b39 : Chain (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ Toff324 ∷ Toff234 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-1234 ∷ []) (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ Toff134 ∷ CZ34 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ CCZ134 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-1234 ∷ [])
  b39 = at 23 2 (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) (lw0 c4 (CCZ134 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 22 2 (Toff324 ∷ CCZ124 ∷ []) (lw0 c4 (CCZ124 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 20 2 (Toff324 ∷ CCZ124 ∷ []) (lw0 c4 (CCZ124 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 21 2 (Toff324 ∷ CCZ124 ∷ []) (lw0 c4 (CCZ124 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (Toff134 ∷ CCZ234 ∷ []) (lw0 c4 (CCZ234 ∷ Toff134 ∷ []) (Toff134 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff134 ∷ CZ34 ∷ CCZ134 ∷ []) (lw0 c4 (CCZ134 ∷ Toff134 ∷ []) (Toff134 ∷ CZ34 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 65 2 [] (lw0 c4 (CCZ124 ∷ CCZ124 ∷ []) [] tt tt Eq.refl) ▸
       at 66 3 (CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ []) (lw0 c4 (CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸ done

  b40 : Chain (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ Toff134 ∷ CZ34 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ CCZ134 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-1234 ∷ []) (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ Toff134 ∷ CZ34 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-1234 ∷ [])
  b40 = at 65 2 [] (lw0 c4 (CCZ134 ∷ CCZ134 ∷ []) [] tt tt Eq.refl) ▸
       at 65 2 [] (lw0 c4 (CCZ124 ∷ CCZ124 ∷ []) [] tt tt Eq.refl) ▸
       at 65 2 [] (lw0 c4 (CCZ124 ∷ CCZ124 ∷ []) [] tt tt Eq.refl) ▸
       at 66 2 (CCZ134 ∷ CCZ124 ∷ []) (lw0 c4 (CCZ124 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 65 2 [] (lw0 c4 (CCZ134 ∷ CCZ134 ∷ []) [] tt tt Eq.refl) ▸
       at 65 2 [] (lw0 c4 (CCZ124 ∷ CCZ124 ∷ []) [] tt tt Eq.refl) ▸
       at 66 2 (CCZ134 ∷ CCZ124 ∷ []) (lw0 c4 (CCZ124 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 65 2 [] (lw0 c4 (CCZ134 ∷ CCZ134 ∷ []) [] tt tt Eq.refl) ▸ done

  b41 : Chain (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ Toff134 ∷ CZ34 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ [])
  b41 = at 66 2 [] (lw0 c4 (CCZ124 ∷ CCZ124 ∷ []) [] tt tt Eq.refl) ▸
       at 0 67 [] (lw0 c4 (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ Toff134 ∷ CZ34 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CCZ234 ∷ CS12⁻ ∷ Toff214 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ CCZ124 ∷ CS13⁻ ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ []) [] tt tt Eq.refl) ▸
       at 0 1 (Bx0-1234 ∷ []) (sym (lem-boxify-9-nf-of-rhs c4)) ▸ done


-- auto CCZ012 | CCZ340: 15 steps
lem-auto-CCZ012-∣-CCZ340 : Complete 4 → ⟪ (CCZ012 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-CCZ340 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ012 ∷ CCZ034 ∷ []) (CS03 ∷ CS02 ∷ CX12 ∷ CX40 ∷ CS03⁻ ∷ CX40 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ CS34 ∷ [])
  b0 = at 1 1 (CS03 ∷ CX40 ∷ CS03⁻ ∷ CX40 ∷ CS34 ∷ []) (pw1 c4 (CCZ034 ∷ []) (CS03 ∷ CX40 ∷ CS03⁻ ∷ CX40 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (CS03 ∷ CCZ012 ∷ []) (lw4 c4 (CCZ012 ∷ CS03 ∷ []) (CS03 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 5 4 (CX40 ∷ CS03⁻ ∷ CX40 ∷ CS01 ∷ []) (pw2 c4 (CS01 ∷ CX40 ∷ CS03⁻ ∷ CX40 ∷ []) (CX40 ∷ CS03⁻ ∷ CX40 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CX40 ∷ CX12 ∷ []) (pw3 c4 (CX12 ∷ CX40 ∷ []) (CX40 ∷ CX12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CS03⁻ ∷ CX12 ∷ []) (lw4 c4 (CX12 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CX12 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CX40 ∷ CX12 ∷ []) (pw3 c4 (CX12 ∷ CX40 ∷ []) (CX40 ∷ CX12 ∷ []) tt tt Eq.refl) ▸
       at 3 4 (CX40 ∷ CS03⁻ ∷ CX40 ∷ CS02⁻ ∷ []) (pw1 c4 (CS02⁻ ∷ CX40 ∷ CS03⁻ ∷ CX40 ∷ []) (CX40 ∷ CS03⁻ ∷ CX40 ∷ CS02⁻ ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CS03 ∷ CS02 ∷ CX12 ∷ CX40 ∷ CS03⁻ ∷ CX40 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ CS34 ∷ []) (CCZ034 ∷ CCZ012 ∷ [])
  b1 = at 2 2 (CX40 ∷ CX12 ∷ []) (pw3 c4 (CX12 ∷ CX40 ∷ []) (CX40 ∷ CX12 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CS03⁻ ∷ CX12 ∷ []) (lw4 c4 (CX12 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CX12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CX40 ∷ CX12 ∷ []) (pw3 c4 (CX12 ∷ CX40 ∷ []) (CX40 ∷ CX12 ∷ []) tt tt Eq.refl) ▸
       at 1 4 (CX40 ∷ CS03⁻ ∷ CX40 ∷ CS02 ∷ []) (pw1 c4 (CS02 ∷ CX40 ∷ CS03⁻ ∷ CX40 ∷ []) (CX40 ∷ CS03⁻ ∷ CX40 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 4 5 (CCZ012 ∷ []) (lw4 c4 (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CS34 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-CS34-at3443 c4) ▸
       at 0 5 (CCZ034 ∷ []) (pw1 c4 (CS03 ∷ CX40 ∷ CS03⁻ ∷ CX40 ∷ CS34 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl) ▸ done


-- auto CCZ012 | TOFF340: 5 steps
lem-auto-CCZ012-∣-TOFF340 : Complete 4 → ⟪ (CCZ012 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-TOFF340 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Toff304 ∷ []) (Toff304 ∷ CCZ012 ∷ [])
  b0 = at 1 1 (K3 ∷ CCZ034 ∷ K3⁻ ∷ []) (pw1 c4 (Toff304 ∷ []) (K3 ∷ CCZ034 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 0 2 (K3 ∷ CCZ012 ∷ []) (lw4 c4 (CCZ012 ∷ K3 ∷ []) (K3 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ034 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-CCZ340 c4) ▸
       at 2 2 (K3⁻ ∷ CCZ012 ∷ []) (lw4 c4 (CCZ012 ∷ K3⁻ ∷ []) (K3⁻ ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Toff304 ∷ []) (pw1 c4 (K3 ∷ CCZ034 ∷ K3⁻ ∷ []) (Toff304 ∷ []) tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ120: 3 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ120 : Complete 4 → ⟪ (Bx0-1234 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ120 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ CCZ012 ∷ []) (CCZ012 ∷ Bx0-1234 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (CCZ012 ∷ Bx0-1234 ∷ []) (sym (lem-Cz-beta c4)) ▸
       at 0 1 (CCZ012 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸ done

