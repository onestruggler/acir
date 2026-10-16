{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D002 where

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
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-auto-CCZ012-∣-CCZ304 ; lem-auto-CCZ012-∣-CCZ314 ; lem-auto-CCZ012-∣-TOFF304 ; lem-auto-TOFF012-∣-CCZ324-at0330 ; lem-beta-T ; lem-beta-form-at2332 ; lem-beta-inv ; lem-c124-beta ; lem-sym12 ; lem-sym23 ; lem-sym34)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-1-BOX⟨0·2134⟩ ; lem-nat-1-CCZ023 ; lem-nat-1-CCZ024 ; lem-nat-1-CCZ034 ; lem-nat-1-TOFF203 ; lem-nat-2-BOX⟨0·1234⟩ ; lem-nat-2-BOX⟨0·1324⟩ ; lem-nat-2-CCZ012 ; lem-nat-2-CCZ013 ; lem-nat-2-CCZ024 ; lem-nat-2-CCZ034 ; lem-nat-2-TOFF012 ; lem-nat-3-BOX⟨0·1243⟩ ; lem-nat-3-BOX⟨0·1423⟩ ; lem-nat-3-CCZ014 ; lem-nat-3-CCZ024 ; lem-nat-3-TOFF013)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-1-CCZ013 ; lem-nat-1-CCZ014 ; lem-nat-3-BOX⟨0·1324⟩ ; lem-nat-3-CCZ013 ; lem-nat-3-CCZ023)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-comm-CS03-TOFF214 ; lem-comm-TOFF214-CSd03 ; lem-comm-TOFF314-CS02 ; lem-comm-TOFF314-CSd02 ; lem-nat-0-CCZ024 ; lem-nat-0-CCZ124 ; lem-nat-1-TOFF103 ; lem-nat-2-BOX⟨0·3124⟩ ; lem-nat-2-CCZ124 ; lem-nat-2-CCZ134 ; lem-nat-2-TOFF204 ; lem-nat-2-TOFF304 ; lem-nat-3-TOFF203 ; lem-nat-3-TOFF204)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-0-BOX⟨1·4023⟩ ; lem-nat-0-CCZ014 ; lem-nat-0-TOFF014 ; lem-nat-1-BOX⟨2·4013⟩ ; lem-nat-1-TOFF104 ; lem-nat-1-TOFF204 ; lem-nat-2-BOX⟨3·4012⟩ ; lem-nat-3-BOX⟨0·4123⟩)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-0-BOX⟨3·4102⟩ ; lem-nat-0-CCZ134 ; lem-nat-0-TOFF304 ; lem-nat-1-BOX⟨0·1243⟩)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-0-BOX⟨0·4132⟩ ; lem-nat-0-BOX⟨3·4021⟩ ; lem-nat-0-TOFF204 ; lem-nat-1-BOX⟨0·1234⟩ ; lem-nat-1-BOX⟨1·4032⟩ ; lem-nat-2-BOX⟨0·2134⟩ ; lem-nat-2-BOX⟨0·2143⟩ ; lem-nat-2-BOX⟨2·4031⟩ ; lem-nat-3-BOX⟨0·3124⟩ ; lem-nat-3-BOX⟨0·3142⟩ ; lem-nat-3-TOFF214)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-nat-0-BOX⟨0·4123⟩ ; lem-nat-0-BOX⟨3·4120⟩ ; lem-nat-0-TOFF214 ; lem-nat-1-BOX⟨1·4023⟩ ; lem-nat-1-BOX⟨3·4012⟩ ; lem-nat-1-BOX⟨3·4021⟩ ; lem-nat-2-BOX⟨2·4013⟩ ; lem-nat-2-TOFF104)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-0-BOX⟨0·1423⟩ ; lem-nat-0-BOX⟨0·4213⟩ ; lem-nat-0-BOX⟨3·4012⟩ ; lem-nat-1-BOX⟨0·1324⟩ ; lem-nat-1-BOX⟨1·0423⟩ ; lem-nat-1-BOX⟨1·4203⟩ ; lem-nat-2-BOX⟨0·2314⟩ ; lem-nat-2-BOX⟨2·4103⟩ ; lem-nat-3-BOX⟨0·3214⟩)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-nat-0-BOX⟨0·1243⟩ ; lem-nat-0-BOX⟨1·0234⟩ ; lem-nat-0-BOX⟨1·0423⟩ ; lem-nat-0-BOX⟨2·4103⟩ ; lem-nat-1-BOX⟨1·0243⟩ ; lem-nat-1-BOX⟨2·0134⟩ ; lem-nat-1-BOX⟨2·0413⟩ ; lem-nat-2-BOX⟨2·0143⟩ ; lem-nat-2-BOX⟨2·0413⟩ ; lem-nat-2-BOX⟨3·0124⟩ ; lem-nat-2-BOX⟨3·0412⟩ ; lem-nat-3-BOX⟨0·1234⟩ ; lem-nat-3-CCZ123 ; lem-nat-3-CCZ124)
-- auto CCZ012 | CCZ314 @2332: 7 steps
lem-auto-CCZ012-∣-CCZ314-at2332 : Complete 4 → ⟪ (CCZ013 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ CCZ013 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-CCZ314-at2332 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ013 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 2 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 1 2 (CCZ134 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-CCZ314 c4) ▸
       at 0 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 1 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | CCZ314 @122331: 7 steps
lem-auto-CCZ012-∣-CCZ314-at122331 : Complete 4 → ⟪ (CCZ023 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ CCZ023 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-CCZ314-at122331 c4 = run b0
  where
  b0 : Chain (CCZ023 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ023 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 2 2 (CCZ124 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ124 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-CCZ314-at2332 c4) ▸
       at 0 2 (CCZ124 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | CCZ314 @01122330: 7 steps
lem-auto-CCZ012-∣-CCZ314-at01122330 : Complete 4 → ⟪ (CCZ123 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ CCZ123 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-CCZ314-at01122330 c4 = run b0
  where
  b0 : Chain (CCZ123 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ123 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ123 ∷ []) (CCZ023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 1 2 (CCZ124 ∷ CCZ023 ∷ []) (lem-auto-CCZ012-∣-CCZ314-at122331 c4) ▸
       at 0 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 1 2 (CCZ123 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ023 ∷ []) (CCZ123 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | TOFF304 @2332: 7 steps
lem-auto-CCZ012-∣-TOFF304-at2332 : Complete 4 → ⟪ (CCZ013 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CCZ013 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-TOFF304-at2332 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ Toff204 ∷ []) (Toff204 ∷ CCZ013 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 2 2 (Toff304 ∷ Sw23 ∷ []) (lem-nat-2-TOFF204 c4) ▸
       at 1 2 (Toff304 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-TOFF304 c4) ▸
       at 0 2 (Toff204 ∷ Sw23 ∷ []) (lem-nat-2-TOFF304 c4) ▸
       at 1 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | TOFF304 @243243: 7 steps
lem-auto-CCZ012-∣-TOFF304-at243243 : Complete 4 → ⟪ (CCZ014 ∷ Toff203 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ CCZ014 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-TOFF304-at243243 c4 = run b0
  where
  b0 : Chain (CCZ014 ∷ Toff203 ∷ []) (Toff203 ∷ CCZ014 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4) ▸
       at 2 2 (Toff204 ∷ Sw34 ∷ []) (lem-nat-3-TOFF203 c4) ▸
       at 1 2 (Toff204 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-TOFF304-at2332 c4) ▸
       at 0 2 (Toff203 ∷ Sw34 ∷ []) (lem-nat-3-TOFF204 c4) ▸
       at 1 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | TOFF304 @12243143: 7 steps
lem-auto-CCZ012-∣-TOFF304-at12243143 : Complete 4 → ⟪ (CCZ024 ∷ Toff103 ∷ []) ⟫ʷ ≈ ⟪ (Toff103 ∷ CCZ024 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-TOFF304-at12243143 c4 = run b0
  where
  b0 : Chain (CCZ024 ∷ Toff103 ∷ []) (Toff103 ∷ CCZ024 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 2 2 (Toff203 ∷ Sw12 ∷ []) (lem-nat-1-TOFF103 c4) ▸
       at 1 2 (Toff203 ∷ CCZ014 ∷ []) (lem-auto-CCZ012-∣-TOFF304-at243243 c4) ▸
       at 0 2 (Toff103 ∷ Sw12 ∷ []) (lem-nat-1-TOFF203 c4) ▸
       at 1 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | TOFF304 @0112243043: 7 steps
lem-auto-CCZ012-∣-TOFF304-at0112243043 : Complete 4 → ⟪ (CCZ124 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CCZ124 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-TOFF304-at0112243043 c4 = run b0
  where
  b0 : Chain (CCZ124 ∷ Toff013 ∷ []) (Toff013 ∷ CCZ124 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 2 2 (Toff103 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff013 ∷ []) (Toff103 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff103 ∷ CCZ024 ∷ []) (lem-auto-CCZ012-∣-TOFF304-at12243143 c4) ▸
       at 0 2 (Toff013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff103 ∷ []) (Toff013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | CCZ304 @2332: 7 steps
lem-auto-CCZ012-∣-CCZ304-at2332 : Complete 4 → ⟪ (CCZ013 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ CCZ013 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-CCZ304-at2332 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ013 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 2 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 1 2 (CCZ034 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-CCZ304 c4) ▸
       at 0 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 1 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | CCZ304 @243243: 7 steps
lem-auto-CCZ012-∣-CCZ304-at243243 : Complete 4 → ⟪ (CCZ014 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ CCZ014 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-CCZ304-at243243 c4 = run b0
  where
  b0 : Chain (CCZ014 ∷ CCZ023 ∷ []) (CCZ023 ∷ CCZ014 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4) ▸
       at 2 2 (CCZ024 ∷ Sw34 ∷ []) (lem-nat-3-CCZ023 c4) ▸
       at 1 2 (CCZ024 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-CCZ304-at2332 c4) ▸
       at 0 2 (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 c4) ▸
       at 1 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | CCZ304 @12243143: 7 steps
lem-auto-CCZ012-∣-CCZ304-at12243143 : Complete 4 → ⟪ (CCZ024 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ CCZ024 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-CCZ304-at12243143 c4 = run b0
  where
  b0 : Chain (CCZ024 ∷ CCZ013 ∷ []) (CCZ013 ∷ CCZ024 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 2 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 1 2 (CCZ023 ∷ CCZ014 ∷ []) (lem-auto-CCZ012-∣-CCZ304-at243243 c4) ▸
       at 0 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 1 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | CCZ304 @0112243043: 7 steps
lem-auto-CCZ012-∣-CCZ304-at0112243043 : Complete 4 → ⟪ (CCZ124 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ CCZ124 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-CCZ304-at0112243043 c4 = run b0
  where
  b0 : Chain (CCZ124 ∷ CCZ013 ∷ []) (CCZ013 ∷ CCZ124 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 2 2 (CCZ013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ013 ∷ CCZ024 ∷ []) (lem-auto-CCZ012-∣-CCZ304-at12243143 c4) ▸
       at 0 2 (CCZ013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- T312-beta: 17 steps
lem-T312-beta : Complete 4 → ⟪ (Toff312 ∷ Bx0-1234 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CCZ124 ∷ []) ⟫ʷ
lem-T312-beta c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Toff312 ∷ Bx0-1234 ∷ Toff312 ∷ []) (CCZ013 ∷ Toff013 ∷ CCZ012 ∷ Toff012 ∷ CCZ123 ∷ CCZ024 ∷ CCZ123 ∷ Toff012 ∷ CCZ012 ∷ Toff013 ∷ CCZ013 ∷ CCZ024 ∷ Toff312 ∷ Toff312 ∷ [])
  b0 = at 1 1 (Bx0-1324 ∷ []) (lem-sym23 c4) ▸
       at 1 1 (CCZ013 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ CCZ024 ∷ []) (lem-beta-form-at2332 c4) ▸
       at 3 0 (Toff312 ∷ Toff312 ∷ []) (lw4 c4 [] (Toff312 ∷ Toff312 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (CCZ013 ∷ Toff013 ∷ CCZ012 ∷ Toff012 ∷ CCZ123 ∷ []) (lw4 c4 (Toff312 ∷ CCZ013 ∷ Toff013 ∷ Toff312 ∷ []) (CCZ013 ∷ Toff013 ∷ CCZ012 ∷ Toff012 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ024 ∷ Toff312 ∷ []) (lem-auto-TOFF012-∣-CCZ324-at0330 c4) ▸
       at 9 0 (Toff312 ∷ Toff312 ∷ []) (lw4 c4 [] (Toff312 ∷ Toff312 ∷ []) tt tt Eq.refl) ▸
       at 6 4 (CCZ123 ∷ Toff012 ∷ CCZ012 ∷ Toff013 ∷ CCZ013 ∷ []) (lw4 c4 (Toff312 ∷ Toff013 ∷ CCZ013 ∷ Toff312 ∷ []) (CCZ123 ∷ Toff012 ∷ CCZ012 ∷ Toff013 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (CCZ024 ∷ Toff312 ∷ []) (lem-auto-TOFF012-∣-CCZ324-at0330 c4) ▸ done

  b1 : Chain (CCZ013 ∷ Toff013 ∷ CCZ012 ∷ Toff012 ∷ CCZ123 ∷ CCZ024 ∷ CCZ123 ∷ Toff012 ∷ CCZ012 ∷ Toff013 ∷ CCZ013 ∷ CCZ024 ∷ Toff312 ∷ Toff312 ∷ []) (Bx0-1324 ∷ CCZ124 ∷ [])
  b1 = at 12 2 [] (lw4 c4 (Toff312 ∷ Toff312 ∷ []) [] tt tt Eq.refl) ▸
       at 4 2 (CCZ024 ∷ CCZ123 ∷ []) (lem-auto-CCZ012-∣-CCZ314-at01122330 c4) ▸
       at 5 2 [] (lw4 c4 (CCZ123 ∷ CCZ123 ∷ []) [] tt tt Eq.refl) ▸
       at 2 5 (CCZ024 ∷ CCZ124 ∷ []) (pw3 c4 (CCZ012 ∷ Toff012 ∷ CCZ024 ∷ Toff012 ∷ CCZ012 ∷ []) (CCZ024 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff013 ∷ CCZ124 ∷ []) (lem-auto-CCZ012-∣-TOFF304-at0112243043 c4) ▸
       at 4 2 (CCZ013 ∷ CCZ124 ∷ []) (lem-auto-CCZ012-∣-CCZ304-at0112243043 c4) ▸
       at 5 2 (CCZ024 ∷ CCZ124 ∷ []) (pw3 c4 (CCZ124 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 0 6 (Bx0-1324 ∷ []) (sym (lem-beta-form-at2332 c4)) ▸ done

  b2 : Chain (Bx0-1324 ∷ CCZ124 ∷ []) (Bx0-1234 ∷ CCZ124 ∷ [])
  b2 = at 0 1 (Bx0-1234 ∷ []) (sym (lem-sym23 c4)) ▸ done


-- F0-A: 9 steps
lem-F0-A : Complete 4 → ⟪ (Toff214 ∷ Toff314 ∷ CS02⁻ ∷ CS03⁻ ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ CS03⁻ ∷ CCZ023 ∷ Toff214 ∷ Toff314 ∷ []) ⟫ʷ
lem-F0-A c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff214 ∷ Toff314 ∷ CS02⁻ ∷ CS03⁻ ∷ CCZ023 ∷ []) (CS02⁻ ∷ CS03⁻ ∷ CCZ023 ∷ CX23 ∷ CX23 ∷ Toff214 ∷ Toff314 ∷ [])
  b0 = at 0 0 (CX23 ∷ CX23 ∷ []) (lw4 c4 [] (CX23 ∷ CX23 ∷ []) tt tt Eq.refl) ▸
       at 4 0 (CX23 ∷ CX23 ∷ []) (lw4 c4 [] (CX23 ∷ CX23 ∷ []) tt tt Eq.refl) ▸
       at 9 0 (CX23 ∷ CX23 ∷ []) (lw4 c4 [] (CX23 ∷ CX23 ∷ []) tt tt Eq.refl) ▸
       at 1 4 (Toff214 ∷ []) (lw0 c4 (CX23 ∷ Toff214 ∷ Toff314 ∷ CX23 ∷ []) (Toff214 ∷ []) tt tt Eq.refl) ▸
       at 2 5 (CS03⁻ ∷ []) (lw4 c4 (CX23 ∷ CS02⁻ ∷ CS03⁻ ∷ CCZ023 ∷ CX23 ∷ []) (CS03⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS03⁻ ∷ Toff214 ∷ []) (lem-comm-TOFF214-CSd03 c4) ▸
       at 0 2 (CS02⁻ ∷ CS03⁻ ∷ CCZ023 ∷ CX23 ∷ []) (lw4 c4 (CX23 ∷ CS03⁻ ∷ []) (CS02⁻ ∷ CS03⁻ ∷ CCZ023 ∷ CX23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CX23 ∷ Toff214 ∷ Toff314 ∷ []) (lw0 c4 (Toff214 ∷ CX23 ∷ []) (CX23 ∷ Toff214 ∷ Toff314 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CS02⁻ ∷ CS03⁻ ∷ CCZ023 ∷ CX23 ∷ CX23 ∷ Toff214 ∷ Toff314 ∷ []) (CS02⁻ ∷ CS03⁻ ∷ CCZ023 ∷ Toff214 ∷ Toff314 ∷ [])
  b1 = at 3 2 [] (lw4 c4 (CX23 ∷ CX23 ∷ []) [] tt tt Eq.refl) ▸ done


-- F0-B: 6 steps
lem-F0-B : Complete 4 → ⟪ (Toff214 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ Toff214 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ Toff314 ∷ CS02 ∷ CS03 ∷ Toff314 ∷ Toff214 ∷ CS03⁻ ∷ CS02⁻ ∷ []) ⟫ʷ
lem-F0-B c4 = run b0
  where
  b0 : Chain (Toff214 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ Toff214 ∷ CCZ023 ∷ []) (Toff214 ∷ Toff314 ∷ CS02 ∷ CS03 ∷ Toff314 ∷ Toff214 ∷ CS03⁻ ∷ CS02⁻ ∷ [])
  b0 = at 2 1 (CS02 ∷ CS03 ∷ CS02⁻ ∷ CS03⁻ ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ []) (CS02 ∷ CS03 ∷ CS02⁻ ∷ CS03⁻ ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff214 ∷ Toff314 ∷ []) (lw0 c4 (Toff314 ∷ Toff214 ∷ []) (Toff214 ∷ Toff314 ∷ []) tt tt Eq.refl) ▸
       at 4 5 (Toff214 ∷ Toff314 ∷ CS02⁻ ∷ CS03⁻ ∷ CCZ023 ∷ []) (sym (lem-F0-A c4)) ▸
       at 4 0 [] (lw4 c4 [] [] tt tt Eq.refl) ▸
       at 6 4 (CS03⁻ ∷ CS02⁻ ∷ []) (lw4 c4 (CS02⁻ ∷ CS03⁻ ∷ CCZ023 ∷ CCZ023 ∷ []) (CS03⁻ ∷ CS02⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff314 ∷ Toff214 ∷ []) (lw0 c4 (Toff214 ∷ Toff314 ∷ []) (Toff314 ∷ Toff214 ∷ []) tt tt Eq.refl) ▸ done


-- F0-C: 8 steps
lem-F0-C : Complete 4 → ⟪ (Toff214 ∷ Toff314 ∷ CS02 ∷ CS03 ∷ Toff314 ∷ Toff214 ∷ CS03⁻ ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-F0-C c4 = run b0
  where
  b0 : Chain (Toff214 ∷ Toff314 ∷ CS02 ∷ CS03 ∷ Toff314 ∷ Toff214 ∷ CS03⁻ ∷ CS02⁻ ∷ []) (Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b0 = at 1 2 (CS02 ∷ Toff314 ∷ []) (lem-comm-TOFF314-CS02 c4) ▸
       at 4 2 (Toff214 ∷ Toff314 ∷ []) (lw0 c4 (Toff314 ∷ Toff214 ∷ []) (Toff214 ∷ Toff314 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff214 ∷ CS03 ∷ []) (lem-comm-CS03-TOFF214 c4) ▸
       at 2 2 (Toff214 ∷ Toff314 ∷ []) (lw0 c4 (Toff314 ∷ Toff214 ∷ []) (Toff214 ∷ Toff314 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CS02⁻ ∷ CS03⁻ ∷ []) (lw4 c4 (CS03⁻ ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CS03⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CS02⁻ ∷ Toff314 ∷ []) (lem-comm-TOFF314-CSd02 c4) ▸
       at 4 2 (CS02⁻ ∷ CS03 ∷ []) (lw4 c4 (CS03 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CS02⁻ ∷ Toff314 ∷ []) (lem-comm-TOFF314-CSd02 c4) ▸ done


-- beta-T @1221: 8 steps
lem-beta-T-at1221 : Complete 4 → ⟪ (Bx0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) ⟫ʷ
lem-beta-T-at1221 c4 = run b0
  where
  b0 : Chain (Bx0-2134 ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2134⟩ c4) ▸
       at 1 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-beta-T c4) ▸
       at 0 2 (Toff012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff012 ∷ []) (Toff012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 2 2 (Toff012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff012 ∷ []) (Toff012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 4 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- beta-T @132132: 8 steps
lem-beta-T-at132132 : Complete 4 → ⟪ (Bx0-3124 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) ⟫ʷ
lem-beta-T-at132132 c4 = run b0
  where
  b0 : Chain (Bx0-3124 ∷ []) (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-2134 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3124⟩ c4) ▸
       at 1 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-beta-T-at1221 c4) ▸
       at 0 2 (Toff013 ∷ Sw23 ∷ []) (lem-nat-2-TOFF012 c4) ▸
       at 1 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 2 2 (Toff013 ∷ Sw23 ∷ []) (lem-nat-2-TOFF012 c4) ▸
       at 3 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 4 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- beta-T @14213243: 8 steps
lem-beta-T-at14213243 : Complete 4 → ⟪ (Bx0-4123 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) ⟫ʷ
lem-beta-T-at14213243 c4 = run b0
  where
  b0 : Chain (Bx0-4123 ∷ []) (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-3124 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·4123⟩ c4) ▸
       at 1 1 (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) (lem-beta-T-at132132 c4) ▸
       at 0 2 (Toff014 ∷ Sw34 ∷ []) (lem-nat-3-TOFF013 c4) ▸
       at 1 2 (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 c4) ▸
       at 2 2 (Toff014 ∷ Sw34 ∷ []) (lem-nat-3-TOFF013 c4) ▸
       at 3 2 (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 c4) ▸
       at 4 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- beta-T @0114203243: 8 steps
lem-beta-T-at0114203243 : Complete 4 → ⟪ (Bx1-4023 ∷ []) ⟫ʷ ≈ ⟪ (Toff104 ∷ CCZ123 ∷ Toff104 ∷ CCZ123 ∷ []) ⟫ʷ
lem-beta-T-at0114203243 c4 = run b0
  where
  b0 : Chain (Bx1-4023 ∷ []) (Toff104 ∷ CCZ123 ∷ Toff104 ∷ CCZ123 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-4123 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·4023⟩ c4) ▸
       at 1 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-beta-T-at14213243 c4) ▸
       at 0 2 (Toff104 ∷ Sw01 ∷ []) (lem-nat-0-TOFF014 c4) ▸
       at 1 2 (CCZ123 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ023 ∷ []) (CCZ123 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff104 ∷ Sw01 ∷ []) (lem-nat-0-TOFF014 c4) ▸
       at 3 2 (CCZ123 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ023 ∷ []) (CCZ123 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- beta-T @0214203143: 8 steps
lem-beta-T-at0214203143 : Complete 4 → ⟪ (Bx2-4013 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) ⟫ʷ
lem-beta-T-at0214203143 c4 = run b0
  where
  b0 : Chain (Bx2-4013 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-4023 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·4013⟩ c4) ▸
       at 1 1 (Toff104 ∷ CCZ123 ∷ Toff104 ∷ CCZ123 ∷ []) (lem-beta-T-at0114203243 c4) ▸
       at 0 2 (Toff204 ∷ Sw12 ∷ []) (lem-nat-1-TOFF104 c4) ▸
       at 1 2 (CCZ123 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff204 ∷ Sw12 ∷ []) (lem-nat-1-TOFF104 c4) ▸
       at 3 2 (CCZ123 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- beta-T @0314203142: 8 steps
lem-beta-T-at0314203142 : Complete 4 → ⟪ (Bx3-4012 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) ⟫ʷ
lem-beta-T-at0314203142 c4 = run b0
  where
  b0 : Chain (Bx3-4012 ∷ []) (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx2-4013 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·4012⟩ c4) ▸
       at 1 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0214203143 c4) ▸
       at 0 2 (Toff304 ∷ Sw23 ∷ []) (lem-nat-2-TOFF204 c4) ▸
       at 1 2 (CCZ123 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff304 ∷ Sw23 ∷ []) (lem-nat-2-TOFF204 c4) ▸
       at 3 2 (CCZ123 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- beta-T @0314213042: 8 steps
lem-beta-T-at0314213042 : Complete 4 → ⟪ (Bx3-4102 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ []) ⟫ʷ
lem-beta-T-at0314213042 c4 = run b0
  where
  b0 : Chain (Bx3-4102 ∷ []) (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-4012 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·4102⟩ c4) ▸
       at 1 1 (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) (lem-beta-T-at0314203142 c4) ▸
       at 0 2 (Toff314 ∷ Sw01 ∷ []) (lem-nat-0-TOFF304 c4) ▸
       at 1 2 (CCZ023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ123 ∷ []) (CCZ023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff314 ∷ Sw01 ∷ []) (lem-nat-0-TOFF304 c4) ▸
       at 3 2 (CCZ023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ123 ∷ []) (CCZ023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym34 @1221: 5 steps
lem-sym34-at1221 : Complete 4 → ⟪ (Bx0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2143 ∷ []) ⟫ʷ
lem-sym34-at1221 c4 = run b0
  where
  b0 : Chain (Bx0-2134 ∷ []) (Bx0-2143 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2134⟩ c4) ▸
       at 1 1 (Bx0-1243 ∷ []) (lem-sym34 c4) ▸
       at 0 2 (Bx0-2143 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1243⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym34 @132132: 5 steps
lem-sym34-at132132 : Complete 4 → ⟪ (Bx0-3124 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3142 ∷ []) ⟫ʷ
lem-sym34-at132132 c4 = run b0
  where
  b0 : Chain (Bx0-3124 ∷ []) (Bx0-3142 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-2134 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3124⟩ c4) ▸
       at 1 1 (Bx0-2143 ∷ []) (lem-sym34-at1221 c4) ▸
       at 0 2 (Bx0-3142 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·2143⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym34 @14213243: 5 steps
lem-sym34-at14213243 : Complete 4 → ⟪ (Bx0-4123 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4132 ∷ []) ⟫ʷ
lem-sym34-at14213243 c4 = run b0
  where
  b0 : Chain (Bx0-4123 ∷ []) (Bx0-4132 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-3124 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·4123⟩ c4) ▸
       at 1 1 (Bx0-3142 ∷ []) (lem-sym34-at132132 c4) ▸
       at 0 2 (Bx0-4132 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·3142⟩ c4) ▸
       at 1 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym34 @0114203243: 5 steps
lem-sym34-at0114203243 : Complete 4 → ⟪ (Bx1-4023 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-4032 ∷ []) ⟫ʷ
lem-sym34-at0114203243 c4 = run b0
  where
  b0 : Chain (Bx1-4023 ∷ []) (Bx1-4032 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-4123 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·4023⟩ c4) ▸
       at 1 1 (Bx0-4132 ∷ []) (lem-sym34-at14213243 c4) ▸
       at 0 2 (Bx1-4032 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·4132⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym34 @0214203143: 5 steps
lem-sym34-at0214203143 : Complete 4 → ⟪ (Bx2-4013 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4031 ∷ []) ⟫ʷ
lem-sym34-at0214203143 c4 = run b0
  where
  b0 : Chain (Bx2-4013 ∷ []) (Bx2-4031 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-4023 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·4013⟩ c4) ▸
       at 1 1 (Bx1-4032 ∷ []) (lem-sym34-at0114203243 c4) ▸
       at 0 2 (Bx2-4031 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·4032⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym34 @0314203142: 5 steps
lem-sym34-at0314203142 : Complete 4 → ⟪ (Bx3-4012 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4021 ∷ []) ⟫ʷ
lem-sym34-at0314203142 c4 = run b0
  where
  b0 : Chain (Bx3-4012 ∷ []) (Bx3-4021 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx2-4013 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·4012⟩ c4) ▸
       at 1 1 (Bx2-4031 ∷ []) (lem-sym34-at0214203143 c4) ▸
       at 0 2 (Bx3-4021 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·4031⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym34 @0314213042: 5 steps
lem-sym34-at0314213042 : Complete 4 → ⟪ (Bx3-4102 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4120 ∷ []) ⟫ʷ
lem-sym34-at0314213042 c4 = run b0
  where
  b0 : Chain (Bx3-4102 ∷ []) (Bx3-4120 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-4012 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·4102⟩ c4) ▸
       at 1 1 (Bx3-4021 ∷ []) (lem-sym34-at0314203142 c4) ▸
       at 0 2 (Bx3-4120 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·4021⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- T312-beta @1221: 8 steps
lem-T312-beta-at1221 : Complete 4 → ⟪ (Toff312 ∷ Bx0-2134 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ CCZ124 ∷ []) ⟫ʷ
lem-T312-beta-at1221 c4 = run b0
  where
  b0 : Chain (Toff312 ∷ Bx0-2134 ∷ Toff312 ∷ []) (Bx0-2134 ∷ CCZ124 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff312 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff312 ∷ []) (Toff312 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-1234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2134⟩ c4) ▸
       at 3 2 (Toff312 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff312 ∷ []) (Toff312 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Bx0-1234 ∷ CCZ124 ∷ []) (lem-T312-beta c4) ▸
       at 0 2 (Bx0-2134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1234⟩ c4) ▸
       at 1 2 (CCZ124 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- T312-beta @132132: 8 steps
lem-T312-beta-at132132 : Complete 4 → ⟪ (Toff213 ∷ Bx0-3124 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3124 ∷ CCZ134 ∷ []) ⟫ʷ
lem-T312-beta-at132132 c4 = run b0
  where
  b0 : Chain (Toff213 ∷ Bx0-3124 ∷ Toff213 ∷ []) (Bx0-3124 ∷ CCZ134 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff312 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff213 ∷ []) (Toff312 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-2134 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3124⟩ c4) ▸
       at 3 2 (Toff312 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff213 ∷ []) (Toff312 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Bx0-2134 ∷ CCZ124 ∷ []) (lem-T312-beta-at1221 c4) ▸
       at 0 2 (Bx0-3124 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·2134⟩ c4) ▸
       at 1 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- T312-beta @14213243: 8 steps
lem-T312-beta-at14213243 : Complete 4 → ⟪ (Toff214 ∷ Bx0-4123 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4123 ∷ CCZ134 ∷ []) ⟫ʷ
lem-T312-beta-at14213243 c4 = run b0
  where
  b0 : Chain (Toff214 ∷ Bx0-4123 ∷ Toff214 ∷ []) (Bx0-4123 ∷ CCZ134 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff213 ∷ Sw34 ∷ []) (lem-nat-3-TOFF214 c4) ▸
       at 2 2 (Bx0-3124 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·4123⟩ c4) ▸
       at 3 2 (Toff213 ∷ Sw34 ∷ []) (lem-nat-3-TOFF214 c4) ▸
       at 1 3 (Bx0-3124 ∷ CCZ134 ∷ []) (lem-T312-beta-at132132 c4) ▸
       at 0 2 (Bx0-4123 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·3124⟩ c4) ▸
       at 1 2 (CCZ134 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ CCZ134 ∷ []) (CCZ134 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- T312-beta @0114203243: 8 steps
lem-T312-beta-at0114203243 : Complete 4 → ⟪ (Toff204 ∷ Bx1-4023 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-4023 ∷ CCZ034 ∷ []) ⟫ʷ
lem-T312-beta-at0114203243 c4 = run b0
  where
  b0 : Chain (Toff204 ∷ Bx1-4023 ∷ Toff204 ∷ []) (Bx1-4023 ∷ CCZ034 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff214 ∷ Sw01 ∷ []) (lem-nat-0-TOFF204 c4) ▸
       at 2 2 (Bx0-4123 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·4023⟩ c4) ▸
       at 3 2 (Toff214 ∷ Sw01 ∷ []) (lem-nat-0-TOFF204 c4) ▸
       at 1 3 (Bx0-4123 ∷ CCZ134 ∷ []) (lem-T312-beta-at14213243 c4) ▸
       at 0 2 (Bx1-4023 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·4123⟩ c4) ▸
       at 1 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- T312-beta @0214203143: 8 steps
lem-T312-beta-at0214203143 : Complete 4 → ⟪ (Toff104 ∷ Bx2-4013 ∷ Toff104 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4013 ∷ CCZ034 ∷ []) ⟫ʷ
lem-T312-beta-at0214203143 c4 = run b0
  where
  b0 : Chain (Toff104 ∷ Bx2-4013 ∷ Toff104 ∷ []) (Bx2-4013 ∷ CCZ034 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff204 ∷ Sw12 ∷ []) (lem-nat-1-TOFF104 c4) ▸
       at 2 2 (Bx1-4023 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·4013⟩ c4) ▸
       at 3 2 (Toff204 ∷ Sw12 ∷ []) (lem-nat-1-TOFF104 c4) ▸
       at 1 3 (Bx1-4023 ∷ CCZ034 ∷ []) (lem-T312-beta-at0114203243 c4) ▸
       at 0 2 (Bx2-4013 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·4023⟩ c4) ▸
       at 1 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- T312-beta @0314203142: 8 steps
lem-T312-beta-at0314203142 : Complete 4 → ⟪ (Toff104 ∷ Bx3-4012 ∷ Toff104 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4012 ∷ CCZ024 ∷ []) ⟫ʷ
lem-T312-beta-at0314203142 c4 = run b0
  where
  b0 : Chain (Toff104 ∷ Bx3-4012 ∷ Toff104 ∷ []) (Bx3-4012 ∷ CCZ024 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff104 ∷ Sw23 ∷ []) (lem-nat-2-TOFF104 c4) ▸
       at 2 2 (Bx2-4013 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·4012⟩ c4) ▸
       at 3 2 (Toff104 ∷ Sw23 ∷ []) (lem-nat-2-TOFF104 c4) ▸
       at 1 3 (Bx2-4013 ∷ CCZ034 ∷ []) (lem-T312-beta-at0214203143 c4) ▸
       at 0 2 (Bx3-4012 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·4013⟩ c4) ▸
       at 1 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- T312-beta @0314203241: 8 steps
lem-T312-beta-at0314203241 : Complete 4 → ⟪ (Toff204 ∷ Bx3-4021 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4021 ∷ CCZ014 ∷ []) ⟫ʷ
lem-T312-beta-at0314203241 c4 = run b0
  where
  b0 : Chain (Toff204 ∷ Bx3-4021 ∷ Toff204 ∷ []) (Bx3-4021 ∷ CCZ014 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff104 ∷ Sw12 ∷ []) (lem-nat-1-TOFF204 c4) ▸
       at 2 2 (Bx3-4012 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·4021⟩ c4) ▸
       at 3 2 (Toff104 ∷ Sw12 ∷ []) (lem-nat-1-TOFF204 c4) ▸
       at 1 3 (Bx3-4012 ∷ CCZ024 ∷ []) (lem-T312-beta-at0314203142 c4) ▸
       at 0 2 (Bx3-4021 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·4012⟩ c4) ▸
       at 1 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- T312-beta @0314213240: 8 steps
lem-T312-beta-at0314213240 : Complete 4 → ⟪ (Toff214 ∷ Bx3-4120 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4120 ∷ CCZ014 ∷ []) ⟫ʷ
lem-T312-beta-at0314213240 c4 = run b0
  where
  b0 : Chain (Toff214 ∷ Bx3-4120 ∷ Toff214 ∷ []) (Bx3-4120 ∷ CCZ014 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff204 ∷ Sw01 ∷ []) (lem-nat-0-TOFF214 c4) ▸
       at 2 2 (Bx3-4021 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·4120⟩ c4) ▸
       at 3 2 (Toff204 ∷ Sw01 ∷ []) (lem-nat-0-TOFF214 c4) ▸
       at 1 3 (Bx3-4021 ∷ CCZ014 ∷ []) (lem-T312-beta-at0314203241 c4) ▸
       at 0 2 (Bx3-4120 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·4021⟩ c4) ▸
       at 1 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym34 @0314203241: 5 steps
lem-sym34-at0314203241 : Complete 4 → ⟪ (Bx3-4021 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4012 ∷ []) ⟫ʷ
lem-sym34-at0314203241 c4 = run b0
  where
  b0 : Chain (Bx3-4021 ∷ []) (Bx3-4012 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-4012 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·4021⟩ c4) ▸
       at 1 1 (Bx3-4021 ∷ []) (lem-sym34-at0314203142 c4) ▸
       at 0 2 (Bx3-4012 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·4021⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym34 @0314213240: 5 steps
lem-sym34-at0314213240 : Complete 4 → ⟪ (Bx3-4120 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4102 ∷ []) ⟫ʷ
lem-sym34-at0314213240 c4 = run b0
  where
  b0 : Chain (Bx3-4120 ∷ []) (Bx3-4102 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-4021 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·4120⟩ c4) ▸
       at 1 1 (Bx3-4012 ∷ []) (lem-sym34-at0314203241 c4) ▸
       at 0 2 (Bx3-4102 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·4012⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym23 @1221: 5 steps
lem-sym23-at1221 : Complete 4 → ⟪ (Bx0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2314 ∷ []) ⟫ʷ
lem-sym23-at1221 c4 = run b0
  where
  b0 : Chain (Bx0-2134 ∷ []) (Bx0-2314 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2134⟩ c4) ▸
       at 1 1 (Bx0-1324 ∷ []) (lem-sym23 c4) ▸
       at 0 2 (Bx0-2314 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1324⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym23 @132132: 5 steps
lem-sym23-at132132 : Complete 4 → ⟪ (Bx0-3124 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3214 ∷ []) ⟫ʷ
lem-sym23-at132132 c4 = run b0
  where
  b0 : Chain (Bx0-3124 ∷ []) (Bx0-3214 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-2134 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3124⟩ c4) ▸
       at 1 1 (Bx0-2314 ∷ []) (lem-sym23-at1221 c4) ▸
       at 0 2 (Bx0-3214 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·2314⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym23 @14213243: 5 steps
lem-sym23-at14213243 : Complete 4 → ⟪ (Bx0-4123 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4213 ∷ []) ⟫ʷ
lem-sym23-at14213243 c4 = run b0
  where
  b0 : Chain (Bx0-4123 ∷ []) (Bx0-4213 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-3124 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·4123⟩ c4) ▸
       at 1 1 (Bx0-3214 ∷ []) (lem-sym23-at132132 c4) ▸
       at 0 2 (Bx0-4213 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·3214⟩ c4) ▸
       at 1 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym23 @0114203243: 5 steps
lem-sym23-at0114203243 : Complete 4 → ⟪ (Bx1-4023 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-4203 ∷ []) ⟫ʷ
lem-sym23-at0114203243 c4 = run b0
  where
  b0 : Chain (Bx1-4023 ∷ []) (Bx1-4203 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-4123 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·4023⟩ c4) ▸
       at 1 1 (Bx0-4213 ∷ []) (lem-sym23-at14213243 c4) ▸
       at 0 2 (Bx1-4203 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·4213⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym23 @0214203143: 5 steps
lem-sym23-at0214203143 : Complete 4 → ⟪ (Bx2-4013 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4103 ∷ []) ⟫ʷ
lem-sym23-at0214203143 c4 = run b0
  where
  b0 : Chain (Bx2-4013 ∷ []) (Bx2-4103 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-4023 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·4013⟩ c4) ▸
       at 1 1 (Bx1-4203 ∷ []) (lem-sym23-at0114203243 c4) ▸
       at 0 2 (Bx2-4103 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·4203⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym23 @0314203142: 5 steps
lem-sym23-at0314203142 : Complete 4 → ⟪ (Bx3-4012 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4102 ∷ []) ⟫ʷ
lem-sym23-at0314203142 c4 = run b0
  where
  b0 : Chain (Bx3-4012 ∷ []) (Bx3-4102 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx2-4013 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·4012⟩ c4) ▸
       at 1 1 (Bx2-4103 ∷ []) (lem-sym23-at0214203143 c4) ▸
       at 0 2 (Bx3-4102 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·4103⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym23 @0314213042: 5 steps
lem-sym23-at0314213042 : Complete 4 → ⟪ (Bx3-4102 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4012 ∷ []) ⟫ʷ
lem-sym23-at0314213042 c4 = run b0
  where
  b0 : Chain (Bx3-4102 ∷ []) (Bx3-4012 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-4012 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·4102⟩ c4) ▸
       at 1 1 (Bx3-4102 ∷ []) (lem-sym23-at0314203142 c4) ▸
       at 0 2 (Bx3-4012 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·4102⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym12 @1221: 5 steps
lem-sym12-at1221 : Complete 4 → ⟪ (Bx0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-sym12-at1221 c4 = run b0
  where
  b0 : Chain (Bx0-2134 ∷ []) (Bx0-1234 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2134⟩ c4) ▸
       at 1 1 (Bx0-2134 ∷ []) (lem-sym12 c4) ▸
       at 0 2 (Bx0-1234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2134⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym12 @132132: 5 steps
lem-sym12-at132132 : Complete 4 → ⟪ (Bx0-3124 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ []) ⟫ʷ
lem-sym12-at132132 c4 = run b0
  where
  b0 : Chain (Bx0-3124 ∷ []) (Bx0-1324 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-2134 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3124⟩ c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym12-at1221 c4) ▸
       at 0 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym12 @14213243: 5 steps
lem-sym12-at14213243 : Complete 4 → ⟪ (Bx0-4123 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ []) ⟫ʷ
lem-sym12-at14213243 c4 = run b0
  where
  b0 : Chain (Bx0-4123 ∷ []) (Bx0-1423 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-3124 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·4123⟩ c4) ▸
       at 1 1 (Bx0-1324 ∷ []) (lem-sym12-at132132 c4) ▸
       at 0 2 (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ c4) ▸
       at 1 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym12 @0114203243: 5 steps
lem-sym12-at0114203243 : Complete 4 → ⟪ (Bx1-4023 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0423 ∷ []) ⟫ʷ
lem-sym12-at0114203243 c4 = run b0
  where
  b0 : Chain (Bx1-4023 ∷ []) (Bx1-0423 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-4123 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·4023⟩ c4) ▸
       at 1 1 (Bx0-1423 ∷ []) (lem-sym12-at14213243 c4) ▸
       at 0 2 (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym12 @0214203143: 5 steps
lem-sym12-at0214203143 : Complete 4 → ⟪ (Bx2-4013 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ []) ⟫ʷ
lem-sym12-at0214203143 c4 = run b0
  where
  b0 : Chain (Bx2-4013 ∷ []) (Bx2-0413 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-4023 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·4013⟩ c4) ▸
       at 1 1 (Bx1-0423 ∷ []) (lem-sym12-at0114203243 c4) ▸
       at 0 2 (Bx2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0423⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym12 @0314203142: 5 steps
lem-sym12-at0314203142 : Complete 4 → ⟪ (Bx3-4012 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ []) ⟫ʷ
lem-sym12-at0314203142 c4 = run b0
  where
  b0 : Chain (Bx3-4012 ∷ []) (Bx3-0412 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx2-4013 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·4012⟩ c4) ▸
       at 1 1 (Bx2-0413 ∷ []) (lem-sym12-at0214203143 c4) ▸
       at 0 2 (Bx3-0412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0413⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- beta-inv @2332: 5 steps
lem-beta-inv-at2332 : Complete 4 → ⟪ (Bx0-1324 ∷ Bx0-1324 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-beta-inv-at2332 c4 = run b0
  where
  b0 : Chain (Bx0-1324 ∷ Bx0-1324 ∷ []) []
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ c4) ▸
       at 2 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ c4) ▸
       at 1 2 [] (lem-beta-inv c4) ▸
       at 0 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- beta-inv @243243: 5 steps
lem-beta-inv-at243243 : Complete 4 → ⟪ (Bx0-1423 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-beta-inv-at243243 c4 = run b0
  where
  b0 : Chain (Bx0-1423 ∷ Bx0-1423 ∷ []) []
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ c4) ▸
       at 2 2 (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ c4) ▸
       at 1 2 [] (lem-beta-inv-at2332 c4) ▸
       at 0 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- beta-inv @0110243243: 5 steps
lem-beta-inv-at0110243243 : Complete 4 → ⟪ (Bx1-0423 ∷ Bx1-0423 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-beta-inv-at0110243243 c4 = run b0
  where
  b0 : Chain (Bx1-0423 ∷ Bx1-0423 ∷ []) []
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ c4) ▸
       at 2 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ c4) ▸
       at 1 2 [] (lem-beta-inv-at243243 c4) ▸
       at 0 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- beta-inv @0210243143: 5 steps
lem-beta-inv-at0210243143 : Complete 4 → ⟪ (Bx2-0413 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-beta-inv-at0210243143 c4 = run b0
  where
  b0 : Chain (Bx2-0413 ∷ Bx2-0413 ∷ []) []
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ c4) ▸
       at 2 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ c4) ▸
       at 1 2 [] (lem-beta-inv-at0110243243 c4) ▸
       at 0 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- beta-inv @0310243142: 5 steps
lem-beta-inv-at0310243142 : Complete 4 → ⟪ (Bx3-0412 ∷ Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-beta-inv-at0310243142 c4 = run b0
  where
  b0 : Chain (Bx3-0412 ∷ Bx3-0412 ∷ []) []
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx2-0413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0412⟩ c4) ▸
       at 2 2 (Bx2-0413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0412⟩ c4) ▸
       at 1 2 [] (lem-beta-inv-at0210243143 c4) ▸
       at 0 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- beta-T @0214213043: 8 steps
lem-beta-T-at0214213043 : Complete 4 → ⟪ (Bx2-4103 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ []) ⟫ʷ
lem-beta-T-at0214213043 c4 = run b0
  where
  b0 : Chain (Bx2-4103 ∷ []) (Toff214 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx2-4013 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·4103⟩ c4) ▸
       at 1 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0214203143 c4) ▸
       at 0 2 (Toff214 ∷ Sw01 ∷ []) (lem-nat-0-TOFF204 c4) ▸
       at 1 2 (CCZ023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ123 ∷ []) (CCZ023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff214 ∷ Sw01 ∷ []) (lem-nat-0-TOFF204 c4) ▸
       at 3 2 (CCZ023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ123 ∷ []) (CCZ023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym23 @0214213043: 5 steps
lem-sym23-at0214213043 : Complete 4 → ⟪ (Bx2-4103 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4013 ∷ []) ⟫ʷ
lem-sym23-at0214213043 c4 = run b0
  where
  b0 : Chain (Bx2-4103 ∷ []) (Bx2-4013 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx2-4013 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·4103⟩ c4) ▸
       at 1 1 (Bx2-4103 ∷ []) (lem-sym23-at0214203143 c4) ▸
       at 0 2 (Bx2-4013 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·4103⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- F0-D: 15 steps
lem-F0-D : Complete 4 → ⟪ (CCZ014 ∷ Bx3-0412 ∷ Toff214 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ Toff214 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ []) ⟫ʷ
lem-F0-D c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ014 ∷ Bx3-0412 ∷ Toff214 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ Toff214 ∷ CCZ023 ∷ []) (CCZ014 ∷ Bx3-0412 ∷ Bx3-4012 ∷ CCZ014 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ [])
  b0 = at 4 1 (CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ []) (CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 6 0 (CCZ023 ∷ CCZ023 ∷ []) (lw4 c4 [] (CCZ023 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 3 4 (Bx3-4102 ∷ []) (sym (lem-beta-T-at0314213042 c4)) ▸
       at 3 1 (Bx3-4120 ∷ []) (lem-sym34-at0314213042 c4) ▸
       at 4 0 (Toff214 ∷ Toff214 ∷ []) (lw0 c4 [] (Toff214 ∷ Toff214 ∷ []) tt tt Eq.refl) ▸
       at 2 3 (Bx3-4120 ∷ CCZ014 ∷ []) (lem-T312-beta-at0314213240 c4) ▸
       at 2 1 (Bx3-4102 ∷ []) (lem-sym34-at0314213240 c4) ▸
       at 2 1 (Bx3-4012 ∷ []) (lem-sym23-at0314213042 c4) ▸ done

  b1 : Chain (CCZ014 ∷ Bx3-0412 ∷ Bx3-4012 ∷ CCZ014 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ []) (Bx2-0413 ∷ [])
  b1 = at 2 1 (Bx3-0412 ∷ []) (lem-sym12-at0314203142 c4) ▸
       at 1 2 [] (lem-beta-inv-at0310243142 c4) ▸
       at 0 2 [] (pw2 c4 (CCZ014 ∷ CCZ014 ∷ []) [] tt tt Eq.refl) ▸
       at 1 1 (CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ []) (CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx2-4103 ∷ []) (sym (lem-beta-T-at0214213043 c4)) ▸
       at 0 1 (Bx2-4013 ∷ []) (lem-sym23-at0214213043 c4) ▸
       at 0 1 (Bx2-0413 ∷ []) (lem-sym12-at0214203143 c4) ▸ done


-- sym34 @0110: 5 steps
lem-sym34-at0110 : Complete 4 → ⟪ (Bx1-0234 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0243 ∷ []) ⟫ʷ
lem-sym34-at0110 c4 = run b0
  where
  b0 : Chain (Bx1-0234 ∷ []) (Bx1-0243 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0234⟩ c4) ▸
       at 1 1 (Bx0-1243 ∷ []) (lem-sym34 c4) ▸
       at 0 2 (Bx1-0243 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1243⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym34 @021021: 5 steps
lem-sym34-at021021 : Complete 4 → ⟪ (Bx2-0134 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0143 ∷ []) ⟫ʷ
lem-sym34-at021021 c4 = run b0
  where
  b0 : Chain (Bx2-0134 ∷ []) (Bx2-0143 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-0234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0134⟩ c4) ▸
       at 1 1 (Bx1-0243 ∷ []) (lem-sym34-at0110 c4) ▸
       at 0 2 (Bx2-0143 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0243⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym34 @03102132: 5 steps
lem-sym34-at03102132 : Complete 4 → ⟪ (Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0142 ∷ []) ⟫ʷ
lem-sym34-at03102132 c4 = run b0
  where
  b0 : Chain (Bx3-0124 ∷ []) (Bx3-0142 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx2-0134 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0124⟩ c4) ▸
       at 1 1 (Bx2-0143 ∷ []) (lem-sym34-at021021 c4) ▸
       at 0 2 (Bx3-0142 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0143⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- c124-beta @3443: 7 steps
lem-c124-beta-at3443 : Complete 4 → ⟪ (CCZ123 ∷ Bx0-1243 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1243 ∷ CCZ123 ∷ []) ⟫ʷ
lem-c124-beta-at3443 c4 = run b0
  where
  b0 : Chain (CCZ123 ∷ Bx0-1243 ∷ []) (Bx0-1243 ∷ CCZ123 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ124 ∷ Sw34 ∷ []) (lem-nat-3-CCZ123 c4) ▸
       at 2 2 (Bx0-1234 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1243⟩ c4) ▸
       at 1 2 (Bx0-1234 ∷ CCZ124 ∷ []) (lem-c124-beta c4) ▸
       at 0 2 (Bx0-1243 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1234⟩ c4) ▸
       at 1 2 (CCZ123 ∷ Sw34 ∷ []) (lem-nat-3-CCZ124 c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done

