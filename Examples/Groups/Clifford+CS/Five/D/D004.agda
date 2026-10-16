{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D004 where

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
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-BOXd-BOX ; lem-CS20-beta-c ; lem-K0-pass ; lem-beta-T ; lem-sym12 ; lem-sym23)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-auto-CCZ012-∣-CCZ314-at2332 ; lem-sym12-at1221 ; lem-sym23-at1221)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-CZ10-beta-c-at1221 ; lem-T312-beta-at01122330 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ034-at0110243243 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ103 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ342 ; lem-auto-BOX⟨0·1234⟩-∣-TOFF012 ; lem-beta-T-at0110243243 ; lem-beta-T-at122331 ; lem-sym12-at0110 ; lem-sym12-at0112203443 ; lem-sym23-at0110243243 ; lem-sym23-at01103443 ; lem-sym23-at011220 ; lem-sym23-at01122330 ; lem-sym23-at122331 ; lem-sym34-at01103443 ; lem-sym34-at011220 ; lem-sym34-at2332 ; lem-sym34-at3443)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-1-BOX⟨0·2134⟩ ; lem-nat-1-CCZ024 ; lem-nat-2-BOX⟨0·1234⟩ ; lem-nat-2-BOX⟨0·1324⟩ ; lem-nat-2-CCZ012 ; lem-nat-2-CCZ013 ; lem-nat-2-TOFF012 ; lem-nat-2-TOFF013 ; lem-nat-3-BOX⟨0·1423⟩ ; lem-nat-3-CCZ014 ; lem-nat-3-TOFF013 ; lem-nat-3-TOFF014)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-1-CCZ014 ; lem-nat-2-TOFF201 ; lem-nat-3-BOX⟨0·1324⟩ ; lem-nat-3-CCZ013)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-1-TOFF301 ; lem-nat-2-CCZ124 ; lem-nat-2-CCZ134)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-0-TOFF014 ; lem-nat-0-TOFF104)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-0-CCZ034)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-1-BOX⟨0·1234⟩ ; lem-nat-2-BOX⟨0·2134⟩ ; lem-nat-3-BOX⟨0·3124⟩)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-nat-0-BOX⟨0·4123⟩ ; lem-nat-1-BOX⟨1·4023⟩)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-0-BOX⟨0·1423⟩ ; lem-nat-1-BOX⟨0·1324⟩ ; lem-nat-1-BOX⟨1·0423⟩ ; lem-nat-2-CZ03)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-nat-0-BOX⟨0·1234⟩ ; lem-nat-0-BOX⟨1·0234⟩ ; lem-nat-0-BOX⟨1·0423⟩ ; lem-nat-1-BOX⟨1·0243⟩ ; lem-nat-1-BOX⟨2·0134⟩ ; lem-nat-1-BOX⟨2·0413⟩ ; lem-nat-1-BOX⟨3·0214⟩ ; lem-nat-2-BOX⟨2·0314⟩ ; lem-nat-2-BOX⟨3·0124⟩ ; lem-nat-2-CZ02 ; lem-nat-3-CCZ123 ; lem-nat-3-CCZ124)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-nat-1-BOX⟨0·2314⟩ ; lem-nat-1-CZ01 ; lem-nat-1-CZ02 ; lem-nat-2-BOX⟨0·1342⟩ ; lem-nat-3-CZ03 ; lem-nat-3-CZ04)
open import Examples.Groups.Clifford+CS.Five.D.R012 using (lem-nat-0-BOXd⟨1·0423⟩ ; lem-nat-1-BOX⟨0·1342⟩ ; lem-nat-1-BOX⟨0·2341⟩ ; lem-nat-1-CS01 ; lem-nat-1-CS02 ; lem-nat-2-BOXd⟨0·1324⟩ ; lem-nat-3-BOXd⟨0·1423⟩)
open import Examples.Groups.Clifford+CS.Five.D.R013 using (lem-nat-0-BOX⟨0·1324⟩ ; lem-nat-0-BOX⟨3·0214⟩ ; lem-nat-0-BOX⟨3·1024⟩ ; lem-nat-0-BOXd⟨1·4023⟩ ; lem-nat-1-BOX⟨1·0324⟩ ; lem-nat-1-BOX⟨1·2034⟩ ; lem-nat-1-BOXd⟨0·2134⟩ ; lem-nat-1-BOXd⟨2·0413⟩ ; lem-nat-1-BOXd⟨2·4013⟩ ; lem-nat-2-BOX⟨2·1034⟩ ; lem-nat-2-BOXd⟨0·3124⟩ ; lem-nat-3-BOXd⟨0·4123⟩)
-- auto CCZ012 | CCZ314 @243243: 7 steps
lem-auto-CCZ012-∣-CCZ314-at243243 : Complete 4 → ⟪ (CCZ014 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CCZ014 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-CCZ314-at243243 c4 = run b0
  where
  b0 : Chain (CCZ014 ∷ CCZ123 ∷ []) (CCZ123 ∷ CCZ014 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4) ▸
       at 2 2 (CCZ124 ∷ Sw34 ∷ []) (lem-nat-3-CCZ123 c4) ▸
       at 1 2 (CCZ124 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-CCZ314-at2332 c4) ▸
       at 0 2 (CCZ123 ∷ Sw34 ∷ []) (lem-nat-3-CCZ124 c4) ▸
       at 1 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | CCZ314 @12243143: 7 steps
lem-auto-CCZ012-∣-CCZ314-at12243143 : Complete 4 → ⟪ (CCZ024 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CCZ024 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-CCZ314-at12243143 c4 = run b0
  where
  b0 : Chain (CCZ024 ∷ CCZ123 ∷ []) (CCZ123 ∷ CCZ024 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 2 2 (CCZ123 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ123 ∷ CCZ014 ∷ []) (lem-auto-CCZ012-∣-CCZ314-at243243 c4) ▸
       at 0 2 (CCZ123 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ342 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ342-at2332 : Complete 4 → ⟪ (Bx0-1324 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ342-at2332 c4 = run b0
  where
  b0 : Chain (Bx0-1324 ∷ CCZ234 ∷ []) (CCZ234 ∷ Bx0-1324 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ c4) ▸
       at 2 2 (CCZ234 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ234 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ342 c4) ▸
       at 0 2 (CCZ234 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ342 @243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ342-at243243 : Complete 4 → ⟪ (Bx0-1423 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Bx0-1423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ342-at243243 c4 = run b0
  where
  b0 : Chain (Bx0-1423 ∷ CCZ234 ∷ []) (CCZ234 ∷ Bx0-1423 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ c4) ▸
       at 2 2 (CCZ234 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ234 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ342-at2332 c4) ▸
       at 0 2 (CCZ234 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ342 @0110243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ342-at0110243243 : Complete 4 → ⟪ (Bx1-0423 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Bx1-0423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ342-at0110243243 c4 = run b0
  where
  b0 : Chain (Bx1-0423 ∷ CCZ234 ∷ []) (CCZ234 ∷ Bx1-0423 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ c4) ▸
       at 2 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 1 2 (CCZ234 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ342-at243243 c4) ▸
       at 0 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 1 2 (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | TOFF012 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-TOFF012-at2332 : Complete 4 → ⟪ (Bx0-1324 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-TOFF012-at2332 c4 = run b0
  where
  b0 : Chain (Bx0-1324 ∷ Toff013 ∷ []) (Toff013 ∷ Bx0-1324 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ c4) ▸
       at 2 2 (Toff012 ∷ Sw23 ∷ []) (lem-nat-2-TOFF013 c4) ▸
       at 1 2 (Toff012 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-TOFF012 c4) ▸
       at 0 2 (Toff013 ∷ Sw23 ∷ []) (lem-nat-2-TOFF012 c4) ▸
       at 1 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | TOFF012 @243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-TOFF012-at243243 : Complete 4 → ⟪ (Bx0-1423 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ Bx0-1423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-TOFF012-at243243 c4 = run b0
  where
  b0 : Chain (Bx0-1423 ∷ Toff014 ∷ []) (Toff014 ∷ Bx0-1423 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ c4) ▸
       at 2 2 (Toff013 ∷ Sw34 ∷ []) (lem-nat-3-TOFF014 c4) ▸
       at 1 2 (Toff013 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-TOFF012-at2332 c4) ▸
       at 0 2 (Toff014 ∷ Sw34 ∷ []) (lem-nat-3-TOFF013 c4) ▸
       at 1 2 (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | TOFF012 @0110243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-TOFF012-at0110243243 : Complete 4 → ⟪ (Bx1-0423 ∷ Toff104 ∷ []) ⟫ʷ ≈ ⟪ (Toff104 ∷ Bx1-0423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-TOFF012-at0110243243 c4 = run b0
  where
  b0 : Chain (Bx1-0423 ∷ Toff104 ∷ []) (Toff104 ∷ Bx1-0423 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ c4) ▸
       at 2 2 (Toff014 ∷ Sw01 ∷ []) (lem-nat-0-TOFF104 c4) ▸
       at 1 2 (Toff014 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-TOFF012-at243243 c4) ▸
       at 0 2 (Toff104 ∷ Sw01 ∷ []) (lem-nat-0-TOFF014 c4) ▸
       at 1 2 (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ103 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ103-at2332 : Complete 4 → ⟪ (Bx0-1324 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ103-at2332 c4 = run b0
  where
  b0 : Chain (Bx0-1324 ∷ CCZ012 ∷ []) (CCZ012 ∷ Bx0-1324 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ c4) ▸
       at 2 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 1 2 (CCZ013 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ103 c4) ▸
       at 0 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 1 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ103 @243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ103-at243243 : Complete 4 → ⟪ (Bx0-1423 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Bx0-1423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ103-at243243 c4 = run b0
  where
  b0 : Chain (Bx0-1423 ∷ CCZ012 ∷ []) (CCZ012 ∷ Bx0-1423 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ c4) ▸
       at 2 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 1 2 (CCZ012 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ103-at2332 c4) ▸
       at 0 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 1 2 (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ103 @0110243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ103-at0110243243 : Complete 4 → ⟪ (Bx1-0423 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Bx1-0423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ103-at0110243243 c4 = run b0
  where
  b0 : Chain (Bx1-0423 ∷ CCZ012 ∷ []) (CCZ012 ∷ Bx1-0423 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ c4) ▸
       at 2 2 (CCZ012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ103-at243243 c4) ▸
       at 0 2 (CCZ012 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- K0-pass @0110: 7 steps
lem-K0-pass-at0110 : Complete 4 → ⟪ (K1 ∷ Bx1-0234 ∷ K1⁻ ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0234 ∷ []) ⟫ʷ
lem-K0-pass-at0110 c4 = run b0
  where
  b0 : Chain (K1 ∷ Bx1-0234 ∷ K1⁻ ∷ []) (Bx1-0234 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (K0 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ K1 ∷ []) (K0 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-1234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0234⟩ c4) ▸
       at 3 2 (K0⁻ ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ K1⁻ ∷ []) (K0⁻ ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Bx0-1234 ∷ []) (lem-K0-pass c4) ▸
       at 0 2 (Bx1-0234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1234⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- TW: 54 steps
lem-TW : Complete 4 → ⟪ (Toff102 ∷ Bx0-1234 ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ Bx1-0234 ∷ []) ⟫ʷ
lem-TW c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (run b6))))))
  where
  b0 : Chain (Toff102 ∷ Bx0-1234 ∷ Toff102 ∷ []) (K1 ∷ CCZ012 ∷ Toff023 ∷ Toff104 ∷ Toff023 ∷ K1⁻ ∷ CCZ014 ∷ K1 ∷ CCZ012 ∷ K1⁻ ∷ [])
  b0 = at 0 1 (K1 ∷ CCZ012 ∷ K1⁻ ∷ []) (lw4 c4 (Toff102 ∷ []) (K1 ∷ CCZ012 ∷ K1⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 1 (K1 ∷ CCZ012 ∷ K1⁻ ∷ []) (lw4 c4 (Toff102 ∷ []) (K1 ∷ CCZ012 ∷ K1⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Bx0-2134 ∷ []) (lem-sym12 c4) ▸
       at 3 1 (Bx0-2314 ∷ []) (lem-sym23-at1221 c4) ▸
       at 3 1 (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ []) (lem-beta-T-at122331 c4) ▸
       at 2 2 (Toff023 ∷ K1⁻ ∷ []) (lw4 c4 (K1⁻ ∷ Toff023 ∷ []) (Toff023 ∷ K1⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff104 ∷ K1⁻ ∷ []) (pw2 c4 (K1⁻ ∷ CCZ014 ∷ []) (Toff104 ∷ K1⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff023 ∷ K1⁻ ∷ []) (lw4 c4 (K1⁻ ∷ Toff023 ∷ []) (Toff023 ∷ K1⁻ ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (K1 ∷ CCZ012 ∷ Toff023 ∷ Toff104 ∷ Toff023 ∷ K1⁻ ∷ CCZ014 ∷ K1 ∷ CCZ012 ∷ K1⁻ ∷ []) (K1 ∷ Toff023 ∷ Toff104 ∷ CCZ012 ∷ CCZ024 ∷ Bx1-0423 ∷ Toff023 ∷ CCZ123 ∷ Toff104 ∷ CCZ012 ∷ K1⁻ ∷ [])
  b1 = at 5 2 (Toff104 ∷ K1⁻ ∷ []) (pw2 c4 (K1⁻ ∷ CCZ014 ∷ []) (Toff104 ∷ K1⁻ ∷ []) tt tt Eq.refl) ▸
       at 6 2 [] (lw4 c4 (K1⁻ ∷ K1 ∷ []) [] tt tt Eq.refl) ▸
       at 1 2 (Toff023 ∷ CCZ012 ∷ CCZ123 ∷ []) (lw4 c4 (CCZ012 ∷ Toff023 ∷ []) (Toff023 ∷ CCZ012 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 3 0 (Toff104 ∷ Toff104 ∷ []) (pw2 c4 [] (Toff104 ∷ Toff104 ∷ []) tt tt Eq.refl) ▸
       at 7 0 (CCZ123 ∷ CCZ123 ∷ []) (lw4 c4 [] (CCZ123 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 4 4 (Bx1-0423 ∷ []) (sym (lem-beta-T-at0110243243 c4)) ▸
       at 2 2 (Toff104 ∷ CCZ012 ∷ CCZ024 ∷ []) (pw3 c4 (CCZ012 ∷ Toff104 ∷ []) (Toff104 ∷ CCZ012 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Toff023 ∷ CCZ123 ∷ []) (lw4 c4 (CCZ123 ∷ Toff023 ∷ []) (Toff023 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (K1 ∷ Toff023 ∷ Toff104 ∷ CCZ012 ∷ CCZ024 ∷ Bx1-0423 ∷ Toff023 ∷ CCZ123 ∷ Toff104 ∷ CCZ012 ∷ K1⁻ ∷ []) (K1 ∷ Toff023 ∷ Toff104 ∷ CCZ012 ∷ CCZ024 ∷ Toff023 ∷ Bx1-2043 ∷ CCZ234 ∷ CCZ123 ∷ Toff104 ∷ CCZ012 ∷ K1⁻ ∷ [])
  b2 = at 5 0 (Toff023 ∷ Toff023 ∷ []) (lw4 c4 [] (Toff023 ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
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
       at 4 2 (Toff023 ∷ CCZ024 ∷ CCZ234 ∷ []) (pw1 c4 (CCZ024 ∷ Toff023 ∷ []) (Toff023 ∷ CCZ024 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff023 ∷ CCZ012 ∷ CCZ123 ∷ []) (lw4 c4 (CCZ012 ∷ Toff023 ∷ []) (Toff023 ∷ CCZ012 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ123 ∷ CCZ234 ∷ []) (lw0 c4 (CCZ234 ∷ CCZ123 ∷ []) (CCZ123 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ123 ∷ Bx1-0423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ034-at0110243243 c4) ▸
       at 7 2 (CCZ123 ∷ CCZ234 ∷ []) (lw0 c4 (CCZ234 ∷ CCZ123 ∷ []) (CCZ123 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ123 ∷ CCZ024 ∷ []) (lem-auto-CCZ012-∣-CCZ314-at12243143 c4) ▸ done

  b4 : Chain (K1 ∷ Toff023 ∷ Toff104 ∷ Toff023 ∷ CCZ012 ∷ CCZ123 ∷ CCZ123 ∷ CCZ024 ∷ CCZ234 ∷ Bx1-0423 ∷ CCZ234 ∷ Toff104 ∷ CCZ012 ∷ K1⁻ ∷ []) (K1 ∷ Toff023 ∷ Toff104 ∷ Toff023 ∷ Toff104 ∷ CCZ012 ∷ CCZ024 ∷ CCZ012 ∷ CCZ024 ∷ Bx1-0423 ∷ K1⁻ ∷ [])
  b4 = at 5 2 [] (lw4 c4 (CCZ123 ∷ CCZ123 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 (CCZ234 ∷ Bx1-0423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ342-at0110243243 c4) ▸
       at 6 2 [] (lw0 c4 (CCZ234 ∷ CCZ234 ∷ []) [] tt tt Eq.refl) ▸
       at 6 2 (Toff104 ∷ Bx1-0423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-TOFF012-at0110243243 c4) ▸
       at 5 2 (Toff104 ∷ CCZ024 ∷ []) (pw3 c4 (CCZ024 ∷ Toff104 ∷ []) (Toff104 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff104 ∷ CCZ012 ∷ CCZ024 ∷ []) (pw3 c4 (CCZ012 ∷ Toff104 ∷ []) (Toff104 ∷ CCZ012 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ012 ∷ Bx1-0423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ103-at0110243243 c4) ▸
       at 7 2 (CCZ012 ∷ CCZ024 ∷ []) (pw3 c4 (CCZ024 ∷ CCZ012 ∷ []) (CCZ012 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸ done

  b5 : Chain (K1 ∷ Toff023 ∷ Toff104 ∷ Toff023 ∷ Toff104 ∷ CCZ012 ∷ CCZ024 ∷ CCZ012 ∷ CCZ024 ∷ Bx1-0423 ∷ K1⁻ ∷ []) (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ K1 ∷ Bx1-0423 ∷ K1⁻ ∷ [])
  b5 = at 6 2 (CCZ012 ∷ CCZ024 ∷ []) (pw3 c4 (CCZ024 ∷ CCZ012 ∷ []) (CCZ012 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 5 2 [] (lw4 c4 (CCZ012 ∷ CCZ012 ∷ []) [] tt tt Eq.refl) ▸
       at 5 2 [] (pw1 c4 (CCZ024 ∷ CCZ024 ∷ []) [] tt tt Eq.refl) ▸
       at 5 0 (K1⁻ ∷ K1 ∷ []) (lw4 c4 [] (K1⁻ ∷ K1 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Toff023 ∷ K1 ∷ []) (lw4 c4 (K1 ∷ Toff023 ∷ []) (Toff023 ∷ K1 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ014 ∷ K1 ∷ []) (pw2 c4 (K1 ∷ Toff104 ∷ []) (CCZ014 ∷ K1 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff023 ∷ K1 ∷ []) (lw4 c4 (K1 ∷ Toff023 ∷ []) (Toff023 ∷ K1 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CCZ014 ∷ []) (pw2 c4 (K1 ∷ Toff104 ∷ K1⁻ ∷ []) (CCZ014 ∷ []) tt tt Eq.refl) ▸ done

  b6 : Chain (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ K1 ∷ Bx1-0423 ∷ K1⁻ ∷ []) (Bx0-1234 ∷ Bx1-0234 ∷ [])
  b6 = at 0 4 (Bx0-2314 ∷ []) (sym (lem-beta-T-at122331 c4)) ▸
       at 0 1 (Bx0-2134 ∷ []) (lem-sym23-at122331 c4) ▸
       at 0 1 (Bx0-1234 ∷ []) (lem-sym12-at1221 c4) ▸
       at 2 1 (Bx1-0243 ∷ []) (lem-sym23-at0110243243 c4) ▸
       at 2 1 (Bx1-0234 ∷ []) (lem-sym34-at01103443 c4) ▸
       at 1 3 (Bx1-0234 ∷ []) (lem-K0-pass-at0110 c4) ▸ done


-- auto CZ01 | CCZ234: 1 steps
lem-auto-CZ01-∣-CCZ234 : Complete 4 → ⟪ (CZ01 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ CZ01 ∷ []) ⟫ʷ
lem-auto-CZ01-∣-CCZ234 c4 = run b0
  where
  b0 : Chain (CZ01 ∷ CCZ234 ∷ []) (CCZ234 ∷ CZ01 ∷ [])
  b0 = at 0 2 (CCZ234 ∷ CZ01 ∷ []) (c₂ (CZ) (CCZ)) ▸ done


-- auto BOX(0;1234) | CZ10: 5 steps
lem-auto-BOX⟨0·1234⟩-∣-CZ10 : Complete 4 → ⟪ (Bx0-1234 ∷ CZ01 ∷ []) ⟫ʷ ≈ ⟪ (CZ01 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CZ10 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ CZ01 ∷ []) (CZ01 ∷ Bx0-1234 ∷ [])
  b0 = at 1 1 (CZ01 ∷ []) (lw4 c4 (CZ01 ∷ []) (CZ01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx0-2134 ∷ []) (lem-sym12 c4) ▸
       at 0 2 (CZ01 ∷ Bx0-2134 ∷ []) (sym (lem-CZ10-beta-c-at1221 c4)) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym12-at1221 c4) ▸
       at 0 1 (CZ01 ∷ []) (lw4 c4 (CZ01 ∷ []) (CZ01 ∷ []) tt tt Eq.refl) ▸ done


-- auto CZ01 | CCZ234 @1221: 7 steps
lem-auto-CZ01-∣-CCZ234-at1221 : Complete 4 → ⟪ (CZ02 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ CZ02 ∷ []) ⟫ʷ
lem-auto-CZ01-∣-CCZ234-at1221 c4 = run b0
  where
  b0 : Chain (CZ02 ∷ CCZ134 ∷ []) (CCZ134 ∷ CZ02 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CZ01 ∷ Sw12 ∷ []) (lem-nat-1-CZ02 c4) ▸
       at 2 2 (CCZ234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ134 ∷ []) (CCZ234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ234 ∷ CZ01 ∷ []) (lem-auto-CZ01-∣-CCZ234 c4) ▸
       at 0 2 (CCZ134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ234 ∷ []) (CCZ134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CZ02 ∷ Sw12 ∷ []) (lem-nat-1-CZ01 c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CZ01 | CCZ234 @132132: 7 steps
lem-auto-CZ01-∣-CCZ234-at132132 : Complete 4 → ⟪ (CZ03 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ CZ03 ∷ []) ⟫ʷ
lem-auto-CZ01-∣-CCZ234-at132132 c4 = run b0
  where
  b0 : Chain (CZ03 ∷ CCZ124 ∷ []) (CCZ124 ∷ CZ03 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CZ02 ∷ Sw23 ∷ []) (lem-nat-2-CZ03 c4) ▸
       at 2 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 1 2 (CCZ134 ∷ CZ02 ∷ []) (lem-auto-CZ01-∣-CCZ234-at1221 c4) ▸
       at 0 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 1 2 (CZ03 ∷ Sw23 ∷ []) (lem-nat-2-CZ02 c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CZ01 | CCZ234 @14213243: 7 steps
lem-auto-CZ01-∣-CCZ234-at14213243 : Complete 4 → ⟪ (CZ04 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CZ04 ∷ []) ⟫ʷ
lem-auto-CZ01-∣-CCZ234-at14213243 c4 = run b0
  where
  b0 : Chain (CZ04 ∷ CCZ123 ∷ []) (CCZ123 ∷ CZ04 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CZ03 ∷ Sw34 ∷ []) (lem-nat-3-CZ04 c4) ▸
       at 2 2 (CCZ124 ∷ Sw34 ∷ []) (lem-nat-3-CCZ123 c4) ▸
       at 1 2 (CCZ124 ∷ CZ03 ∷ []) (lem-auto-CZ01-∣-CCZ234-at132132 c4) ▸
       at 0 2 (CCZ123 ∷ Sw34 ∷ []) (lem-nat-3-CCZ124 c4) ▸
       at 1 2 (CZ04 ∷ Sw34 ∷ []) (lem-nat-3-CZ03 c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CZ10 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CZ10-at2332 : Complete 4 → ⟪ (Bx0-1324 ∷ CZ01 ∷ []) ⟫ʷ ≈ ⟪ (CZ01 ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CZ10-at2332 c4 = run b0
  where
  b0 : Chain (Bx0-1324 ∷ CZ01 ∷ []) (CZ01 ∷ Bx0-1324 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ c4) ▸
       at 2 2 (CZ01 ∷ Sw23 ∷ []) (sym (c₂ (CZ) (Swap))) ▸
       at 1 2 (CZ01 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CZ10 c4) ▸
       at 0 2 (CZ01 ∷ Sw23 ∷ []) (sym (c₂ (CZ) (Swap))) ▸
       at 1 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CZ10 @243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CZ10-at243243 : Complete 4 → ⟪ (Bx0-1423 ∷ CZ01 ∷ []) ⟫ʷ ≈ ⟪ (CZ01 ∷ Bx0-1423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CZ10-at243243 c4 = run b0
  where
  b0 : Chain (Bx0-1423 ∷ CZ01 ∷ []) (CZ01 ∷ Bx0-1423 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ c4) ▸
       at 2 2 (CZ01 ∷ Sw34 ∷ []) (sym (c₂ (CZ) (Swap ↑))) ▸
       at 1 2 (CZ01 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CZ10-at2332 c4) ▸
       at 0 2 (CZ01 ∷ Sw34 ∷ []) (sym (c₂ (CZ) (Swap ↑))) ▸
       at 1 2 (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CZ10 @0110243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CZ10-at0110243243 : Complete 4 → ⟪ (Bx1-0423 ∷ CZ01 ∷ []) ⟫ʷ ≈ ⟪ (CZ01 ∷ Bx1-0423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CZ10-at0110243243 c4 = run b0
  where
  b0 : Chain (Bx1-0423 ∷ CZ01 ∷ []) (CZ01 ∷ Bx1-0423 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ c4) ▸
       at 2 2 (CZ01 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CZ01 ∷ []) (CZ01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CZ01 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CZ10-at243243 c4) ▸
       at 0 2 (CZ01 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CZ01 ∷ []) (CZ01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- CW: 52 steps
lem-CW : Complete 4 → ⟪ (CX01 ∷ Bx0-1234 ∷ CX01 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ Bx1-0234 ∷ []) ⟫ʷ
lem-CW c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (run b6))))))
  where
  b0 : Chain (CX01 ∷ Bx0-1234 ∷ CX01 ∷ []) (K1 ∷ CZ01 ∷ Toff023 ∷ Toff104 ∷ Toff023 ∷ K1⁻ ∷ CCZ014 ∷ K1 ∷ CZ01 ∷ K1⁻ ∷ [])
  b0 = at 0 1 (K1 ∷ CZ01 ∷ K1⁻ ∷ []) (lw4 c4 (CX01 ∷ []) (K1 ∷ CZ01 ∷ K1⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 1 (K1 ∷ CZ01 ∷ K1⁻ ∷ []) (lw4 c4 (CX01 ∷ []) (K1 ∷ CZ01 ∷ K1⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Bx0-2134 ∷ []) (lem-sym12 c4) ▸
       at 3 1 (Bx0-2314 ∷ []) (lem-sym23-at1221 c4) ▸
       at 3 1 (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ []) (lem-beta-T-at122331 c4) ▸
       at 2 2 (Toff023 ∷ K1⁻ ∷ []) (lw4 c4 (K1⁻ ∷ Toff023 ∷ []) (Toff023 ∷ K1⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff104 ∷ K1⁻ ∷ []) (pw2 c4 (K1⁻ ∷ CCZ014 ∷ []) (Toff104 ∷ K1⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff023 ∷ K1⁻ ∷ []) (lw4 c4 (K1⁻ ∷ Toff023 ∷ []) (Toff023 ∷ K1⁻ ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (K1 ∷ CZ01 ∷ Toff023 ∷ Toff104 ∷ Toff023 ∷ K1⁻ ∷ CCZ014 ∷ K1 ∷ CZ01 ∷ K1⁻ ∷ []) (K1 ∷ Toff023 ∷ Toff104 ∷ CZ01 ∷ CZ04 ∷ Bx1-0423 ∷ Toff023 ∷ CCZ123 ∷ Toff104 ∷ CZ01 ∷ K1⁻ ∷ [])
  b1 = at 5 2 (Toff104 ∷ K1⁻ ∷ []) (pw2 c4 (K1⁻ ∷ CCZ014 ∷ []) (Toff104 ∷ K1⁻ ∷ []) tt tt Eq.refl) ▸
       at 6 2 [] (lw4 c4 (K1⁻ ∷ K1 ∷ []) [] tt tt Eq.refl) ▸
       at 1 2 (Toff023 ∷ CZ01 ∷ CCZ123 ∷ []) (lw4 c4 (CZ01 ∷ Toff023 ∷ []) (Toff023 ∷ CZ01 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 3 0 (Toff104 ∷ Toff104 ∷ []) (pw2 c4 [] (Toff104 ∷ Toff104 ∷ []) tt tt Eq.refl) ▸
       at 7 0 (CCZ123 ∷ CCZ123 ∷ []) (lw4 c4 [] (CCZ123 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 4 4 (Bx1-0423 ∷ []) (sym (lem-beta-T-at0110243243 c4)) ▸
       at 2 2 (Toff104 ∷ CZ01 ∷ CZ04 ∷ []) (pw2 c4 (CZ01 ∷ Toff104 ∷ []) (Toff104 ∷ CZ01 ∷ CZ04 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Toff023 ∷ CCZ123 ∷ []) (lw4 c4 (CCZ123 ∷ Toff023 ∷ []) (Toff023 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (K1 ∷ Toff023 ∷ Toff104 ∷ CZ01 ∷ CZ04 ∷ Bx1-0423 ∷ Toff023 ∷ CCZ123 ∷ Toff104 ∷ CZ01 ∷ K1⁻ ∷ []) (K1 ∷ Toff023 ∷ Toff104 ∷ CZ01 ∷ CZ04 ∷ Toff023 ∷ Bx1-2043 ∷ CCZ234 ∷ CCZ123 ∷ Toff104 ∷ CZ01 ∷ K1⁻ ∷ [])
  b2 = at 5 0 (Toff023 ∷ Toff023 ∷ []) (lw4 c4 [] (Toff023 ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (Bx1-0243 ∷ []) (lem-sym23-at0110243243 c4) ▸
       at 7 1 (Bx1-0234 ∷ []) (lem-sym34-at01103443 c4) ▸
       at 7 1 (Bx1-2034 ∷ []) (lem-sym12-at0110 c4) ▸
       at 7 1 (Bx1-2304 ∷ []) (lem-sym23-at011220 c4) ▸
       at 6 3 (Bx1-2304 ∷ CCZ234 ∷ []) (lem-T312-beta-at01122330 c4) ▸
       at 6 1 (Bx1-2034 ∷ []) (lem-sym23-at01122330 c4) ▸
       at 6 1 (Bx1-2043 ∷ []) (lem-sym34-at011220 c4) ▸ done

  b3 : Chain (K1 ∷ Toff023 ∷ Toff104 ∷ CZ01 ∷ CZ04 ∷ Toff023 ∷ Bx1-2043 ∷ CCZ234 ∷ CCZ123 ∷ Toff104 ∷ CZ01 ∷ K1⁻ ∷ []) (K1 ∷ Toff023 ∷ Toff104 ∷ Toff023 ∷ CZ01 ∷ CCZ123 ∷ CCZ123 ∷ CZ04 ∷ CCZ234 ∷ Bx1-0423 ∷ CCZ234 ∷ Toff104 ∷ CZ01 ∷ K1⁻ ∷ [])
  b3 = at 6 1 (Bx1-0243 ∷ []) (lem-sym12-at0112203443 c4) ▸
       at 6 1 (Bx1-0423 ∷ []) (lem-sym23-at01103443 c4) ▸
       at 4 2 (Toff023 ∷ CZ04 ∷ CCZ234 ∷ []) (pw1 c4 (CZ04 ∷ Toff023 ∷ []) (Toff023 ∷ CZ04 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff023 ∷ CZ01 ∷ CCZ123 ∷ []) (lw4 c4 (CZ01 ∷ Toff023 ∷ []) (Toff023 ∷ CZ01 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ123 ∷ CCZ234 ∷ []) (lw0 c4 (CCZ234 ∷ CCZ123 ∷ []) (CCZ123 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ123 ∷ Bx1-0423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ034-at0110243243 c4) ▸
       at 7 2 (CCZ123 ∷ CCZ234 ∷ []) (lw0 c4 (CCZ234 ∷ CCZ123 ∷ []) (CCZ123 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ123 ∷ CZ04 ∷ []) (lem-auto-CZ01-∣-CCZ234-at14213243 c4) ▸ done

  b4 : Chain (K1 ∷ Toff023 ∷ Toff104 ∷ Toff023 ∷ CZ01 ∷ CCZ123 ∷ CCZ123 ∷ CZ04 ∷ CCZ234 ∷ Bx1-0423 ∷ CCZ234 ∷ Toff104 ∷ CZ01 ∷ K1⁻ ∷ []) (K1 ∷ Toff023 ∷ Toff104 ∷ Toff023 ∷ Toff104 ∷ CZ01 ∷ CZ01 ∷ Bx1-0423 ∷ K1⁻ ∷ [])
  b4 = at 5 2 [] (lw4 c4 (CCZ123 ∷ CCZ123 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 (CCZ234 ∷ Bx1-0423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ342-at0110243243 c4) ▸
       at 6 2 [] (lw0 c4 (CCZ234 ∷ CCZ234 ∷ []) [] tt tt Eq.refl) ▸
       at 6 2 (Toff104 ∷ Bx1-0423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-TOFF012-at0110243243 c4) ▸
       at 5 2 (Toff104 ∷ CZ04 ∷ []) (pw2 c4 (CZ04 ∷ Toff104 ∷ []) (Toff104 ∷ CZ04 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff104 ∷ CZ01 ∷ CZ04 ∷ []) (pw2 c4 (CZ01 ∷ Toff104 ∷ []) (Toff104 ∷ CZ01 ∷ CZ04 ∷ []) tt tt Eq.refl) ▸
       at 6 2 [] (pw1 c4 (CZ04 ∷ CZ04 ∷ []) [] tt tt Eq.refl) ▸
       at 6 2 (CZ01 ∷ Bx1-0423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CZ10-at0110243243 c4) ▸ done

  b5 : Chain (K1 ∷ Toff023 ∷ Toff104 ∷ Toff023 ∷ Toff104 ∷ CZ01 ∷ CZ01 ∷ Bx1-0423 ∷ K1⁻ ∷ []) (Bx0-2134 ∷ K1 ∷ Bx1-0423 ∷ K1⁻ ∷ [])
  b5 = at 5 2 [] (lw4 c4 (CZ01 ∷ CZ01 ∷ []) [] tt tt Eq.refl) ▸
       at 5 0 (K1⁻ ∷ K1 ∷ []) (lw4 c4 [] (K1⁻ ∷ K1 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Toff023 ∷ K1 ∷ []) (lw4 c4 (K1 ∷ Toff023 ∷ []) (Toff023 ∷ K1 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ014 ∷ K1 ∷ []) (pw2 c4 (K1 ∷ Toff104 ∷ []) (CCZ014 ∷ K1 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff023 ∷ K1 ∷ []) (lw4 c4 (K1 ∷ Toff023 ∷ []) (Toff023 ∷ K1 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CCZ014 ∷ []) (pw2 c4 (K1 ∷ Toff104 ∷ K1⁻ ∷ []) (CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx0-2314 ∷ []) (sym (lem-beta-T-at122331 c4)) ▸
       at 0 1 (Bx0-2134 ∷ []) (lem-sym23-at122331 c4) ▸ done

  b6 : Chain (Bx0-2134 ∷ K1 ∷ Bx1-0423 ∷ K1⁻ ∷ []) (Bx0-1234 ∷ Bx1-0234 ∷ [])
  b6 = at 0 1 (Bx0-1234 ∷ []) (lem-sym12-at1221 c4) ▸
       at 2 1 (Bx1-0243 ∷ []) (lem-sym23-at0110243243 c4) ▸
       at 2 1 (Bx1-0234 ∷ []) (lem-sym34-at01103443 c4) ▸
       at 1 3 (Bx1-0234 ∷ []) (lem-K0-pass-at0110 c4) ▸ done


-- sym34 @233442: 5 steps
lem-sym34-at233442 : Complete 4 → ⟪ (Bx0-1342 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ []) ⟫ʷ
lem-sym34-at233442 c4 = run b0
  where
  b0 : Chain (Bx0-1342 ∷ []) (Bx0-1324 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1243 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1342⟩ c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym34-at3443 c4) ▸
       at 0 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym34 @12233441: 5 steps
lem-sym34-at12233441 : Complete 4 → ⟪ (Bx0-2341 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2314 ∷ []) ⟫ʷ
lem-sym34-at12233441 c4 = run b0
  where
  b0 : Chain (Bx0-2341 ∷ []) (Bx0-2314 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1342 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2341⟩ c4) ▸
       at 1 1 (Bx0-1324 ∷ []) (lem-sym34-at233442 c4) ▸
       at 0 2 (Bx0-2314 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1324⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- CS20-beta-c @1221: 7 steps
lem-CS20-beta-c-at1221 : Complete 4 → ⟪ (CS01 ∷ Bx0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ CS01 ∷ []) ⟫ʷ
lem-CS20-beta-c-at1221 c4 = run b0
  where
  b0 : Chain (CS01 ∷ Bx0-2134 ∷ []) (Bx0-2134 ∷ CS01 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS02 ∷ Sw12 ∷ []) (lem-nat-1-CS01 c4) ▸
       at 2 2 (Bx0-1234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2134⟩ c4) ▸
       at 1 2 (Bx0-1234 ∷ CS02 ∷ []) (lem-CS20-beta-c c4) ▸
       at 0 2 (Bx0-2134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1234⟩ c4) ▸
       at 1 2 (CS01 ∷ Sw12 ∷ []) (lem-nat-1-CS02 c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym34 @122331: 5 steps
lem-sym34-at122331 : Complete 4 → ⟪ (Bx0-2314 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2341 ∷ []) ⟫ʷ
lem-sym34-at122331 c4 = run b0
  where
  b0 : Chain (Bx0-2314 ∷ []) (Bx0-2341 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1324 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2314⟩ c4) ▸
       at 1 1 (Bx0-1342 ∷ []) (lem-sym34-at2332 c4) ▸
       at 0 2 (Bx0-2341 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1342⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CS01 | BOX(0;2341): 5 steps
lem-auto-CS01-∣-BOX⟨0·2341⟩ : Complete 4 → ⟪ (CS01 ∷ Bx0-2341 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2341 ∷ CS01 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨0·2341⟩ c4 = run b0
  where
  b0 : Chain (CS01 ∷ Bx0-2341 ∷ []) (Bx0-2341 ∷ CS01 ∷ [])
  b0 = at 1 1 (Bx0-2314 ∷ []) (lem-sym34-at12233441 c4) ▸
       at 1 1 (Bx0-2134 ∷ []) (lem-sym23-at122331 c4) ▸
       at 0 2 (Bx0-2134 ∷ CS01 ∷ []) (lem-CS20-beta-c-at1221 c4) ▸
       at 0 1 (Bx0-2314 ∷ []) (lem-sym23-at1221 c4) ▸
       at 0 1 (Bx0-2341 ∷ []) (lem-sym34-at122331 c4) ▸ done


-- AX-SB: 8 steps
lem-AX-SB : Complete 4 → ⟪ (CS01 ∷ Sb0-2-34-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-34-1 ∷ CS01 ∷ []) ⟫ʷ
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
lem-sym23-at0210243143 : Complete 4 → ⟪ (Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0143 ∷ []) ⟫ʷ
lem-sym23-at0210243143 c4 = run b0
  where
  b0 : Chain (Bx2-0413 ∷ []) (Bx2-0143 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ c4) ▸
       at 1 1 (Bx1-0243 ∷ []) (lem-sym23-at0110243243 c4) ▸
       at 0 2 (Bx2-0143 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0243⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- SBsym: 9 steps
lem-SBsym : Complete 4 → ⟪ (Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-14-3 ∷ []) ⟫ʷ
lem-SBsym c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb2-0-41-3 ∷ []) (Bx2-0143 ∷ Toff314 ∷ Sb2-0-3-4 ∷ Toff314 ∷ Sb⁻2-0-3-4 ∷ [])
  b0 = at 0 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 2 1 (CS03 ∷ []) (refl) ▸
       at 4 1 (CS03⁻ ∷ []) (refl) ▸
       at 0 1 (Bx2-0143 ∷ []) (lem-sym23-at0210243143 c4) ▸
       at 1 1 (Toff314 ∷ []) (lw0 c4 (Toff314 ∷ []) (Toff314 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Toff314 ∷ []) (lw0 c4 (Toff314 ∷ []) (Toff314 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb2-0-3-4 ∷ []) (refl) ▸
       at 4 1 (Sb⁻2-0-3-4 ∷ []) (refl) ▸ done

  b1 : Chain (Bx2-0143 ∷ Toff314 ∷ Sb2-0-3-4 ∷ Toff314 ∷ Sb⁻2-0-3-4 ∷ []) (Sb2-0-14-3 ∷ [])
  b1 = at 0 5 (Sb2-0-14-3 ∷ []) (refl) ▸ done


-- SBsymd: 61 steps
lem-SBsymd : Complete 4 → ⟪ (Sb⁻2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-0-14-3 ∷ []) ⟫ʷ
lem-SBsymd c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (run b7)))))))
  where
  b0 : Chain (Sb⁻2-0-41-3 ∷ []) (Sb⁻2-0-41-3 ∷ CCZ012 ∷ Toff201 ∷ Bx0-243 ∷ Bx⁻2-03 ∷ CCZ024 ∷ Toff024 ∷ Bx⁻2-03 ∷ Toff024 ∷ CCZ024 ∷ Toff201 ∷ CCZ012 ∷ [])
  b0 = at 1 0 (CCZ012 ∷ CCZ012 ∷ []) (lw4 c4 [] (CCZ012 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 2 0 (Toff201 ∷ Toff201 ∷ []) (lw4 c4 [] (Toff201 ∷ Toff201 ∷ []) tt tt Eq.refl) ▸
       at 3 0 (CCZ024 ∷ Toff024 ∷ CZ03 ∷ Toff024 ∷ CCZ024 ∷ CZ03 ∷ CZ03 ∷ CCZ024 ∷ Toff024 ∷ CZ03 ∷ Toff024 ∷ CCZ024 ∷ []) (pw1 c4 [] (CCZ024 ∷ Toff024 ∷ CZ03 ∷ Toff024 ∷ CCZ024 ∷ CZ03 ∷ CZ03 ∷ CCZ024 ∷ Toff024 ∷ CZ03 ∷ Toff024 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Bx2-03 ∷ []) (refl) ▸
       at 8 1 (Bx2-03 ∷ []) (refl) ▸
       at 3 6 (Bx0-243 ∷ []) (refl) ▸
       at 4 1 (Bx⁻2-03 ∷ []) (refl) ▸
       at 7 1 (Bx⁻2-03 ∷ []) (refl) ▸ done

  b1 : Chain (Sb⁻2-0-41-3 ∷ CCZ012 ∷ Toff201 ∷ Bx0-243 ∷ Bx⁻2-03 ∷ CCZ024 ∷ Toff024 ∷ Bx⁻2-03 ∷ Toff024 ∷ CCZ024 ∷ Toff201 ∷ CCZ012 ∷ []) (Sb⁻2-0-41-3 ∷ CCZ012 ∷ Toff201 ∷ Bx0-243 ∷ Toff201 ∷ CCZ012 ∷ Bx0-243 ∷ Bx⁻2-03 ∷ CCZ024 ∷ Toff024 ∷ CZ03 ∷ Toff024 ∷ CCZ024 ∷ CCZ012 ∷ Toff201 ∷ Bx⁻0-243 ∷ Toff201 ∷ CCZ012 ∷ [])
  b1 = at 4 6 (Bx⁻0-243 ∷ []) (refl) ▸
       at 4 0 (Toff201 ∷ Toff201 ∷ []) (lw4 c4 [] (Toff201 ∷ Toff201 ∷ []) tt tt Eq.refl) ▸
       at 5 0 (CCZ012 ∷ CCZ012 ∷ []) (lw4 c4 [] (CCZ012 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 6 0 (CCZ024 ∷ Toff024 ∷ CZ03 ∷ Toff024 ∷ CCZ024 ∷ CZ03 ∷ CZ03 ∷ CCZ024 ∷ Toff024 ∷ CZ03 ∷ Toff024 ∷ CCZ024 ∷ []) (pw1 c4 [] (CCZ024 ∷ Toff024 ∷ CZ03 ∷ Toff024 ∷ CCZ024 ∷ CZ03 ∷ CZ03 ∷ CCZ024 ∷ Toff024 ∷ CZ03 ∷ Toff024 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 8 1 (Bx2-03 ∷ []) (refl) ▸
       at 11 1 (Bx2-03 ∷ []) (refl) ▸
       at 6 6 (Bx0-243 ∷ []) (refl) ▸
       at 7 1 (Bx⁻2-03 ∷ []) (refl) ▸ done

  b2 : Chain (Sb⁻2-0-41-3 ∷ CCZ012 ∷ Toff201 ∷ Bx0-243 ∷ Toff201 ∷ CCZ012 ∷ Bx0-243 ∷ Bx⁻2-03 ∷ CCZ024 ∷ Toff024 ∷ CZ03 ∷ Toff024 ∷ CCZ024 ∷ CCZ012 ∷ Toff201 ∷ Bx⁻0-243 ∷ Toff201 ∷ CCZ012 ∷ []) (Sb⁻2-0-41-3 ∷ Bx2-0143 ∷ Toff314 ∷ Sb2-0-3-4 ∷ Sb⁻2-0-3-4 ∷ Toff314 ∷ Bx⁻2-0143 ∷ [])
  b2 = at 10 1 (Bx⁻2-03 ∷ []) (refl) ▸
       at 7 6 (Bx⁻0-243 ∷ []) (refl) ▸
       at 1 6 (Bx2-0143 ∷ []) (refl) ▸
       at 2 6 (Bx⁻2-0143 ∷ []) (refl) ▸
       at 2 0 (Toff314 ∷ Toff314 ∷ []) (lw0 c4 [] (Toff314 ∷ Toff314 ∷ []) tt tt Eq.refl) ▸
       at 3 0 (CS03 ∷ CS03⁻ ∷ []) (lw4 c4 [] (CS03 ∷ CS03⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Sb2-0-3-4 ∷ []) (refl) ▸
       at 4 1 (Sb⁻2-0-3-4 ∷ []) (refl) ▸ done

  b3 : Chain (Sb⁻2-0-41-3 ∷ Bx2-0143 ∷ Toff314 ∷ Sb2-0-3-4 ∷ Sb⁻2-0-3-4 ∷ Toff314 ∷ Bx⁻2-0143 ∷ []) (Sb⁻2-0-41-3 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Sb⁻2-0-14-3 ∷ [])
  b3 = at 4 0 (Toff314 ∷ Toff314 ∷ []) (lw0 c4 [] (Toff314 ∷ Toff314 ∷ []) tt tt Eq.refl) ▸
       at 5 0 (CS03⁻ ∷ CS03 ∷ []) (lw4 c4 [] (CS03⁻ ∷ CS03 ∷ []) tt tt Eq.refl) ▸
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
       at 9 2 [] (pw1 c4 (CCZ024 ∷ CCZ024 ∷ []) [] tt tt Eq.refl) ▸
       at 8 2 [] (pw1 c4 (Toff204 ∷ Toff204 ∷ []) [] tt tt Eq.refl) ▸
       at 7 1 (Bx⁻2-03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-03 ∷ Toff012 ∷ CCZ012 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 10 1 (CZ03 ∷ []) (refl) ▸ done

  b5 : Chain (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻0-213 ∷ CCZ024 ∷ Toff204 ∷ CZ03 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Sb⁻2-0-14-3 ∷ []) (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ CZ03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx0-213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Sb⁻2-0-14-3 ∷ [])
  b5 = at 13 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) (refl) ▸
       at 15 1 (CZ03 ∷ []) (refl) ▸
       at 18 1 (CZ03 ∷ []) (refl) ▸
       at 7 12 [] (lw4 c4 (CZ03 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ []) [] tt tt Eq.refl) ▸
       at 6 2 [] (pw1 c4 (Toff204 ∷ Toff204 ∷ []) [] tt tt Eq.refl) ▸
       at 5 2 [] (pw1 c4 (CCZ024 ∷ CCZ024 ∷ []) [] tt tt Eq.refl) ▸
       at 4 1 (Bx⁻2-03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-03 ∷ Toff012 ∷ CCZ012 ∷ []) (refl) ▸
       at 4 1 (CZ03 ∷ []) (refl) ▸ done

  b6 : Chain (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ CZ03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx0-213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Sb⁻2-0-14-3 ∷ []) (Sb2-0-3-1 ∷ Toff314 ∷ CS03⁻ ∷ CS03 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Sb⁻2-0-14-3 ∷ [])
  b6 = at 7 1 (CZ03 ∷ []) (refl) ▸
       at 10 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) (refl) ▸
       at 12 1 (CZ03 ∷ []) (refl) ▸
       at 15 1 (CZ03 ∷ []) (refl) ▸
       at 4 12 [] (lw4 c4 (CZ03 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ []) [] tt tt Eq.refl) ▸
       at 3 2 [] (lw0 c4 (Toff314 ∷ Toff314 ∷ []) [] tt tt Eq.refl) ▸
       at 2 1 (CS03⁻ ∷ []) (refl) ▸
       at 3 1 (CS03 ∷ []) (refl) ▸ done

  b7 : Chain (Sb2-0-3-1 ∷ Toff314 ∷ CS03⁻ ∷ CS03 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Sb⁻2-0-14-3 ∷ []) (Sb⁻2-0-14-3 ∷ [])
  b7 = at 2 2 [] (lw4 c4 (CS03⁻ ∷ CS03 ∷ []) [] tt tt Eq.refl) ▸
       at 1 2 [] (lw0 c4 (Toff314 ∷ Toff314 ∷ []) [] tt tt Eq.refl) ▸
       at 0 1 (CS03 ∷ []) (refl) ▸
       at 1 1 (CS03⁻ ∷ []) (refl) ▸
       at 0 2 [] (lw4 c4 (CS03 ∷ CS03⁻ ∷ []) [] tt tt Eq.refl) ▸ done


-- sym12 @2332: 5 steps
lem-sym12-at2332 : Complete 4 → ⟪ (Bx0-1324 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3124 ∷ []) ⟫ʷ
lem-sym12-at2332 c4 = run b0
  where
  b0 : Chain (Bx0-1324 ∷ []) (Bx0-3124 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ c4) ▸
       at 1 1 (Bx0-2134 ∷ []) (lem-sym12 c4) ▸
       at 0 2 (Bx0-3124 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·2134⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym12 @243243: 5 steps
lem-sym12-at243243 : Complete 4 → ⟪ (Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4123 ∷ []) ⟫ʷ
lem-sym12-at243243 c4 = run b0
  where
  b0 : Chain (Bx0-1423 ∷ []) (Bx0-4123 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ c4) ▸
       at 1 1 (Bx0-3124 ∷ []) (lem-sym12-at2332 c4) ▸
       at 0 2 (Bx0-4123 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·3124⟩ c4) ▸
       at 1 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym12 @0110243243: 5 steps
lem-sym12-at0110243243 : Complete 4 → ⟪ (Bx1-0423 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-4023 ∷ []) ⟫ʷ
lem-sym12-at0110243243 c4 = run b0
  where
  b0 : Chain (Bx1-0423 ∷ []) (Bx1-4023 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ c4) ▸
       at 1 1 (Bx0-4123 ∷ []) (lem-sym12-at243243 c4) ▸
       at 0 2 (Bx1-4023 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·4123⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym12 @0210243143: 5 steps
lem-sym12-at0210243143 : Complete 4 → ⟪ (Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4013 ∷ []) ⟫ʷ
lem-sym12-at0210243143 c4 = run b0
  where
  b0 : Chain (Bx2-0413 ∷ []) (Bx2-4013 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ c4) ▸
       at 1 1 (Bx1-4023 ∷ []) (lem-sym12-at0110243243 c4) ▸
       at 0 2 (Bx2-4013 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·4023⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- SBtgt: 8 steps
lem-SBtgt : Complete 4 → ⟪ (Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-01-3 ∷ []) ⟫ʷ
lem-SBtgt c4 = run b0
  where
  b0 : Chain (Sb2-0-41-3 ∷ []) (Sb2-4-01-3 ∷ [])
  b0 = at 0 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 2 1 (CS03 ∷ []) (refl) ▸
       at 4 1 (CS03⁻ ∷ []) (refl) ▸
       at 0 1 (Bx2-4013 ∷ []) (lem-sym12-at0210243143 c4) ▸
       at 1 4 (Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (pw2 c4 (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb2-4-3-1 ∷ []) (refl) ▸
       at 4 1 (Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 0 5 (Sb2-4-01-3 ∷ []) (refl) ▸ done


-- BOXd-BOX @2332: 5 steps
lem-BOXd-BOX-at2332 : Complete 4 → ⟪ (Bx⁻0-1324 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ []) ⟫ʷ
lem-BOXd-BOX-at2332 c4 = run b0
  where
  b0 : Chain (Bx⁻0-1324 ∷ []) (Bx0-1324 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx⁻0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·1324⟩ c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-BOXd-BOX c4) ▸
       at 0 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- BOXd-BOX @243243: 5 steps
lem-BOXd-BOX-at243243 : Complete 4 → ⟪ (Bx⁻0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ []) ⟫ʷ
lem-BOXd-BOX-at243243 c4 = run b0
  where
  b0 : Chain (Bx⁻0-1423 ∷ []) (Bx0-1423 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx⁻0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨0·1423⟩ c4) ▸
       at 1 1 (Bx0-1324 ∷ []) (lem-BOXd-BOX-at2332 c4) ▸
       at 0 2 (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ c4) ▸
       at 1 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- BOXd-BOX @0110243243: 5 steps
lem-BOXd-BOX-at0110243243 : Complete 4 → ⟪ (Bx⁻1-0423 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0423 ∷ []) ⟫ʷ
lem-BOXd-BOX-at0110243243 c4 = run b0
  where
  b0 : Chain (Bx⁻1-0423 ∷ []) (Bx1-0423 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx⁻0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨1·0423⟩ c4) ▸
       at 1 1 (Bx0-1423 ∷ []) (lem-BOXd-BOX-at243243 c4) ▸
       at 0 2 (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- BOXd-BOX @0210243143: 5 steps
lem-BOXd-BOX-at0210243143 : Complete 4 → ⟪ (Bx⁻2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ []) ⟫ʷ
lem-BOXd-BOX-at0210243143 c4 = run b0
  where
  b0 : Chain (Bx⁻2-0413 ∷ []) (Bx2-0413 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx⁻1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨2·0413⟩ c4) ▸
       at 1 1 (Bx1-0423 ∷ []) (lem-BOXd-BOX-at0110243243 c4) ▸
       at 0 2 (Bx2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0423⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- BOXd-BOX @1221: 5 steps
lem-BOXd-BOX-at1221 : Complete 4 → ⟪ (Bx⁻0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ []) ⟫ʷ
lem-BOXd-BOX-at1221 c4 = run b0
  where
  b0 : Chain (Bx⁻0-2134 ∷ []) (Bx0-2134 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx⁻0-1234 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨0·2134⟩ c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-BOXd-BOX c4) ▸
       at 0 2 (Bx0-2134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1234⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- BOXd-BOX @132132: 5 steps
lem-BOXd-BOX-at132132 : Complete 4 → ⟪ (Bx⁻0-3124 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3124 ∷ []) ⟫ʷ
lem-BOXd-BOX-at132132 c4 = run b0
  where
  b0 : Chain (Bx⁻0-3124 ∷ []) (Bx0-3124 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx⁻0-2134 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·3124⟩ c4) ▸
       at 1 1 (Bx0-2134 ∷ []) (lem-BOXd-BOX-at1221 c4) ▸
       at 0 2 (Bx0-3124 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·2134⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- BOXd-BOX @14213243: 5 steps
lem-BOXd-BOX-at14213243 : Complete 4 → ⟪ (Bx⁻0-4123 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4123 ∷ []) ⟫ʷ
lem-BOXd-BOX-at14213243 c4 = run b0
  where
  b0 : Chain (Bx⁻0-4123 ∷ []) (Bx0-4123 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx⁻0-3124 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨0·4123⟩ c4) ▸
       at 1 1 (Bx0-3124 ∷ []) (lem-BOXd-BOX-at132132 c4) ▸
       at 0 2 (Bx0-4123 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·3124⟩ c4) ▸
       at 1 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- BOXd-BOX @0114203243: 5 steps
lem-BOXd-BOX-at0114203243 : Complete 4 → ⟪ (Bx⁻1-4023 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-4023 ∷ []) ⟫ʷ
lem-BOXd-BOX-at0114203243 c4 = run b0
  where
  b0 : Chain (Bx⁻1-4023 ∷ []) (Bx1-4023 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx⁻0-4123 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨1·4023⟩ c4) ▸
       at 1 1 (Bx0-4123 ∷ []) (lem-BOXd-BOX-at14213243 c4) ▸
       at 0 2 (Bx1-4023 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·4123⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- BOXd-BOX @0214203143: 5 steps
lem-BOXd-BOX-at0214203143 : Complete 4 → ⟪ (Bx⁻2-4013 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4013 ∷ []) ⟫ʷ
lem-BOXd-BOX-at0214203143 c4 = run b0
  where
  b0 : Chain (Bx⁻2-4013 ∷ []) (Bx2-4013 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx⁻1-4023 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨2·4013⟩ c4) ▸
       at 1 1 (Bx1-4023 ∷ []) (lem-BOXd-BOX-at0114203243 c4) ▸
       at 0 2 (Bx2-4013 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·4023⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- SBtgtd: 10 steps
lem-SBtgtd : Complete 4 → ⟪ (Sb⁻2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-4-01-3 ∷ []) ⟫ʷ
lem-SBtgtd c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb⁻2-0-41-3 ∷ []) (Sb2-4-3-1 ∷ Toff301 ∷ CS34⁻ ∷ Toff301 ∷ Bx⁻2-4013 ∷ [])
  b0 = at 0 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) (refl) ▸
       at 0 1 (CS03 ∷ []) (refl) ▸
       at 2 1 (CS03⁻ ∷ []) (refl) ▸
       at 0 4 (CS34 ∷ Toff301 ∷ CS34⁻ ∷ Toff301 ∷ []) (pw2 c4 (CS03 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ []) (CS34 ∷ Toff301 ∷ CS34⁻ ∷ Toff301 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Bx2-0413 ∷ []) (lem-BOXd-BOX-at0210243143 c4) ▸
       at 4 1 (Bx2-4013 ∷ []) (lem-sym12-at0210243143 c4) ▸
       at 4 1 (Bx⁻2-4013 ∷ []) (sym (lem-BOXd-BOX-at0214203143 c4)) ▸
       at 0 1 (Sb2-4-3-1 ∷ []) (refl) ▸ done

  b1 : Chain (Sb2-4-3-1 ∷ Toff301 ∷ CS34⁻ ∷ Toff301 ∷ Bx⁻2-4013 ∷ []) (Sb⁻2-4-01-3 ∷ [])
  b1 = at 2 1 (Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 0 5 (Sb⁻2-4-01-3 ∷ []) (refl) ▸ done


-- sym12 @021021: 5 steps
lem-sym12-at021021 : Complete 4 → ⟪ (Bx2-0134 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1034 ∷ []) ⟫ʷ
lem-sym12-at021021 c4 = run b0
  where
  b0 : Chain (Bx2-0134 ∷ []) (Bx2-1034 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-0234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0134⟩ c4) ▸
       at 1 1 (Bx1-2034 ∷ []) (lem-sym12-at0110 c4) ▸
       at 0 2 (Bx2-1034 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·2034⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym12 @03102132: 5 steps
lem-sym12-at03102132 : Complete 4 → ⟪ (Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1024 ∷ []) ⟫ʷ
lem-sym12-at03102132 c4 = run b0
  where
  b0 : Chain (Bx3-0124 ∷ []) (Bx3-1024 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx2-0134 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0124⟩ c4) ▸
       at 1 1 (Bx2-1034 ∷ []) (lem-sym12-at021021 c4) ▸
       at 0 2 (Bx3-1024 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·1034⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym23 @0110: 5 steps
lem-sym23-at0110 : Complete 4 → ⟪ (Bx1-0234 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0324 ∷ []) ⟫ʷ
lem-sym23-at0110 c4 = run b0
  where
  b0 : Chain (Bx1-0234 ∷ []) (Bx1-0324 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0234⟩ c4) ▸
       at 1 1 (Bx0-1324 ∷ []) (lem-sym23 c4) ▸
       at 0 2 (Bx1-0324 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1324⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym23 @021021: 5 steps
lem-sym23-at021021 : Complete 4 → ⟪ (Bx2-0134 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0314 ∷ []) ⟫ʷ
lem-sym23-at021021 c4 = run b0
  where
  b0 : Chain (Bx2-0134 ∷ []) (Bx2-0314 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-0234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0134⟩ c4) ▸
       at 1 1 (Bx1-0324 ∷ []) (lem-sym23-at0110 c4) ▸
       at 0 2 (Bx2-0314 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0324⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym23 @03102132: 5 steps
lem-sym23-at03102132 : Complete 4 → ⟪ (Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0214 ∷ []) ⟫ʷ
lem-sym23-at03102132 c4 = run b0
  where
  b0 : Chain (Bx3-0124 ∷ []) (Bx3-0214 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx2-0134 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0124⟩ c4) ▸
       at 1 1 (Bx2-0314 ∷ []) (lem-sym23-at021021 c4) ▸
       at 0 2 (Bx3-0214 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0314⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym23 @032032: 5 steps
lem-sym23-at032032 : Complete 4 → ⟪ (Bx3-1024 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1204 ∷ []) ⟫ʷ
lem-sym23-at032032 c4 = run b0
  where
  b0 : Chain (Bx3-1024 ∷ []) (Bx3-1204 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-0124 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1024⟩ c4) ▸
       at 1 1 (Bx3-0214 ∷ []) (lem-sym23-at03102132 c4) ▸
       at 0 2 (Bx3-1204 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·0214⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- beta-T @0110: 8 steps
lem-beta-T-at0110 : Complete 4 → ⟪ (Bx1-0234 ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ CCZ134 ∷ Toff102 ∷ CCZ134 ∷ []) ⟫ʷ
lem-beta-T-at0110 c4 = run b0
  where
  b0 : Chain (Bx1-0234 ∷ []) (Toff102 ∷ CCZ134 ∷ Toff102 ∷ CCZ134 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0234⟩ c4) ▸
       at 1 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-beta-T c4) ▸
       at 0 2 (Toff102 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff012 ∷ []) (Toff102 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4) ▸
       at 2 2 (Toff102 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff012 ∷ []) (Toff102 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4) ▸
       at 4 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- beta-T @021021: 8 steps
lem-beta-T-at021021 : Complete 4 → ⟪ (Bx2-0134 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) ⟫ʷ
lem-beta-T-at021021 c4 = run b0
  where
  b0 : Chain (Bx2-0134 ∷ []) (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-0234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0134⟩ c4) ▸
       at 1 1 (Toff102 ∷ CCZ134 ∷ Toff102 ∷ CCZ134 ∷ []) (lem-beta-T-at0110 c4) ▸
       at 0 2 (Toff201 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff102 ∷ []) (Toff201 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ134 ∷ []) (CCZ234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff201 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff102 ∷ []) (Toff201 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ134 ∷ []) (CCZ234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- beta-T @03102132: 8 steps
lem-beta-T-at03102132 : Complete 4 → ⟪ (Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ []) ⟫ʷ
lem-beta-T-at03102132 c4 = run b0
  where
  b0 : Chain (Bx3-0124 ∷ []) (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx2-0134 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0124⟩ c4) ▸
       at 1 1 (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-beta-T-at021021 c4) ▸
       at 0 2 (Toff301 ∷ Sw23 ∷ []) (lem-nat-2-TOFF201 c4) ▸
       at 1 2 (CCZ234 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff301 ∷ Sw23 ∷ []) (lem-nat-2-TOFF201 c4) ▸
       at 3 2 (CCZ234 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- beta-T @031031: 8 steps
lem-beta-T-at031031 : Complete 4 → ⟪ (Bx3-0214 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ []) ⟫ʷ
lem-beta-T-at031031 c4 = run b0
  where
  b0 : Chain (Bx3-0214 ∷ []) (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-0124 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0214⟩ c4) ▸
       at 1 1 (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ []) (lem-beta-T-at03102132 c4) ▸
       at 0 2 (Toff302 ∷ Sw12 ∷ []) (lem-nat-1-TOFF301 c4) ▸
       at 1 2 (CCZ134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ234 ∷ []) (CCZ134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff302 ∷ Sw12 ∷ []) (lem-nat-1-TOFF301 c4) ▸
       at 3 2 (CCZ134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ234 ∷ []) (CCZ134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done

