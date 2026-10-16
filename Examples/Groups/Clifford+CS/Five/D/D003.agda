{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D003 where

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
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-CX10-beta-c ; lem-CZ10-beta-c ; lem-Cz-beta ; lem-T-beta ; lem-beta-T-at2332 ; lem-beta-T-at243243 ; lem-beta-form ; lem-beta-mirror ; lem-c124-beta ; lem-sym12 ; lem-sym23 ; lem-sym34)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-F0-B ; lem-F0-C ; lem-F0-D ; lem-T312-beta ; lem-c124-beta-at3443 ; lem-sym12-at1221 ; lem-sym12-at132132 ; lem-sym23-at1221 ; lem-sym34-at03102132 ; lem-sym34-at1221)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-1-BOX⟨0·2134⟩ ; lem-nat-1-BOX⟨0·2413⟩ ; lem-nat-1-CCZ023 ; lem-nat-1-CCZ024 ; lem-nat-2-BOX⟨0·1234⟩ ; lem-nat-2-BOX⟨0·1324⟩ ; lem-nat-2-BOX⟨0·3412⟩ ; lem-nat-2-CCZ012 ; lem-nat-2-CCZ013 ; lem-nat-2-CCZ024 ; lem-nat-2-CCZ034 ; lem-nat-3-BOX⟨0·1243⟩ ; lem-nat-3-BOX⟨0·1423⟩ ; lem-nat-3-CCZ014 ; lem-nat-3-CCZ024)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-1-BOX⟨0·1423⟩ ; lem-nat-1-CCZ013 ; lem-nat-1-CCZ014 ; lem-nat-2-BOX⟨0·2413⟩ ; lem-nat-3-BOX⟨0·1324⟩ ; lem-nat-3-CCZ013 ; lem-nat-3-CCZ023)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-2-CCZ124 ; lem-nat-2-CCZ134)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-0-TOFF014)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-1-BOX⟨0·1243⟩)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-1-BOX⟨0·1234⟩ ; lem-nat-2-BOX⟨0·2134⟩ ; lem-nat-2-BOX⟨0·2143⟩)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-0-BOX⟨0·1423⟩ ; lem-nat-1-BOX⟨0·1324⟩ ; lem-nat-1-TOFF013)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-nat-0-BOX⟨0·1234⟩ ; lem-nat-0-BOX⟨0·1243⟩ ; lem-nat-0-BOX⟨1·0234⟩ ; lem-nat-0-BOX⟨1·0243⟩ ; lem-nat-0-BOX⟨1·0423⟩ ; lem-nat-1-BOX⟨1·0234⟩ ; lem-nat-1-BOX⟨1·0243⟩ ; lem-nat-1-BOX⟨2·0143⟩ ; lem-nat-1-BOX⟨3·0124⟩ ; lem-nat-1-BOX⟨3·0214⟩ ; lem-nat-2-BOX⟨2·0134⟩ ; lem-nat-2-BOX⟨2·0143⟩ ; lem-nat-2-BOX⟨2·0314⟩ ; lem-nat-2-BOX⟨2·0413⟩ ; lem-nat-2-BOX⟨3·0142⟩ ; lem-nat-2-BOX⟨3·0214⟩ ; lem-nat-2-BOX⟨3·0412⟩ ; lem-nat-3-BOX⟨0·1234⟩)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-nat-0-BOX⟨0·2134⟩ ; lem-nat-0-BOX⟨1·2034⟩ ; lem-nat-1-BOX⟨0·2143⟩ ; lem-nat-1-BOX⟨0·2314⟩ ; lem-nat-1-CX10 ; lem-nat-1-CX20 ; lem-nat-1-CZ01 ; lem-nat-1-CZ02 ; lem-nat-2-BOX⟨0·1243⟩ ; lem-nat-2-BOX⟨0·1342⟩ ; lem-nat-2-BOX⟨0·3142⟩ ; lem-nat-2-CCZ014 ; lem-nat-3-BOX⟨0·2134⟩ ; lem-nat-3-BOX⟨2·0314⟩ ; lem-nat-3-BOX⟨2·0413⟩)
open import Examples.Groups.Clifford+CS.Five.D.R012 using (lem-nat-0-BOX⟨0·2143⟩ ; lem-nat-0-BOX⟨0·2314⟩ ; lem-nat-0-BOX⟨1·2043⟩ ; lem-nat-0-BOX⟨1·2304⟩)
-- c124-beta @01103443: 7 steps
lem-c124-beta-at01103443 : Complete 4 → ⟪ (CCZ023 ∷ Bx1-0243 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0243 ∷ CCZ023 ∷ []) ⟫ʷ
lem-c124-beta-at01103443 c4 = run b0
  where
  b0 : Chain (CCZ023 ∷ Bx1-0243 ∷ []) (Bx1-0243 ∷ CCZ023 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ123 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ023 ∷ []) (CCZ123 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-1243 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0243⟩ c4) ▸
       at 1 2 (Bx0-1243 ∷ CCZ123 ∷ []) (lem-c124-beta-at3443 c4) ▸
       at 0 2 (Bx1-0243 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1243⟩ c4) ▸
       at 1 2 (CCZ023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ123 ∷ []) (CCZ023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- c124-beta @0210213443: 7 steps
lem-c124-beta-at0210213443 : Complete 4 → ⟪ (CCZ013 ∷ Bx2-0143 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0143 ∷ CCZ013 ∷ []) ⟫ʷ
lem-c124-beta-at0210213443 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ Bx2-0143 ∷ []) (Bx2-0143 ∷ CCZ013 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 2 2 (Bx1-0243 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0143⟩ c4) ▸
       at 1 2 (Bx1-0243 ∷ CCZ023 ∷ []) (lem-c124-beta-at01103443 c4) ▸
       at 0 2 (Bx2-0143 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0243⟩ c4) ▸
       at 1 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- c124-beta @0310213442: 7 steps
lem-c124-beta-at0310213442 : Complete 4 → ⟪ (CCZ012 ∷ Bx3-0142 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0142 ∷ CCZ012 ∷ []) ⟫ʷ
lem-c124-beta-at0310213442 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Bx3-0142 ∷ []) (Bx3-0142 ∷ CCZ012 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 2 2 (Bx2-0143 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0142⟩ c4) ▸
       at 1 2 (Bx2-0143 ∷ CCZ013 ∷ []) (lem-c124-beta-at0210213443 c4) ▸
       at 0 2 (Bx3-0142 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0143⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym34 @3443: 5 steps
lem-sym34-at3443 : Complete 4 → ⟪ (Bx0-1243 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-sym34-at3443 c4 = run b0
  where
  b0 : Chain (Bx0-1243 ∷ []) (Bx0-1234 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1243⟩ c4) ▸
       at 1 1 (Bx0-1243 ∷ []) (lem-sym34 c4) ▸
       at 0 2 (Bx0-1234 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1243⟩ c4) ▸
       at 1 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym34 @01103443: 5 steps
lem-sym34-at01103443 : Complete 4 → ⟪ (Bx1-0243 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0234 ∷ []) ⟫ʷ
lem-sym34-at01103443 c4 = run b0
  where
  b0 : Chain (Bx1-0243 ∷ []) (Bx1-0234 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1243 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0243⟩ c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym34-at3443 c4) ▸
       at 0 2 (Bx1-0234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1234⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym34 @0210213443: 5 steps
lem-sym34-at0210213443 : Complete 4 → ⟪ (Bx2-0143 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ []) ⟫ʷ
lem-sym34-at0210213443 c4 = run b0
  where
  b0 : Chain (Bx2-0143 ∷ []) (Bx2-0134 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-0243 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0143⟩ c4) ▸
       at 1 1 (Bx1-0234 ∷ []) (lem-sym34-at01103443 c4) ▸
       at 0 2 (Bx2-0134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0234⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym34 @0310213442: 5 steps
lem-sym34-at0310213442 : Complete 4 → ⟪ (Bx3-0142 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ []) ⟫ʷ
lem-sym34-at0310213442 c4 = run b0
  where
  b0 : Chain (Bx3-0142 ∷ []) (Bx3-0124 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx2-0143 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0142⟩ c4) ▸
       at 1 1 (Bx2-0134 ∷ []) (lem-sym34-at0210213443 c4) ▸
       at 0 2 (Bx3-0124 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0134⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | BOX(3;0124): 3 steps
lem-auto-CCZ012-∣-BOX⟨3·0124⟩ : Complete 4 → ⟪ (CCZ012 ∷ Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·0124⟩ c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Bx3-0124 ∷ []) (Bx3-0124 ∷ CCZ012 ∷ [])
  b0 = at 1 1 (Bx3-0142 ∷ []) (lem-sym34-at03102132 c4) ▸
       at 0 2 (Bx3-0142 ∷ CCZ012 ∷ []) (lem-c124-beta-at0310213442 c4) ▸
       at 0 1 (Bx3-0124 ∷ []) (lem-sym34-at0310213442 c4) ▸ done


-- auto CCZ012 | BOX(3;0124) @1221: 7 steps
lem-auto-CCZ012-∣-BOX⟨3·0124⟩-at1221 : Complete 4 → ⟪ (CCZ012 ∷ Bx3-0214 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0214 ∷ CCZ012 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·0124⟩-at1221 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Bx3-0214 ∷ []) (Bx3-0214 ∷ CCZ012 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx3-0124 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0214⟩ c4) ▸
       at 1 2 (Bx3-0124 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0124⟩ c4) ▸
       at 0 2 (Bx3-0214 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0124⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ012 ∷ []) (CCZ012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | BOX(3;0124) @132132: 7 steps
lem-auto-CCZ012-∣-BOX⟨3·0124⟩-at132132 : Complete 4 → ⟪ (CCZ013 ∷ Bx2-0314 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0314 ∷ CCZ013 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·0124⟩-at132132 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ Bx2-0314 ∷ []) (Bx2-0314 ∷ CCZ013 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 2 2 (Bx3-0214 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0314⟩ c4) ▸
       at 1 2 (Bx3-0214 ∷ CCZ012 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0124⟩-at1221 c4) ▸
       at 0 2 (Bx2-0314 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0214⟩ c4) ▸
       at 1 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | BOX(3;0124) @14213243: 7 steps
lem-auto-CCZ012-∣-BOX⟨3·0124⟩-at14213243 : Complete 4 → ⟪ (CCZ014 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ CCZ014 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·0124⟩-at14213243 c4 = run b0
  where
  b0 : Chain (CCZ014 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ CCZ014 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4) ▸
       at 2 2 (Bx2-0314 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·0413⟩ c4) ▸
       at 1 2 (Bx2-0314 ∷ CCZ013 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0124⟩-at132132 c4) ▸
       at 0 2 (Bx2-0413 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·0314⟩ c4) ▸
       at 1 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CCZ012 | BOX(3;0124) @142142: 7 steps
lem-auto-CCZ012-∣-BOX⟨3·0124⟩-at142142 : Complete 4 → ⟪ (CCZ014 ∷ Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ CCZ014 ∷ []) ⟫ʷ
lem-auto-CCZ012-∣-BOX⟨3·0124⟩-at142142 c4 = run b0
  where
  b0 : Chain (CCZ014 ∷ Bx3-0412 ∷ []) (Bx3-0412 ∷ CCZ014 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 2 2 (Bx2-0413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0412⟩ c4) ▸
       at 1 2 (Bx2-0413 ∷ CCZ014 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0124⟩-at14213243 c4) ▸
       at 0 2 (Bx3-0412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0413⟩ c4) ▸
       at 1 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- F0: 13 steps
lem-F0 : Complete 4 → ⟪ (Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-41-2 ∷ []) ⟫ʷ
lem-F0 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb2-0-41-3 ∷ []) (Bx3-0412 ∷ CCZ014 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CCZ014 ∷ [])
  b0 = at 0 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 2 1 (CS03 ∷ []) (refl) ▸
       at 4 1 (CS03⁻ ∷ []) (refl) ▸
       at 0 1 (CCZ014 ∷ Bx3-0412 ∷ Toff214 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ Toff214 ∷ CCZ023 ∷ []) (sym (lem-F0-D c4)) ▸
       at 2 6 (Toff214 ∷ Toff314 ∷ CS02 ∷ CS03 ∷ Toff314 ∷ Toff214 ∷ CS03⁻ ∷ CS02⁻ ∷ []) (lem-F0-B c4) ▸
       at 2 8 (Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (lem-F0-C c4) ▸
       at 6 8 (CCZ014 ∷ []) (pw2 c4 (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Bx3-0412 ∷ CCZ014 ∷ []) (lem-auto-CCZ012-∣-BOX⟨3·0124⟩-at142142 c4) ▸ done

  b1 : Chain (Bx3-0412 ∷ CCZ014 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CCZ014 ∷ []) (Sb3-0-41-2 ∷ [])
  b1 = at 1 5 (Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CCZ014 ∷ []) (pw3 c4 (CCZ014 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ []) (Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 5 2 [] (pw2 c4 (CCZ014 ∷ CCZ014 ∷ []) [] tt tt Eq.refl) ▸
       at 2 1 (Sb3-0-2-1 ∷ []) (refl) ▸
       at 4 1 (Sb⁻3-0-2-1 ∷ []) (refl) ▸
       at 0 5 (Sb3-0-41-2 ∷ []) (refl) ▸ done


-- F0d: 61 steps
lem-F0d : Complete 4 → ⟪ (Sb⁻2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻3-0-41-2 ∷ []) ⟫ʷ
lem-F0d c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (run b7)))))))
  where
  b0 : Chain (Sb⁻2-0-41-3 ∷ []) (Sb⁻2-0-41-3 ∷ CCZ034 ∷ Toff304 ∷ Bx0-312 ∷ Bx⁻3-02 ∷ CCZ013 ∷ Toff013 ∷ Bx⁻3-02 ∷ Toff013 ∷ CCZ013 ∷ Toff304 ∷ CCZ034 ∷ [])
  b0 = at 1 0 (CCZ034 ∷ CCZ034 ∷ []) (pw1 c4 [] (CCZ034 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 2 0 (Toff304 ∷ Toff304 ∷ []) (pw1 c4 [] (Toff304 ∷ Toff304 ∷ []) tt tt Eq.refl) ▸
       at 3 0 (CCZ013 ∷ Toff013 ∷ CZ02 ∷ Toff013 ∷ CCZ013 ∷ CZ02 ∷ CZ02 ∷ CCZ013 ∷ Toff013 ∷ CZ02 ∷ Toff013 ∷ CCZ013 ∷ []) (lw4 c4 [] (CCZ013 ∷ Toff013 ∷ CZ02 ∷ Toff013 ∷ CCZ013 ∷ CZ02 ∷ CZ02 ∷ CCZ013 ∷ Toff013 ∷ CZ02 ∷ Toff013 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Bx3-02 ∷ []) (refl) ▸
       at 8 1 (Bx3-02 ∷ []) (refl) ▸
       at 3 6 (Bx0-312 ∷ []) (refl) ▸
       at 4 1 (Bx⁻3-02 ∷ []) (refl) ▸
       at 7 1 (Bx⁻3-02 ∷ []) (refl) ▸ done

  b1 : Chain (Sb⁻2-0-41-3 ∷ CCZ034 ∷ Toff304 ∷ Bx0-312 ∷ Bx⁻3-02 ∷ CCZ013 ∷ Toff013 ∷ Bx⁻3-02 ∷ Toff013 ∷ CCZ013 ∷ Toff304 ∷ CCZ034 ∷ []) (Sb⁻2-0-41-3 ∷ CCZ034 ∷ Toff304 ∷ Bx0-312 ∷ Toff304 ∷ CCZ034 ∷ Bx0-312 ∷ Bx⁻3-02 ∷ CCZ013 ∷ Toff013 ∷ CZ02 ∷ Toff013 ∷ CCZ013 ∷ CCZ034 ∷ Toff304 ∷ Bx⁻0-312 ∷ Toff304 ∷ CCZ034 ∷ [])
  b1 = at 4 6 (Bx⁻0-312 ∷ []) (refl) ▸
       at 4 0 (Toff304 ∷ Toff304 ∷ []) (pw1 c4 [] (Toff304 ∷ Toff304 ∷ []) tt tt Eq.refl) ▸
       at 5 0 (CCZ034 ∷ CCZ034 ∷ []) (pw1 c4 [] (CCZ034 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 6 0 (CCZ013 ∷ Toff013 ∷ CZ02 ∷ Toff013 ∷ CCZ013 ∷ CZ02 ∷ CZ02 ∷ CCZ013 ∷ Toff013 ∷ CZ02 ∷ Toff013 ∷ CCZ013 ∷ []) (lw4 c4 [] (CCZ013 ∷ Toff013 ∷ CZ02 ∷ Toff013 ∷ CCZ013 ∷ CZ02 ∷ CZ02 ∷ CCZ013 ∷ Toff013 ∷ CZ02 ∷ Toff013 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 8 1 (Bx3-02 ∷ []) (refl) ▸
       at 11 1 (Bx3-02 ∷ []) (refl) ▸
       at 6 6 (Bx0-312 ∷ []) (refl) ▸
       at 7 1 (Bx⁻3-02 ∷ []) (refl) ▸ done

  b2 : Chain (Sb⁻2-0-41-3 ∷ CCZ034 ∷ Toff304 ∷ Bx0-312 ∷ Toff304 ∷ CCZ034 ∷ Bx0-312 ∷ Bx⁻3-02 ∷ CCZ013 ∷ Toff013 ∷ CZ02 ∷ Toff013 ∷ CCZ013 ∷ CCZ034 ∷ Toff304 ∷ Bx⁻0-312 ∷ Toff304 ∷ CCZ034 ∷ []) (Sb⁻2-0-41-3 ∷ Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Sb⁻3-0-2-1 ∷ Toff214 ∷ Bx⁻3-0412 ∷ [])
  b2 = at 10 1 (Bx⁻3-02 ∷ []) (refl) ▸
       at 7 6 (Bx⁻0-312 ∷ []) (refl) ▸
       at 1 6 (Bx3-0412 ∷ []) (refl) ▸
       at 2 6 (Bx⁻3-0412 ∷ []) (refl) ▸
       at 2 0 (Toff214 ∷ Toff214 ∷ []) (lw0 c4 [] (Toff214 ∷ Toff214 ∷ []) tt tt Eq.refl) ▸
       at 3 0 (CS02 ∷ CS02⁻ ∷ []) (lw4 c4 [] (CS02 ∷ CS02⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Sb3-0-2-1 ∷ []) (refl) ▸
       at 4 1 (Sb⁻3-0-2-1 ∷ []) (refl) ▸ done

  b3 : Chain (Sb⁻2-0-41-3 ∷ Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Sb⁻3-0-2-1 ∷ Toff214 ∷ Bx⁻3-0412 ∷ []) (Sb⁻2-0-41-3 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Sb⁻3-0-41-2 ∷ [])
  b3 = at 4 0 (Toff214 ∷ Toff214 ∷ []) (lw0 c4 [] (Toff214 ∷ Toff214 ∷ []) tt tt Eq.refl) ▸
       at 5 0 (CS02⁻ ∷ CS02 ∷ []) (lw4 c4 [] (CS02⁻ ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Sb⁻3-0-2-1 ∷ []) (refl) ▸
       at 6 1 (Sb3-0-2-1 ∷ []) (refl) ▸
       at 1 5 (Sb3-0-41-2 ∷ []) (refl) ▸
       at 2 5 (Sb⁻3-0-41-2 ∷ []) (refl) ▸
       at 1 1 (Sb2-0-41-3 ∷ []) (sym (lem-F0 c4)) ▸
       at 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸ done

  b4 : Chain (Sb⁻2-0-41-3 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Sb⁻3-0-41-2 ∷ []) (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻0-213 ∷ CCZ024 ∷ Toff204 ∷ CZ03 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Sb⁻3-0-41-2 ∷ [])
  b4 = at 0 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) (refl) ▸
       at 5 1 (CCZ024 ∷ Toff204 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ []) (refl) ▸
       at 4 1 (Bx⁻0-213 ∷ CCZ024 ∷ Toff204 ∷ Bx⁻0-213 ∷ Toff204 ∷ CCZ024 ∷ []) (refl) ▸
       at 9 2 [] (pw1 c4 (CCZ024 ∷ CCZ024 ∷ []) [] tt tt Eq.refl) ▸
       at 8 2 [] (pw1 c4 (Toff204 ∷ Toff204 ∷ []) [] tt tt Eq.refl) ▸
       at 7 1 (Bx⁻2-03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-03 ∷ Toff012 ∷ CCZ012 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 10 1 (CZ03 ∷ []) (refl) ▸ done

  b5 : Chain (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻0-213 ∷ CCZ024 ∷ Toff204 ∷ CZ03 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Sb⁻3-0-41-2 ∷ []) (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ CZ03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx0-213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Sb⁻3-0-41-2 ∷ [])
  b5 = at 13 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) (refl) ▸
       at 15 1 (CZ03 ∷ []) (refl) ▸
       at 18 1 (CZ03 ∷ []) (refl) ▸
       at 7 12 [] (lw4 c4 (CZ03 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ []) [] tt tt Eq.refl) ▸
       at 6 2 [] (pw1 c4 (Toff204 ∷ Toff204 ∷ []) [] tt tt Eq.refl) ▸
       at 5 2 [] (pw1 c4 (CCZ024 ∷ CCZ024 ∷ []) [] tt tt Eq.refl) ▸
       at 4 1 (Bx⁻2-03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-03 ∷ Toff012 ∷ CCZ012 ∷ []) (refl) ▸
       at 4 1 (CZ03 ∷ []) (refl) ▸ done

  b6 : Chain (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ CZ03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx0-213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Sb⁻3-0-41-2 ∷ []) (Sb2-0-3-1 ∷ Toff314 ∷ CS03⁻ ∷ CS03 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Sb⁻3-0-41-2 ∷ [])
  b6 = at 7 1 (CZ03 ∷ []) (refl) ▸
       at 10 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) (refl) ▸
       at 12 1 (CZ03 ∷ []) (refl) ▸
       at 15 1 (CZ03 ∷ []) (refl) ▸
       at 4 12 [] (lw4 c4 (CZ03 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ []) [] tt tt Eq.refl) ▸
       at 3 2 [] (lw0 c4 (Toff314 ∷ Toff314 ∷ []) [] tt tt Eq.refl) ▸
       at 2 1 (CS03⁻ ∷ []) (refl) ▸
       at 3 1 (CS03 ∷ []) (refl) ▸ done

  b7 : Chain (Sb2-0-3-1 ∷ Toff314 ∷ CS03⁻ ∷ CS03 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Sb⁻3-0-41-2 ∷ []) (Sb⁻3-0-41-2 ∷ [])
  b7 = at 2 2 [] (lw4 c4 (CS03⁻ ∷ CS03 ∷ []) [] tt tt Eq.refl) ▸
       at 1 2 [] (lw0 c4 (Toff314 ∷ Toff314 ∷ []) [] tt tt Eq.refl) ▸
       at 0 1 (CS03 ∷ []) (refl) ▸
       at 1 1 (CS03⁻ ∷ []) (refl) ▸
       at 0 2 [] (lw4 c4 (CS03 ∷ CS03⁻ ∷ []) [] tt tt Eq.refl) ▸ done


-- sym12 @011220: 5 steps
lem-sym12-at011220 : Complete 4 → ⟪ (Bx1-2034 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0234 ∷ []) ⟫ʷ
lem-sym12-at011220 c4 = run b0
  where
  b0 : Chain (Bx1-2034 ∷ []) (Bx1-0234 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-2134 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·2034⟩ c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym12-at1221 c4) ▸
       at 0 2 (Bx1-0234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1234⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- CX10-beta-c @0110: 7 steps
lem-CX10-beta-c-at0110 : Complete 4 → ⟪ (CX01 ∷ Bx1-0234 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0234 ∷ CX01 ∷ []) ⟫ʷ
lem-CX10-beta-c-at0110 c4 = run b0
  where
  b0 : Chain (CX01 ∷ Bx1-0234 ∷ []) (Bx1-0234 ∷ CX01 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CX10 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CX01 ∷ []) (CX10 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-1234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0234⟩ c4) ▸
       at 1 2 (Bx0-1234 ∷ CX10 ∷ []) (lem-CX10-beta-c c4) ▸
       at 0 2 (Bx1-0234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1234⟩ c4) ▸
       at 1 2 (CX01 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CX10 ∷ []) (CX01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym12 @0110: 5 steps
lem-sym12-at0110 : Complete 4 → ⟪ (Bx1-0234 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2034 ∷ []) ⟫ʷ
lem-sym12-at0110 c4 = run b0
  where
  b0 : Chain (Bx1-0234 ∷ []) (Bx1-2034 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0234⟩ c4) ▸
       at 1 1 (Bx0-2134 ∷ []) (lem-sym12 c4) ▸
       at 0 2 (Bx1-2034 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·2134⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CX01 | BOX(1;2034): 3 steps
lem-auto-CX01-∣-BOX⟨1·2034⟩ : Complete 4 → ⟪ (CX01 ∷ Bx1-2034 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2034 ∷ CX01 ∷ []) ⟫ʷ
lem-auto-CX01-∣-BOX⟨1·2034⟩ c4 = run b0
  where
  b0 : Chain (CX01 ∷ Bx1-2034 ∷ []) (Bx1-2034 ∷ CX01 ∷ [])
  b0 = at 1 1 (Bx1-0234 ∷ []) (lem-sym12-at011220 c4) ▸
       at 0 2 (Bx1-0234 ∷ CX01 ∷ []) (lem-CX10-beta-c-at0110 c4) ▸
       at 0 1 (Bx1-2034 ∷ []) (lem-sym12-at0110 c4) ▸ done


-- CZ10-beta-c @1221: 7 steps
lem-CZ10-beta-c-at1221 : Complete 4 → ⟪ (CZ01 ∷ Bx0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ CZ01 ∷ []) ⟫ʷ
lem-CZ10-beta-c-at1221 c4 = run b0
  where
  b0 : Chain (CZ01 ∷ Bx0-2134 ∷ []) (Bx0-2134 ∷ CZ01 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CZ02 ∷ Sw12 ∷ []) (lem-nat-1-CZ01 c4) ▸
       at 2 2 (Bx0-1234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2134⟩ c4) ▸
       at 1 2 (Bx0-1234 ∷ CZ02 ∷ []) (lem-CZ10-beta-c c4) ▸
       at 0 2 (Bx0-2134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1234⟩ c4) ▸
       at 1 2 (CZ01 ∷ Sw12 ∷ []) (lem-nat-1-CZ02 c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- CZ10-beta-c @011220: 7 steps
lem-CZ10-beta-c-at011220 : Complete 4 → ⟪ (CZ01 ∷ Bx1-2034 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2034 ∷ CZ01 ∷ []) ⟫ʷ
lem-CZ10-beta-c-at011220 c4 = run b0
  where
  b0 : Chain (CZ01 ∷ Bx1-2034 ∷ []) (Bx1-2034 ∷ CZ01 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CZ01 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CZ01 ∷ []) (CZ01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-2134 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·2034⟩ c4) ▸
       at 1 2 (Bx0-2134 ∷ CZ01 ∷ []) (lem-CZ10-beta-c-at1221 c4) ▸
       at 0 2 (Bx1-2034 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·2134⟩ c4) ▸
       at 1 2 (CZ01 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CZ01 ∷ []) (CZ01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CZ01 | BOX(1;2034): 3 steps
lem-auto-CZ01-∣-BOX⟨1·2034⟩ : Complete 4 → ⟪ (CZ01 ∷ Bx1-2034 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2034 ∷ CZ01 ∷ []) ⟫ʷ
lem-auto-CZ01-∣-BOX⟨1·2034⟩ c4 = run b0
  where
  b0 : Chain (CZ01 ∷ Bx1-2034 ∷ []) (Bx1-2034 ∷ CZ01 ∷ [])
  b0 = at 0 1 (CZ01 ∷ []) (lw4 c4 (CZ01 ∷ []) (CZ01 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Bx1-2034 ∷ CZ01 ∷ []) (lem-CZ10-beta-c-at011220 c4) ▸
       at 1 1 (CZ01 ∷ []) (lw4 c4 (CZ01 ∷ []) (CZ01 ∷ []) tt tt Eq.refl) ▸ done


-- auto CZ01 CX01 | BOX(1;2034): 2 steps
lem-auto-CZ01-CX01-∣-BOX⟨1·2034⟩ : Complete 4 → ⟪ (CZ01 ∷ CX01 ∷ Bx1-2034 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2034 ∷ CZ01 ∷ CX01 ∷ []) ⟫ʷ
lem-auto-CZ01-CX01-∣-BOX⟨1·2034⟩ c4 = run b0
  where
  b0 : Chain (CZ01 ∷ CX01 ∷ Bx1-2034 ∷ []) (Bx1-2034 ∷ CZ01 ∷ CX01 ∷ [])
  b0 = at 1 2 (Bx1-2034 ∷ CX01 ∷ []) (lem-auto-CX01-∣-BOX⟨1·2034⟩ c4) ▸
       at 0 2 (Bx1-2034 ∷ CZ01 ∷ []) (lem-auto-CZ01-∣-BOX⟨1·2034⟩ c4) ▸ done


-- c124-beta @2332: 7 steps
lem-c124-beta-at2332 : Complete 4 → ⟪ (CCZ134 ∷ Bx0-1324 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ CCZ134 ∷ []) ⟫ʷ
lem-c124-beta-at2332 c4 = run b0
  where
  b0 : Chain (CCZ134 ∷ Bx0-1324 ∷ []) (Bx0-1324 ∷ CCZ134 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 2 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ c4) ▸
       at 1 2 (Bx0-1234 ∷ CCZ124 ∷ []) (lem-c124-beta c4) ▸
       at 0 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ c4) ▸
       at 1 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- c124-beta @122331: 7 steps
lem-c124-beta-at122331 : Complete 4 → ⟪ (CCZ234 ∷ Bx0-2314 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2314 ∷ CCZ234 ∷ []) ⟫ʷ
lem-c124-beta-at122331 c4 = run b0
  where
  b0 : Chain (CCZ234 ∷ Bx0-2314 ∷ []) (Bx0-2314 ∷ CCZ234 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ234 ∷ []) (CCZ134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-1324 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2314⟩ c4) ▸
       at 1 2 (Bx0-1324 ∷ CCZ134 ∷ []) (lem-c124-beta-at2332 c4) ▸
       at 0 2 (Bx0-2314 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1324⟩ c4) ▸
       at 1 2 (CCZ234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ134 ∷ []) (CCZ234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym23 @2332: 5 steps
lem-sym23-at2332 : Complete 4 → ⟪ (Bx0-1324 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-sym23-at2332 c4 = run b0
  where
  b0 : Chain (Bx0-1324 ∷ []) (Bx0-1234 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ c4) ▸
       at 1 1 (Bx0-1324 ∷ []) (lem-sym23 c4) ▸
       at 0 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym23 @122331: 5 steps
lem-sym23-at122331 : Complete 4 → ⟪ (Bx0-2314 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ []) ⟫ʷ
lem-sym23-at122331 c4 = run b0
  where
  b0 : Chain (Bx0-2314 ∷ []) (Bx0-2134 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1324 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2314⟩ c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym23-at2332 c4) ▸
       at 0 2 (Bx0-2134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1234⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ234: 5 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ234 : Complete 4 → ⟪ (Bx0-1234 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ234 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ CCZ234 ∷ []) (CCZ234 ∷ Bx0-1234 ∷ [])
  b0 = at 0 1 (Bx0-2134 ∷ []) (lem-sym12 c4) ▸
       at 0 1 (Bx0-2314 ∷ []) (lem-sym23-at1221 c4) ▸
       at 0 2 (CCZ234 ∷ Bx0-2314 ∷ []) (sym (lem-c124-beta-at122331 c4)) ▸
       at 1 1 (Bx0-2134 ∷ []) (lem-sym23-at122331 c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym12-at1221 c4) ▸ done


-- auto CZ01 CX01 | BOX(1;2034) @0110: 9 steps
lem-auto-CZ01-CX01-∣-BOX⟨1·2034⟩-at0110 : Complete 4 → ⟪ (CZ01 ∷ CX10 ∷ Bx0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ CZ01 ∷ CX10 ∷ []) ⟫ʷ
lem-auto-CZ01-CX01-∣-BOX⟨1·2034⟩-at0110 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CZ01 ∷ CX10 ∷ Bx0-2134 ∷ []) (Bx0-2134 ∷ CZ01 ∷ CX10 ∷ Sw01 ∷ Sw01 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CZ01 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CZ01 ∷ []) (CZ01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CX01 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CX10 ∷ []) (CX01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Bx1-2034 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·2134⟩ c4) ▸
       at 1 3 (Bx1-2034 ∷ CZ01 ∷ CX01 ∷ []) (lem-auto-CZ01-CX01-∣-BOX⟨1·2034⟩ c4) ▸
       at 0 2 (Bx0-2134 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·2034⟩ c4) ▸
       at 1 2 (CZ01 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CZ01 ∷ []) (CZ01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CX10 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CX01 ∷ []) (CX10 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Bx0-2134 ∷ CZ01 ∷ CX10 ∷ Sw01 ∷ Sw01 ∷ []) (Bx0-2134 ∷ CZ01 ∷ CX10 ∷ [])
  b1 = at 3 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto CZ01 CX01 | BOX(1;2034) @021021: 9 steps
lem-auto-CZ01-CX01-∣-BOX⟨1·2034⟩-at021021 : Complete 4 → ⟪ (CZ02 ∷ CX20 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CZ02 ∷ CX20 ∷ []) ⟫ʷ
lem-auto-CZ01-CX01-∣-BOX⟨1·2034⟩-at021021 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CZ02 ∷ CX20 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CZ02 ∷ CX20 ∷ Sw12 ∷ Sw12 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CZ01 ∷ Sw12 ∷ []) (lem-nat-1-CZ02 c4) ▸
       at 2 2 (CX10 ∷ Sw12 ∷ []) (lem-nat-1-CX20 c4) ▸
       at 3 2 (Bx0-2134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1234⟩ c4) ▸
       at 1 3 (Bx0-2134 ∷ CZ01 ∷ CX10 ∷ []) (lem-auto-CZ01-CX01-∣-BOX⟨1·2034⟩-at0110 c4) ▸
       at 0 2 (Bx0-1234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2134⟩ c4) ▸
       at 1 2 (CZ02 ∷ Sw12 ∷ []) (lem-nat-1-CZ01 c4) ▸
       at 2 2 (CX20 ∷ Sw12 ∷ []) (lem-nat-1-CX10 c4) ▸ done

  b1 : Chain (Bx0-1234 ∷ CZ02 ∷ CX20 ∷ Sw12 ∷ Sw12 ∷ []) (Bx0-1234 ∷ CZ02 ∷ CX20 ∷ [])
  b1 = at 3 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- X1-beta: 10 steps
lem-X1-beta : Complete 4 → ⟪ (X1 ∷ Bx0-1234 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-X1-beta c4 = trans (run b0) (run b1)
  where
  b0 : Chain (X1 ∷ Bx0-1234 ∷ X1 ∷ []) (Bx0-1234 ∷ CZ02 ∷ CX20 ∷ CCZ034 ∷ CX20 ∷ CZ02 ∷ CCZ034 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) (lem-beta-form c4) ▸
       at 0 3 (CZ02 ∷ CX20 ∷ Toff012 ∷ CCZ012 ∷ X1 ∷ []) (lw4 c4 (X1 ∷ CCZ012 ∷ Toff012 ∷ []) (CZ02 ∷ CX20 ∷ Toff012 ∷ CCZ012 ∷ X1 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ034 ∷ X1 ∷ []) (pw2 c4 (X1 ∷ CCZ034 ∷ []) (CCZ034 ∷ X1 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (CCZ012 ∷ Toff012 ∷ CX20 ∷ CZ02 ∷ X1 ∷ []) (lw4 c4 (X1 ∷ Toff012 ∷ CCZ012 ∷ []) (CCZ012 ∷ Toff012 ∷ CX20 ∷ CZ02 ∷ X1 ∷ []) tt tt Eq.refl) ▸
       at 9 3 (CCZ034 ∷ []) (pw2 c4 (X1 ∷ CCZ034 ∷ X1 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 7 0 (CCZ034 ∷ CCZ034 ∷ []) (pw1 c4 [] (CCZ034 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 2 6 (Bx0-1234 ∷ []) (sym (lem-beta-mirror c4)) ▸
       at 0 3 (Bx0-1234 ∷ CZ02 ∷ CX20 ∷ []) (lem-auto-CZ01-CX01-∣-BOX⟨1·2034⟩-at021021 c4) ▸ done

  b1 : Chain (Bx0-1234 ∷ CZ02 ∷ CX20 ∷ CCZ034 ∷ CX20 ∷ CZ02 ∷ CCZ034 ∷ []) (CCZ234 ∷ Bx0-1234 ∷ [])
  b1 = at 1 6 (CCZ234 ∷ []) (pw1 c4 (CZ02 ∷ CX20 ∷ CCZ034 ∷ CX20 ∷ CZ02 ∷ CCZ034 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (CCZ234 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ234 c4) ▸ done


-- sym34 @2332: 5 steps
lem-sym34-at2332 : Complete 4 → ⟪ (Bx0-1324 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1342 ∷ []) ⟫ʷ
lem-sym34-at2332 c4 = run b0
  where
  b0 : Chain (Bx0-1324 ∷ []) (Bx0-1342 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ c4) ▸
       at 1 1 (Bx0-1243 ∷ []) (lem-sym34 c4) ▸
       at 0 2 (Bx0-1342 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1243⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym12 @3443: 5 steps
lem-sym12-at3443 : Complete 4 → ⟪ (Bx0-1243 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2143 ∷ []) ⟫ʷ
lem-sym12-at3443 c4 = run b0
  where
  b0 : Chain (Bx0-1243 ∷ []) (Bx0-2143 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1243⟩ c4) ▸
       at 1 1 (Bx0-2134 ∷ []) (lem-sym12 c4) ▸
       at 0 2 (Bx0-2143 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·2134⟩ c4) ▸
       at 1 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym12 @233442: 5 steps
lem-sym12-at233442 : Complete 4 → ⟪ (Bx0-1342 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3142 ∷ []) ⟫ʷ
lem-sym12-at233442 c4 = run b0
  where
  b0 : Chain (Bx0-1342 ∷ []) (Bx0-3142 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1243 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1342⟩ c4) ▸
       at 1 1 (Bx0-2143 ∷ []) (lem-sym12-at3443 c4) ▸
       at 0 2 (Bx0-3142 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·2143⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym23 @3443: 5 steps
lem-sym23-at3443 : Complete 4 → ⟪ (Bx0-1243 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ []) ⟫ʷ
lem-sym23-at3443 c4 = run b0
  where
  b0 : Chain (Bx0-1243 ∷ []) (Bx0-1423 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1243⟩ c4) ▸
       at 1 1 (Bx0-1324 ∷ []) (lem-sym23 c4) ▸
       at 0 2 (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ c4) ▸
       at 1 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym23 @12213443: 5 steps
lem-sym23-at12213443 : Complete 4 → ⟪ (Bx0-2143 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2413 ∷ []) ⟫ʷ
lem-sym23-at12213443 c4 = run b0
  where
  b0 : Chain (Bx0-2143 ∷ []) (Bx0-2413 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1243 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2143⟩ c4) ▸
       at 1 1 (Bx0-1423 ∷ []) (lem-sym23-at3443 c4) ▸
       at 0 2 (Bx0-2413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1423⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym23 @13213442: 5 steps
lem-sym23-at13213442 : Complete 4 → ⟪ (Bx0-3142 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3412 ∷ []) ⟫ʷ
lem-sym23-at13213442 c4 = run b0
  where
  b0 : Chain (Bx0-3142 ∷ []) (Bx0-3412 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-2143 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3142⟩ c4) ▸
       at 1 1 (Bx0-2413 ∷ []) (lem-sym23-at12213443 c4) ▸
       at 0 2 (Bx0-3412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·2413⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- Cz-beta @2332: 7 steps
lem-Cz-beta-at2332 : Complete 4 → ⟪ (CCZ013 ∷ Bx0-1324 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ CCZ013 ∷ []) ⟫ʷ
lem-Cz-beta-at2332 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ Bx0-1324 ∷ []) (Bx0-1324 ∷ CCZ013 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 2 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ c4) ▸
       at 1 2 (Bx0-1234 ∷ CCZ012 ∷ []) (lem-Cz-beta c4) ▸
       at 0 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ c4) ▸
       at 1 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- Cz-beta @243243: 7 steps
lem-Cz-beta-at243243 : Complete 4 → ⟪ (CCZ014 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ CCZ014 ∷ []) ⟫ʷ
lem-Cz-beta-at243243 c4 = run b0
  where
  b0 : Chain (CCZ014 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ CCZ014 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4) ▸
       at 2 2 (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ c4) ▸
       at 1 2 (Bx0-1324 ∷ CCZ013 ∷ []) (lem-Cz-beta-at2332 c4) ▸
       at 0 2 (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ c4) ▸
       at 1 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- Cz-beta @12243143: 7 steps
lem-Cz-beta-at12243143 : Complete 4 → ⟪ (CCZ024 ∷ Bx0-2413 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2413 ∷ CCZ024 ∷ []) ⟫ʷ
lem-Cz-beta-at12243143 c4 = run b0
  where
  b0 : Chain (CCZ024 ∷ Bx0-2413 ∷ []) (Bx0-2413 ∷ CCZ024 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 2 2 (Bx0-1423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2413⟩ c4) ▸
       at 1 2 (Bx0-1423 ∷ CCZ014 ∷ []) (lem-Cz-beta-at243243 c4) ▸
       at 0 2 (Bx0-2413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1423⟩ c4) ▸
       at 1 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- Cz-beta @13243142: 7 steps
lem-Cz-beta-at13243142 : Complete 4 → ⟪ (CCZ034 ∷ Bx0-3412 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3412 ∷ CCZ034 ∷ []) ⟫ʷ
lem-Cz-beta-at13243142 c4 = run b0
  where
  b0 : Chain (CCZ034 ∷ Bx0-3412 ∷ []) (Bx0-3412 ∷ CCZ034 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 2 2 (Bx0-2413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3412⟩ c4) ▸
       at 1 2 (Bx0-2413 ∷ CCZ024 ∷ []) (lem-Cz-beta-at12243143 c4) ▸
       at 0 2 (Bx0-3412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·2413⟩ c4) ▸
       at 1 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym23 @243243: 5 steps
lem-sym23-at243243 : Complete 4 → ⟪ (Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1243 ∷ []) ⟫ʷ
lem-sym23-at243243 c4 = run b0
  where
  b0 : Chain (Bx0-1423 ∷ []) (Bx0-1243 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym23-at2332 c4) ▸
       at 0 2 (Bx0-1243 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1234⟩ c4) ▸
       at 1 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym23 @12243143: 5 steps
lem-sym23-at12243143 : Complete 4 → ⟪ (Bx0-2413 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2143 ∷ []) ⟫ʷ
lem-sym23-at12243143 c4 = run b0
  where
  b0 : Chain (Bx0-2413 ∷ []) (Bx0-2143 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2413⟩ c4) ▸
       at 1 1 (Bx0-1243 ∷ []) (lem-sym23-at243243 c4) ▸
       at 0 2 (Bx0-2143 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1243⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym23 @13243142: 5 steps
lem-sym23-at13243142 : Complete 4 → ⟪ (Bx0-3412 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3142 ∷ []) ⟫ʷ
lem-sym23-at13243142 c4 = run b0
  where
  b0 : Chain (Bx0-3412 ∷ []) (Bx0-3142 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-2413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3412⟩ c4) ▸
       at 1 1 (Bx0-2143 ∷ []) (lem-sym23-at12243143 c4) ▸
       at 0 2 (Bx0-3142 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·2143⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym34 @12213443: 5 steps
lem-sym34-at12213443 : Complete 4 → ⟪ (Bx0-2143 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ []) ⟫ʷ
lem-sym34-at12213443 c4 = run b0
  where
  b0 : Chain (Bx0-2143 ∷ []) (Bx0-2134 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1243 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2143⟩ c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym34-at3443 c4) ▸
       at 0 2 (Bx0-2134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1234⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym34 @13213442: 5 steps
lem-sym34-at13213442 : Complete 4 → ⟪ (Bx0-3142 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3124 ∷ []) ⟫ʷ
lem-sym34-at13213442 c4 = run b0
  where
  b0 : Chain (Bx0-3142 ∷ []) (Bx0-3124 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-2143 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3142⟩ c4) ▸
       at 1 1 (Bx0-2134 ∷ []) (lem-sym34-at12213443 c4) ▸
       at 0 2 (Bx0-3124 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·2134⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ034: 9 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ034 : Complete 4 → ⟪ (Bx0-1234 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ034 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-1234 ∷ CCZ034 ∷ []) (CCZ034 ∷ Bx0-1324 ∷ [])
  b0 = at 0 1 (Bx0-1324 ∷ []) (lem-sym23 c4) ▸
       at 0 1 (Bx0-1342 ∷ []) (lem-sym34-at2332 c4) ▸
       at 0 1 (Bx0-3142 ∷ []) (lem-sym12-at233442 c4) ▸
       at 0 1 (Bx0-3412 ∷ []) (lem-sym23-at13213442 c4) ▸
       at 0 2 (CCZ034 ∷ Bx0-3412 ∷ []) (sym (lem-Cz-beta-at13243142 c4)) ▸
       at 1 1 (Bx0-3142 ∷ []) (lem-sym23-at13243142 c4) ▸
       at 1 1 (Bx0-3124 ∷ []) (lem-sym34-at13213442 c4) ▸
       at 1 1 (Bx0-1324 ∷ []) (lem-sym12-at132132 c4) ▸ done

  b1 : Chain (CCZ034 ∷ Bx0-1324 ∷ []) (CCZ034 ∷ Bx0-1234 ∷ [])
  b1 = at 1 1 (Bx0-1234 ∷ []) (lem-sym23-at2332 c4) ▸ done


-- auto BOX(0;1234) | CCZ342: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ342 : Complete 4 → ⟪ (Bx0-1234 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ342 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ CCZ234 ∷ []) (CCZ234 ∷ Bx0-1234 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ []) (lw0 c4 (CCZ234 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx0-2134 ∷ []) (lem-sym12 c4) ▸
       at 0 1 (Bx0-2314 ∷ []) (lem-sym23-at1221 c4) ▸
       at 0 2 (CCZ234 ∷ Bx0-2314 ∷ []) (sym (lem-c124-beta-at122331 c4)) ▸
       at 1 1 (Bx0-2134 ∷ []) (lem-sym23-at122331 c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym12-at1221 c4) ▸
       at 0 1 (CCZ234 ∷ []) (lw0 c4 (CCZ234 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | TOFF012: 1 steps
lem-auto-BOX⟨0·1234⟩-∣-TOFF012 : Complete 4 → ⟪ (Bx0-1234 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-TOFF012 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ Toff012 ∷ []) (Toff012 ∷ Bx0-1234 ∷ [])
  b0 = at 0 2 (Toff012 ∷ Bx0-1234 ∷ []) (sym (lem-T-beta c4)) ▸ done


-- auto BOX(0;1234) | CCZ103: 5 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ103 : Complete 4 → ⟪ (Bx0-1234 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ103 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ CCZ013 ∷ []) (CCZ013 ∷ Bx0-1234 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ []) (lw4 c4 (CCZ013 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx0-1324 ∷ []) (lem-sym23 c4) ▸
       at 0 2 (CCZ013 ∷ Bx0-1324 ∷ []) (sym (lem-Cz-beta-at2332 c4)) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym23-at2332 c4) ▸
       at 0 1 (CCZ013 ∷ []) (lw4 c4 (CCZ013 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸ done


-- beta-T @122331: 8 steps
lem-beta-T-at122331 : Complete 4 → ⟪ (Bx0-2314 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ []) ⟫ʷ
lem-beta-T-at122331 c4 = run b0
  where
  b0 : Chain (Bx0-2314 ∷ []) (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1324 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2314⟩ c4) ▸
       at 1 1 (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) (lem-beta-T-at2332 c4) ▸
       at 0 2 (Toff023 ∷ Sw12 ∷ []) (lem-nat-1-TOFF013 c4) ▸
       at 1 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 2 2 (Toff023 ∷ Sw12 ∷ []) (lem-nat-1-TOFF013 c4) ▸
       at 3 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 4 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- beta-T @0110243243: 8 steps
lem-beta-T-at0110243243 : Complete 4 → ⟪ (Bx1-0423 ∷ []) ⟫ʷ ≈ ⟪ (Toff104 ∷ CCZ123 ∷ Toff104 ∷ CCZ123 ∷ []) ⟫ʷ
lem-beta-T-at0110243243 c4 = run b0
  where
  b0 : Chain (Bx1-0423 ∷ []) (Toff104 ∷ CCZ123 ∷ Toff104 ∷ CCZ123 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ c4) ▸
       at 1 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-beta-T-at243243 c4) ▸
       at 0 2 (Toff104 ∷ Sw01 ∷ []) (lem-nat-0-TOFF014 c4) ▸
       at 1 2 (CCZ123 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ023 ∷ []) (CCZ123 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff104 ∷ Sw01 ∷ []) (lem-nat-0-TOFF014 c4) ▸
       at 3 2 (CCZ123 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ023 ∷ []) (CCZ123 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym23 @0110243243: 5 steps
lem-sym23-at0110243243 : Complete 4 → ⟪ (Bx1-0423 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0243 ∷ []) ⟫ʷ
lem-sym23-at0110243243 c4 = run b0
  where
  b0 : Chain (Bx1-0423 ∷ []) (Bx1-0243 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ c4) ▸
       at 1 1 (Bx0-1243 ∷ []) (lem-sym23-at243243 c4) ▸
       at 0 2 (Bx1-0243 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1243⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym23 @011220: 5 steps
lem-sym23-at011220 : Complete 4 → ⟪ (Bx1-2034 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2304 ∷ []) ⟫ʷ
lem-sym23-at011220 c4 = run b0
  where
  b0 : Chain (Bx1-2034 ∷ []) (Bx1-2304 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-2134 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·2034⟩ c4) ▸
       at 1 1 (Bx0-2314 ∷ []) (lem-sym23-at1221 c4) ▸
       at 0 2 (Bx1-2304 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·2314⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- T312-beta @2332: 8 steps
lem-T312-beta-at2332 : Complete 4 → ⟪ (Toff213 ∷ Bx0-1324 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ CCZ134 ∷ []) ⟫ʷ
lem-T312-beta-at2332 c4 = run b0
  where
  b0 : Chain (Toff213 ∷ Bx0-1324 ∷ Toff213 ∷ []) (Bx0-1324 ∷ CCZ134 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff312 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff213 ∷ []) (Toff312 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ c4) ▸
       at 3 2 (Toff312 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff213 ∷ []) (Toff312 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Bx0-1234 ∷ CCZ124 ∷ []) (lem-T312-beta c4) ▸
       at 0 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ c4) ▸
       at 1 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- T312-beta @122331: 8 steps
lem-T312-beta-at122331 : Complete 4 → ⟪ (Toff123 ∷ Bx0-2314 ∷ Toff123 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2314 ∷ CCZ234 ∷ []) ⟫ʷ
lem-T312-beta-at122331 c4 = run b0
  where
  b0 : Chain (Toff123 ∷ Bx0-2314 ∷ Toff123 ∷ []) (Bx0-2314 ∷ CCZ234 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff213 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff123 ∷ []) (Toff213 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-1324 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2314⟩ c4) ▸
       at 3 2 (Toff213 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff123 ∷ []) (Toff213 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Bx0-1324 ∷ CCZ134 ∷ []) (lem-T312-beta-at2332 c4) ▸
       at 0 2 (Bx0-2314 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1324⟩ c4) ▸
       at 1 2 (CCZ234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ134 ∷ []) (CCZ234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- T312-beta @01122330: 8 steps
lem-T312-beta-at01122330 : Complete 4 → ⟪ (Toff023 ∷ Bx1-2304 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2304 ∷ CCZ234 ∷ []) ⟫ʷ
lem-T312-beta-at01122330 c4 = run b0
  where
  b0 : Chain (Toff023 ∷ Bx1-2304 ∷ Toff023 ∷ []) (Bx1-2304 ∷ CCZ234 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff123 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff023 ∷ []) (Toff123 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-2314 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·2304⟩ c4) ▸
       at 3 2 (Toff123 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff023 ∷ []) (Toff123 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Bx0-2314 ∷ CCZ234 ∷ []) (lem-T312-beta-at122331 c4) ▸
       at 0 2 (Bx1-2304 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·2314⟩ c4) ▸
       at 1 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym23 @01122330: 5 steps
lem-sym23-at01122330 : Complete 4 → ⟪ (Bx1-2304 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2034 ∷ []) ⟫ʷ
lem-sym23-at01122330 c4 = run b0
  where
  b0 : Chain (Bx1-2304 ∷ []) (Bx1-2034 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-2314 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·2304⟩ c4) ▸
       at 1 1 (Bx0-2134 ∷ []) (lem-sym23-at122331 c4) ▸
       at 0 2 (Bx1-2034 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·2134⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym34 @011220: 5 steps
lem-sym34-at011220 : Complete 4 → ⟪ (Bx1-2034 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2043 ∷ []) ⟫ʷ
lem-sym34-at011220 c4 = run b0
  where
  b0 : Chain (Bx1-2034 ∷ []) (Bx1-2043 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-2134 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·2034⟩ c4) ▸
       at 1 1 (Bx0-2143 ∷ []) (lem-sym34-at1221 c4) ▸
       at 0 2 (Bx1-2043 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·2143⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym12 @12213443: 5 steps
lem-sym12-at12213443 : Complete 4 → ⟪ (Bx0-2143 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1243 ∷ []) ⟫ʷ
lem-sym12-at12213443 c4 = run b0
  where
  b0 : Chain (Bx0-2143 ∷ []) (Bx0-1243 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1243 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2143⟩ c4) ▸
       at 1 1 (Bx0-2143 ∷ []) (lem-sym12-at3443 c4) ▸
       at 0 2 (Bx0-1243 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2143⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym12 @0112203443: 5 steps
lem-sym12-at0112203443 : Complete 4 → ⟪ (Bx1-2043 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0243 ∷ []) ⟫ʷ
lem-sym12-at0112203443 c4 = run b0
  where
  b0 : Chain (Bx1-2043 ∷ []) (Bx1-0243 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-2143 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·2043⟩ c4) ▸
       at 1 1 (Bx0-1243 ∷ []) (lem-sym12-at12213443 c4) ▸
       at 0 2 (Bx1-0243 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1243⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym23 @01103443: 5 steps
lem-sym23-at01103443 : Complete 4 → ⟪ (Bx1-0243 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0423 ∷ []) ⟫ʷ
lem-sym23-at01103443 c4 = run b0
  where
  b0 : Chain (Bx1-0243 ∷ []) (Bx1-0423 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1243 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0243⟩ c4) ▸
       at 1 1 (Bx0-1423 ∷ []) (lem-sym23-at3443 c4) ▸
       at 0 2 (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ034 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ034-at2332 : Complete 4 → ⟪ (Bx0-1324 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ034-at2332 c4 = run b0
  where
  b0 : Chain (Bx0-1324 ∷ CCZ024 ∷ []) (CCZ024 ∷ Bx0-1324 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ c4) ▸
       at 2 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 1 2 (CCZ034 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ034 c4) ▸
       at 0 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 1 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ034 @243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ034-at243243 : Complete 4 → ⟪ (Bx0-1423 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ Bx0-1423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ034-at243243 c4 = run b0
  where
  b0 : Chain (Bx0-1423 ∷ CCZ023 ∷ []) (CCZ023 ∷ Bx0-1423 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ c4) ▸
       at 2 2 (CCZ024 ∷ Sw34 ∷ []) (lem-nat-3-CCZ023 c4) ▸
       at 1 2 (CCZ024 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ034-at2332 c4) ▸
       at 0 2 (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 c4) ▸
       at 1 2 (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ034 @0110243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ034-at0110243243 : Complete 4 → ⟪ (Bx1-0423 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Bx1-0423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ034-at0110243243 c4 = run b0
  where
  b0 : Chain (Bx1-0423 ∷ CCZ123 ∷ []) (CCZ123 ∷ Bx1-0423 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ c4) ▸
       at 2 2 (CCZ023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ123 ∷ []) (CCZ023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ023 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ034-at243243 c4) ▸
       at 0 2 (CCZ123 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ023 ∷ []) (CCZ123 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done

