{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D005 where

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
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-CS12-beta ; lem-CSd12-beta ; lem-CX23-beta ; lem-sym12 ; lem-sym34)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-T312-beta-at14213243 ; lem-beta-inv-at0210243143 ; lem-c124-beta-at3443 ; lem-sym12-at0214203143 ; lem-sym12-at1221 ; lem-sym23-at0214203143 ; lem-sym23-at0214213043 ; lem-sym23-at1221 ; lem-sym34-at0214203143 ; lem-sym34-at03102132 ; lem-sym34-at14213243)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-beta-T-at0110243243 ; lem-c124-beta-at122331 ; lem-sym23-at01103443 ; lem-sym23-at122331 ; lem-sym23-at243243 ; lem-sym23-at3443 ; lem-sym34-at0310213442 ; lem-sym34-at3443)
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-BOXd-BOX-at0210243143 ; lem-beta-T-at031031 ; lem-sym12-at0210243143 ; lem-sym12-at03102132 ; lem-sym23-at0210243143 ; lem-sym23-at032032)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-1-CCZ024 ; lem-nat-1-CCZ034 ; lem-nat-2-BOX⟨0·1234⟩ ; lem-nat-2-BOX⟨0·1324⟩ ; lem-nat-3-BOX⟨0·1423⟩)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-1-CCZ014 ; lem-nat-3-BOX⟨0·1324⟩)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-0-CCZ024 ; lem-nat-0-CCZ124 ; lem-nat-2-CCZ124 ; lem-nat-2-CCZ134 ; lem-nat-2-TOFF204)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-0-CCZ014 ; lem-nat-1-TOFF104)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-0-CCZ034 ; lem-nat-0-CCZ134 ; lem-nat-0-TOFF304 ; lem-nat-0-TOFF314)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-0-BOX⟨0·4132⟩ ; lem-nat-1-BOX⟨1·4032⟩)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-nat-0-BOX⟨0·4123⟩ ; lem-nat-1-BOX⟨1·4023⟩ ; lem-nat-1-TOFF304)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-0-BOX⟨0·1423⟩ ; lem-nat-1-BOX⟨0·1324⟩ ; lem-nat-1-BOX⟨1·0423⟩)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-nat-0-BOX⟨1·0423⟩ ; lem-nat-0-BOX⟨2·4103⟩ ; lem-nat-1-BOX⟨2·0143⟩ ; lem-nat-1-BOX⟨2·0413⟩ ; lem-nat-2-BOX⟨2·0143⟩ ; lem-nat-2-BOX⟨2·0413⟩ ; lem-nat-2-BOX⟨3·0142⟩ ; lem-nat-2-BOX⟨3·0412⟩ ; lem-nat-3-CCZ123 ; lem-nat-3-CCZ124)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-nat-1-BOX⟨0·2314⟩)
open import Examples.Groups.Clifford+CS.Five.D.R013 using (lem-comm-CKd40-CCZ123 ; lem-nat-0-BOX⟨1·4032⟩ ; lem-nat-0-BOX⟨2·4031⟩ ; lem-nat-0-BOX⟨3·1204⟩ ; lem-nat-1-BOX⟨2·4031⟩ ; lem-nat-2-BOX⟨0·4123⟩ ; lem-nat-2-BOX⟨0·4132⟩ ; lem-nat-2-CS12 ; lem-nat-2-CS13 ; lem-nat-2-CSd12 ; lem-nat-2-CSd13 ; lem-nat-2-TOFF314 ; lem-nat-3-CS13 ; lem-nat-3-CS14 ; lem-nat-3-CSd13 ; lem-nat-3-CSd14)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-nat-0-BOX⟨2·0413⟩ ; lem-nat-0-BOX⟨2·1403⟩ ; lem-nat-0-BOX⟨2·4013⟩ ; lem-nat-0-BOX⟨2·4130⟩ ; lem-nat-0-CS04 ; lem-nat-0-CS14 ; lem-nat-0-CX40 ; lem-nat-0-SBOX⟨0·1·42·3⟩ ; lem-nat-0-SBOX⟨1·0·42·3⟩ ; lem-nat-1-CS04 ; lem-nat-1-SBOX⟨1·0·42·3⟩ ; lem-nat-1-SBOX⟨2·0·41·3⟩ ; lem-nat-2-SBOX⟨0·1·23·4⟩ ; lem-nat-2-SBOX⟨0·1·32·4⟩ ; lem-nat-3-CS23 ; lem-nat-3-CS24 ; lem-nat-3-CX42 ; lem-nat-3-SBOX⟨0·1·32·4⟩ ; lem-nat-3-SBOX⟨0·1·42·3⟩)
-- beta-T @0330: 8 steps
lem-beta-T-at0330 : Complete 4 → ⟪ (Bx3-1204 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ []) ⟫ʷ
lem-beta-T-at0330 c4 = run b0
  where
  b0 : Chain (Bx3-1204 ∷ []) (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-0214 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1204⟩ c4) ▸
       at 1 1 (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ []) (lem-beta-T-at031031 c4) ▸
       at 0 2 (Toff312 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff302 ∷ []) (Toff312 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 2 2 (Toff312 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff302 ∷ []) (Toff312 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 4 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- KB-form: 7 steps
lem-KB-form : Complete 4 → ⟪ (K0 ∷ Bx3-0124 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ []) ⟫ʷ
lem-KB-form c4 = run b0
  where
  b0 : Chain (K0 ∷ Bx3-0124 ∷ K0⁻ ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ [])
  b0 = at 1 1 (Bx3-1024 ∷ []) (lem-sym12-at03102132 c4) ▸
       at 1 1 (Bx3-1204 ∷ []) (lem-sym23-at032032 c4) ▸
       at 1 1 (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ []) (lem-beta-T-at0330 c4) ▸
       at 0 2 (Toff312 ∷ K0 ∷ []) (c₁ (K) (Toffᵗ)) ▸
       at 1 2 (Toff034 ∷ K0 ∷ []) (pw1 c4 (K0 ∷ CCZ034 ∷ []) (Toff034 ∷ K0 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff312 ∷ K0 ∷ []) (c₁ (K) (Toffᵗ)) ▸
       at 3 3 (Toff034 ∷ []) (pw1 c4 (K0 ∷ CCZ034 ∷ K0⁻ ∷ []) (Toff034 ∷ []) tt tt Eq.refl) ▸ done


-- sym23 @0210213443: 5 steps
lem-sym23-at0210213443 : Complete 4 → ⟪ (Bx2-0143 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ []) ⟫ʷ
lem-sym23-at0210213443 c4 = run b0
  where
  b0 : Chain (Bx2-0143 ∷ []) (Bx2-0413 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-0243 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0143⟩ c4) ▸
       at 1 1 (Bx1-0423 ∷ []) (lem-sym23-at01103443 c4) ▸
       at 0 2 (Bx2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0423⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym23 @0310213442: 5 steps
lem-sym23-at0310213442 : Complete 4 → ⟪ (Bx3-0142 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ []) ⟫ʷ
lem-sym23-at0310213442 c4 = run b0
  where
  b0 : Chain (Bx3-0142 ∷ []) (Bx3-0412 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx2-0143 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0142⟩ c4) ▸
       at 1 1 (Bx2-0413 ∷ []) (lem-sym23-at0210213443 c4) ▸
       at 0 2 (Bx3-0412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0413⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- beta-T @0210243143: 8 steps
lem-beta-T-at0210243143 : Complete 4 → ⟪ (Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) ⟫ʷ
lem-beta-T-at0210243143 c4 = run b0
  where
  b0 : Chain (Bx2-0413 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ c4) ▸
       at 1 1 (Toff104 ∷ CCZ123 ∷ Toff104 ∷ CCZ123 ∷ []) (lem-beta-T-at0110243243 c4) ▸
       at 0 2 (Toff204 ∷ Sw12 ∷ []) (lem-nat-1-TOFF104 c4) ▸
       at 1 2 (CCZ123 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff204 ∷ Sw12 ∷ []) (lem-nat-1-TOFF104 c4) ▸
       at 3 2 (CCZ123 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- beta-T @0310243142: 8 steps
lem-beta-T-at0310243142 : Complete 4 → ⟪ (Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) ⟫ʷ
lem-beta-T-at0310243142 c4 = run b0
  where
  b0 : Chain (Bx3-0412 ∷ []) (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx2-0413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0412⟩ c4) ▸
       at 1 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4) ▸
       at 0 2 (Toff304 ∷ Sw23 ∷ []) (lem-nat-2-TOFF204 c4) ▸
       at 1 2 (CCZ123 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff304 ∷ Sw23 ∷ []) (lem-nat-2-TOFF204 c4) ▸
       at 3 2 (CCZ123 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym23 @0310243142: 5 steps
lem-sym23-at0310243142 : Complete 4 → ⟪ (Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0142 ∷ []) ⟫ʷ
lem-sym23-at0310243142 c4 = run b0
  where
  b0 : Chain (Bx3-0412 ∷ []) (Bx3-0142 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx2-0413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0412⟩ c4) ▸
       at 1 1 (Bx2-0143 ∷ []) (lem-sym23-at0210243143 c4) ▸
       at 0 2 (Bx3-0142 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0143⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- CKbox: 17 steps
lem-CKbox : Complete 4 → ⟪ (CK40 ∷ Bx3-0124 ∷ CK40 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ Bx3-0124 ∷ K0⁻ ∷ []) ⟫ʷ
lem-CKbox c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CK40 ∷ Bx3-0124 ∷ CK40 ∷ S4 ∷ []) (K0 ∷ Toff304 ∷ X4 ∷ CCZ123 ∷ CK40⁻ ∷ X4 ∷ Toff304 ∷ CCZ123 ∷ K0 ∷ X4 ∷ CK40⁻ ∷ X4 ∷ S4 ∷ [])
  b0 = at 0 1 (K0 ∷ X4 ∷ CK40⁻ ∷ X4 ∷ []) (pw1 c4 (CK40 ∷ []) (K0 ∷ X4 ∷ CK40⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (K0 ∷ X4 ∷ CK40⁻ ∷ X4 ∷ []) (pw1 c4 (CK40 ∷ []) (K0 ∷ X4 ∷ CK40⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Bx3-0142 ∷ []) (lem-sym34-at03102132 c4) ▸
       at 4 1 (Bx3-0412 ∷ []) (lem-sym23-at0310213442 c4) ▸
       at 4 1 (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) (lem-beta-T-at0310243142 c4) ▸
       at 1 4 (Toff304 ∷ X4 ∷ CK40⁻ ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CK40⁻ ∷ X4 ∷ Toff304 ∷ []) (Toff304 ∷ X4 ∷ CK40⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ123 ∷ X4 ∷ []) (sym (c₄ (CCZ ↑) (X))) ▸
       at 3 2 (CCZ123 ∷ CK40⁻ ∷ []) (lem-comm-CKd40-CCZ123 c4) ▸ done

  b1 : Chain (K0 ∷ Toff304 ∷ X4 ∷ CCZ123 ∷ CK40⁻ ∷ X4 ∷ Toff304 ∷ CCZ123 ∷ K0 ∷ X4 ∷ CK40⁻ ∷ X4 ∷ S4 ∷ []) (K0 ∷ Bx3-0124 ∷ X4 ∷ CK40⁻ ∷ X4 ∷ K0 ∷ X4 ∷ CK40⁻ ∷ X4 ∷ S4 ∷ [])
  b1 = at 2 2 (CCZ123 ∷ X4 ∷ []) (sym (c₄ (CCZ ↑) (X))) ▸
       at 3 4 (Toff304 ∷ X4 ∷ CK40⁻ ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CK40⁻ ∷ X4 ∷ Toff304 ∷ []) (Toff304 ∷ X4 ∷ CK40⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ123 ∷ X4 ∷ []) (sym (c₄ (CCZ ↑) (X))) ▸
       at 5 2 (CCZ123 ∷ CK40⁻ ∷ []) (lem-comm-CKd40-CCZ123 c4) ▸
       at 4 2 (CCZ123 ∷ X4 ∷ []) (sym (c₄ (CCZ ↑) (X))) ▸
       at 1 4 (Bx3-0412 ∷ []) (sym (lem-beta-T-at0310243142 c4)) ▸
       at 1 1 (Bx3-0142 ∷ []) (lem-sym23-at0310243142 c4) ▸
       at 1 1 (Bx3-0124 ∷ []) (lem-sym34-at0310213442 c4) ▸ done

  b2 : Chain (K0 ∷ Bx3-0124 ∷ X4 ∷ CK40⁻ ∷ X4 ∷ K0 ∷ X4 ∷ CK40⁻ ∷ X4 ∷ S4 ∷ []) (K0 ∷ Bx3-0124 ∷ K0⁻ ∷ [])
  b2 = at 2 8 (K0⁻ ∷ []) (pw1 c4 (X4 ∷ CK40⁻ ∷ X4 ∷ K0 ∷ X4 ∷ CK40⁻ ∷ X4 ∷ S4 ∷ []) (K0⁻ ∷ []) tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ231: 5 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ231 : Complete 4 → ⟪ (Bx0-1234 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ231 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ CCZ123 ∷ []) (CCZ123 ∷ Bx0-1234 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ []) (lw4 c4 (CCZ123 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx0-1243 ∷ []) (lem-sym34 c4) ▸
       at 0 2 (CCZ123 ∷ Bx0-1243 ∷ []) (sym (lem-c124-beta-at3443 c4)) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym34-at3443 c4) ▸
       at 0 1 (CCZ123 ∷ []) (lw4 c4 (CCZ123 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸ done


-- CS12-beta @2332: 7 steps
lem-CS12-beta-at2332 : Complete 4 → ⟪ (CS13 ∷ Bx0-1324 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ CS13 ∷ []) ⟫ʷ
lem-CS12-beta-at2332 c4 = run b0
  where
  b0 : Chain (CS13 ∷ Bx0-1324 ∷ []) (Bx0-1324 ∷ CS13 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS12 ∷ Sw23 ∷ []) (lem-nat-2-CS13 c4) ▸
       at 2 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ c4) ▸
       at 1 2 (Bx0-1234 ∷ CS12 ∷ []) (lem-CS12-beta c4) ▸
       at 0 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ c4) ▸
       at 1 2 (CS13 ∷ Sw23 ∷ []) (lem-nat-2-CS12 c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- CS12-beta @243243: 7 steps
lem-CS12-beta-at243243 : Complete 4 → ⟪ (CS14 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ CS14 ∷ []) ⟫ʷ
lem-CS12-beta-at243243 c4 = run b0
  where
  b0 : Chain (CS14 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ CS14 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS13 ∷ Sw34 ∷ []) (lem-nat-3-CS14 c4) ▸
       at 2 2 (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ c4) ▸
       at 1 2 (Bx0-1324 ∷ CS13 ∷ []) (lem-CS12-beta-at2332 c4) ▸
       at 0 2 (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ c4) ▸
       at 1 2 (CS14 ∷ Sw34 ∷ []) (lem-nat-3-CS13 c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CS14: 5 steps
lem-auto-BOX⟨0·1234⟩-∣-CS14 : Complete 4 → ⟪ (Bx0-1234 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS14 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ CS14 ∷ []) (CS14 ∷ Bx0-1234 ∷ [])
  b0 = at 0 1 (Bx0-1243 ∷ []) (lem-sym34 c4) ▸
       at 0 1 (Bx0-1423 ∷ []) (lem-sym23-at3443 c4) ▸
       at 0 2 (CS14 ∷ Bx0-1423 ∷ []) (sym (lem-CS12-beta-at243243 c4)) ▸
       at 1 1 (Bx0-1243 ∷ []) (lem-sym23-at243243 c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym34-at3443 c4) ▸ done


-- CSd12-beta @2332: 7 steps
lem-CSd12-beta-at2332 : Complete 4 → ⟪ (CS13⁻ ∷ Bx0-1324 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-CSd12-beta-at2332 c4 = run b0
  where
  b0 : Chain (CS13⁻ ∷ Bx0-1324 ∷ []) (Bx0-1324 ∷ CS13⁻ ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS12⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd13 c4) ▸
       at 2 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ c4) ▸
       at 1 2 (Bx0-1234 ∷ CS12⁻ ∷ []) (lem-CSd12-beta c4) ▸
       at 0 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ c4) ▸
       at 1 2 (CS13⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd12 c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- CSd12-beta @243243: 7 steps
lem-CSd12-beta-at243243 : Complete 4 → ⟪ (CS14⁻ ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ CS14⁻ ∷ []) ⟫ʷ
lem-CSd12-beta-at243243 c4 = run b0
  where
  b0 : Chain (CS14⁻ ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ CS14⁻ ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS13⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd14 c4) ▸
       at 2 2 (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ c4) ▸
       at 1 2 (Bx0-1324 ∷ CS13⁻ ∷ []) (lem-CSd12-beta-at2332 c4) ▸
       at 0 2 (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ c4) ▸
       at 1 2 (CS14⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd13 c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CSd14: 5 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd14 : Complete 4 → ⟪ (Bx0-1234 ∷ CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS14⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd14 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ Bx0-1234 ∷ [])
  b0 = at 0 1 (Bx0-1243 ∷ []) (lem-sym34 c4) ▸
       at 0 1 (Bx0-1423 ∷ []) (lem-sym23-at3443 c4) ▸
       at 0 2 (CS14⁻ ∷ Bx0-1423 ∷ []) (sym (lem-CSd12-beta-at243243 c4)) ▸
       at 1 1 (Bx0-1243 ∷ []) (lem-sym23-at243243 c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym34-at3443 c4) ▸ done


-- sym34 @0214213043: 5 steps
lem-sym34-at0214213043 : Complete 4 → ⟪ (Bx2-4103 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4130 ∷ []) ⟫ʷ
lem-sym34-at0214213043 c4 = run b0
  where
  b0 : Chain (Bx2-4103 ∷ []) (Bx2-4130 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx2-4013 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·4103⟩ c4) ▸
       at 1 1 (Bx2-4031 ∷ []) (lem-sym34-at0214203143 c4) ▸
       at 0 2 (Bx2-4130 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·4031⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- T312-beta @142142: 8 steps
lem-T312-beta-at142142 : Complete 4 → ⟪ (Toff314 ∷ Bx0-4132 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4132 ∷ CCZ124 ∷ []) ⟫ʷ
lem-T312-beta-at142142 c4 = run b0
  where
  b0 : Chain (Toff314 ∷ Bx0-4132 ∷ Toff314 ∷ []) (Bx0-4132 ∷ CCZ124 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff214 ∷ Sw23 ∷ []) (lem-nat-2-TOFF314 c4) ▸
       at 2 2 (Bx0-4123 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·4132⟩ c4) ▸
       at 3 2 (Toff214 ∷ Sw23 ∷ []) (lem-nat-2-TOFF314 c4) ▸
       at 1 3 (Bx0-4123 ∷ CCZ134 ∷ []) (lem-T312-beta-at14213243 c4) ▸
       at 0 2 (Bx0-4132 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·4123⟩ c4) ▸
       at 1 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- T312-beta @01142042: 8 steps
lem-T312-beta-at01142042 : Complete 4 → ⟪ (Toff304 ∷ Bx1-4032 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-4032 ∷ CCZ024 ∷ []) ⟫ʷ
lem-T312-beta-at01142042 c4 = run b0
  where
  b0 : Chain (Toff304 ∷ Bx1-4032 ∷ Toff304 ∷ []) (Bx1-4032 ∷ CCZ024 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff314 ∷ Sw01 ∷ []) (lem-nat-0-TOFF304 c4) ▸
       at 2 2 (Bx0-4132 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·4032⟩ c4) ▸
       at 3 2 (Toff314 ∷ Sw01 ∷ []) (lem-nat-0-TOFF304 c4) ▸
       at 1 3 (Bx0-4132 ∷ CCZ124 ∷ []) (lem-T312-beta-at142142 c4) ▸
       at 0 2 (Bx1-4032 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·4132⟩ c4) ▸
       at 1 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- T312-beta @02142041: 8 steps
lem-T312-beta-at02142041 : Complete 4 → ⟪ (Toff304 ∷ Bx2-4031 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4031 ∷ CCZ014 ∷ []) ⟫ʷ
lem-T312-beta-at02142041 c4 = run b0
  where
  b0 : Chain (Toff304 ∷ Bx2-4031 ∷ Toff304 ∷ []) (Bx2-4031 ∷ CCZ014 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff304 ∷ Sw12 ∷ []) (lem-nat-1-TOFF304 c4) ▸
       at 2 2 (Bx1-4032 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·4031⟩ c4) ▸
       at 3 2 (Toff304 ∷ Sw12 ∷ []) (lem-nat-1-TOFF304 c4) ▸
       at 1 3 (Bx1-4032 ∷ CCZ024 ∷ []) (lem-T312-beta-at01142042 c4) ▸
       at 0 2 (Bx2-4031 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·4032⟩ c4) ▸
       at 1 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- T312-beta @02142140: 8 steps
lem-T312-beta-at02142140 : Complete 4 → ⟪ (Toff314 ∷ Bx2-4130 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4130 ∷ CCZ014 ∷ []) ⟫ʷ
lem-T312-beta-at02142140 c4 = run b0
  where
  b0 : Chain (Toff314 ∷ Bx2-4130 ∷ Toff314 ∷ []) (Bx2-4130 ∷ CCZ014 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff304 ∷ Sw01 ∷ []) (lem-nat-0-TOFF314 c4) ▸
       at 2 2 (Bx2-4031 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·4130⟩ c4) ▸
       at 3 2 (Toff304 ∷ Sw01 ∷ []) (lem-nat-0-TOFF314 c4) ▸
       at 1 3 (Bx2-4031 ∷ CCZ014 ∷ []) (lem-T312-beta-at02142041 c4) ▸
       at 0 2 (Bx2-4130 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·4031⟩ c4) ▸
       at 1 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym34 @142142: 5 steps
lem-sym34-at142142 : Complete 4 → ⟪ (Bx0-4132 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4123 ∷ []) ⟫ʷ
lem-sym34-at142142 c4 = run b0
  where
  b0 : Chain (Bx0-4132 ∷ []) (Bx0-4123 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-4123 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·4132⟩ c4) ▸
       at 1 1 (Bx0-4132 ∷ []) (lem-sym34-at14213243 c4) ▸
       at 0 2 (Bx0-4123 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·4132⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym34 @01142042: 5 steps
lem-sym34-at01142042 : Complete 4 → ⟪ (Bx1-4032 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-4023 ∷ []) ⟫ʷ
lem-sym34-at01142042 c4 = run b0
  where
  b0 : Chain (Bx1-4032 ∷ []) (Bx1-4023 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-4132 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·4032⟩ c4) ▸
       at 1 1 (Bx0-4123 ∷ []) (lem-sym34-at142142 c4) ▸
       at 0 2 (Bx1-4023 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·4123⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym34 @02142041: 5 steps
lem-sym34-at02142041 : Complete 4 → ⟪ (Bx2-4031 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4013 ∷ []) ⟫ʷ
lem-sym34-at02142041 c4 = run b0
  where
  b0 : Chain (Bx2-4031 ∷ []) (Bx2-4013 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-4032 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·4031⟩ c4) ▸
       at 1 1 (Bx1-4023 ∷ []) (lem-sym34-at01142042 c4) ▸
       at 0 2 (Bx2-4013 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·4023⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym34 @02142140: 5 steps
lem-sym34-at02142140 : Complete 4 → ⟪ (Bx2-4130 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4103 ∷ []) ⟫ʷ
lem-sym34-at02142140 c4 = run b0
  where
  b0 : Chain (Bx2-4130 ∷ []) (Bx2-4103 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx2-4031 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·4130⟩ c4) ▸
       at 1 1 (Bx2-4013 ∷ []) (lem-sym34-at02142041 c4) ▸
       at 0 2 (Bx2-4103 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·4013⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ231 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at2332 : Complete 4 → ⟪ (Bx0-1324 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at2332 c4 = run b0
  where
  b0 : Chain (Bx0-1324 ∷ CCZ123 ∷ []) (CCZ123 ∷ Bx0-1324 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ c4) ▸
       at 2 2 (CCZ123 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ123 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231 c4) ▸
       at 0 2 (CCZ123 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ231 @243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at243243 : Complete 4 → ⟪ (Bx0-1423 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Bx0-1423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at243243 c4 = run b0
  where
  b0 : Chain (Bx0-1423 ∷ CCZ124 ∷ []) (CCZ124 ∷ Bx0-1423 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ c4) ▸
       at 2 2 (CCZ123 ∷ Sw34 ∷ []) (lem-nat-3-CCZ124 c4) ▸
       at 1 2 (CCZ123 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at2332 c4) ▸
       at 0 2 (CCZ124 ∷ Sw34 ∷ []) (lem-nat-3-CCZ123 c4) ▸
       at 1 2 (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ231 @0110243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0110243243 : Complete 4 → ⟪ (Bx1-0423 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Bx1-0423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0110243243 c4 = run b0
  where
  b0 : Chain (Bx1-0423 ∷ CCZ024 ∷ []) (CCZ024 ∷ Bx1-0423 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ c4) ▸
       at 2 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 1 2 (CCZ124 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at243243 c4) ▸
       at 0 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 1 2 (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ231 @0210243143: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0210243143 : Complete 4 → ⟪ (Bx2-0413 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ Bx2-0413 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0210243143 c4 = run b0
  where
  b0 : Chain (Bx2-0413 ∷ CCZ014 ∷ []) (CCZ014 ∷ Bx2-0413 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ c4) ▸
       at 2 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 1 2 (CCZ024 ∷ Bx1-0423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0110243243 c4) ▸
       at 0 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 1 2 (Bx2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0423⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CS14 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS14-at2332 : Complete 4 → ⟪ (Bx0-1324 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS14-at2332 c4 = run b0
  where
  b0 : Chain (Bx0-1324 ∷ CS14 ∷ []) (CS14 ∷ Bx0-1324 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ c4) ▸
       at 2 2 (CS14 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS14 ∷ []) (CS14 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS14 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS14 c4) ▸
       at 0 2 (CS14 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS14 ∷ []) (CS14 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CS14 @243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS14-at243243 : Complete 4 → ⟪ (Bx0-1423 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Bx0-1423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS14-at243243 c4 = run b0
  where
  b0 : Chain (Bx0-1423 ∷ CS13 ∷ []) (CS13 ∷ Bx0-1423 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ c4) ▸
       at 2 2 (CS14 ∷ Sw34 ∷ []) (lem-nat-3-CS13 c4) ▸
       at 1 2 (CS14 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS14-at2332 c4) ▸
       at 0 2 (CS13 ∷ Sw34 ∷ []) (lem-nat-3-CS14 c4) ▸
       at 1 2 (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CS14 @0110243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS14-at0110243243 : Complete 4 → ⟪ (Bx1-0423 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Bx1-0423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS14-at0110243243 c4 = run b0
  where
  b0 : Chain (Bx1-0423 ∷ CS03 ∷ []) (CS03 ∷ Bx1-0423 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ c4) ▸
       at 2 2 (CS13 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS03 ∷ []) (CS13 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS13 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS14-at243243 c4) ▸
       at 0 2 (CS03 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS13 ∷ []) (CS03 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CS14 @0210243143: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS14-at0210243143 : Complete 4 → ⟪ (Bx2-0413 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Bx2-0413 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS14-at0210243143 c4 = run b0
  where
  b0 : Chain (Bx2-0413 ∷ CS03 ∷ []) (CS03 ∷ Bx2-0413 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ c4) ▸
       at 2 2 (CS03 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS03 ∷ []) (CS03 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS03 ∷ Bx1-0423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS14-at0110243243 c4) ▸
       at 0 2 (CS03 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS03 ∷ []) (CS03 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0423⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CSd14 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd14-at2332 : Complete 4 → ⟪ (Bx0-1324 ∷ CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS14⁻ ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd14-at2332 c4 = run b0
  where
  b0 : Chain (Bx0-1324 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ Bx0-1324 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ c4) ▸
       at 2 2 (CS14⁻ ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS14⁻ ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd14 c4) ▸
       at 0 2 (CS14⁻ ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CSd14 @243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd14-at243243 : Complete 4 → ⟪ (Bx0-1423 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ Bx0-1423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd14-at243243 c4 = run b0
  where
  b0 : Chain (Bx0-1423 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ Bx0-1423 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ c4) ▸
       at 2 2 (CS14⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd13 c4) ▸
       at 1 2 (CS14⁻ ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd14-at2332 c4) ▸
       at 0 2 (CS13⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd14 c4) ▸
       at 1 2 (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CSd14 @0110243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd14-at0110243243 : Complete 4 → ⟪ (Bx1-0423 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ Bx1-0423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd14-at0110243243 c4 = run b0
  where
  b0 : Chain (Bx1-0423 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ Bx1-0423 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ c4) ▸
       at 2 2 (CS13⁻ ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS03⁻ ∷ []) (CS13⁻ ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS13⁻ ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd14-at243243 c4) ▸
       at 0 2 (CS03⁻ ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS13⁻ ∷ []) (CS03⁻ ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CSd14 @0210243143: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd14-at0210243143 : Complete 4 → ⟪ (Bx2-0413 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ Bx2-0413 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd14-at0210243143 c4 = run b0
  where
  b0 : Chain (Bx2-0413 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ Bx2-0413 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ c4) ▸
       at 2 2 (CS03⁻ ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS03⁻ ∷ Bx1-0423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd14-at0110243243 c4) ▸
       at 0 2 (CS03⁻ ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0423⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- SB2: 31 steps
lem-SB2 : Complete 4 → ⟪ (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ []) ⟫ʷ
lem-SB2 c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ []) (Toff314 ∷ Toff314 ∷ Bx2-4013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b0 = at 0 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 2 1 (CS03 ∷ []) (refl) ▸
       at 4 1 (CS03⁻ ∷ []) (refl) ▸
       at 5 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 7 1 (CS03 ∷ []) (refl) ▸
       at 9 1 (CS03⁻ ∷ []) (refl) ▸
       at 0 0 (Toff314 ∷ Toff314 ∷ []) (lw0 c4 [] (Toff314 ∷ Toff314 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Bx2-4013 ∷ []) (lem-sym12-at0210243143 c4) ▸ done

  b1 : Chain (Toff314 ∷ Toff314 ∷ Bx2-4013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Toff314 ∷ CCZ014 ∷ CS03 ∷ Bx2-0413 ∷ Toff314 ∷ CS03⁻ ∷ Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b1 = at 2 1 (Bx2-4103 ∷ []) (lem-sym23-at0214203143 c4) ▸
       at 2 1 (Bx2-4130 ∷ []) (lem-sym34-at0214213043 c4) ▸
       at 1 3 (Bx2-4130 ∷ CCZ014 ∷ []) (lem-T312-beta-at02142140 c4) ▸
       at 1 1 (Bx2-4103 ∷ []) (lem-sym34-at02142140 c4) ▸
       at 1 1 (Bx2-4013 ∷ []) (lem-sym23-at0214213043 c4) ▸
       at 1 1 (Bx2-0413 ∷ []) (lem-sym12-at0214203143 c4) ▸
       at 1 2 (CCZ014 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0210243143 c4) ▸
       at 2 2 (CS03 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS14-at0210243143 c4) ▸ done

  b2 : Chain (Toff314 ∷ CCZ014 ∷ CS03 ∷ Bx2-0413 ∷ Toff314 ∷ CS03⁻ ∷ Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Toff314 ∷ CCZ014 ∷ CS03 ∷ Toff314 ∷ Bx2-0413 ∷ CCZ014 ∷ CS03⁻ ∷ Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b2 = at 3 0 (Toff314 ∷ Toff314 ∷ []) (lw0 c4 [] (Toff314 ∷ Toff314 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Bx2-4013 ∷ []) (lem-sym12-at0210243143 c4) ▸
       at 5 1 (Bx2-4103 ∷ []) (lem-sym23-at0214203143 c4) ▸
       at 5 1 (Bx2-4130 ∷ []) (lem-sym34-at0214213043 c4) ▸
       at 4 3 (Bx2-4130 ∷ CCZ014 ∷ []) (lem-T312-beta-at02142140 c4) ▸
       at 4 1 (Bx2-4103 ∷ []) (lem-sym34-at02142140 c4) ▸
       at 4 1 (Bx2-4013 ∷ []) (lem-sym23-at0214213043 c4) ▸
       at 4 1 (Bx2-0413 ∷ []) (lem-sym12-at0214203143 c4) ▸ done

  b3 : Chain (Toff314 ∷ CCZ014 ∷ CS03 ∷ Toff314 ∷ Bx2-0413 ∷ CCZ014 ∷ CS03⁻ ∷ Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (CCZ014 ∷ [])
  b3 = at 4 2 (CCZ014 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0210243143 c4) ▸
       at 5 2 (CS03⁻ ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd14-at0210243143 c4) ▸
       at 0 2 (CCZ014 ∷ Toff314 ∷ []) (pw2 c4 (Toff314 ∷ CCZ014 ∷ []) (CCZ014 ∷ Toff314 ∷ []) tt tt Eq.refl) ▸
       at 1 4 (CCZ014 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ []) (pw2 c4 (Toff314 ∷ CS03 ∷ Toff314 ∷ CCZ014 ∷ []) (CCZ014 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ []) tt tt Eq.refl) ▸
       at 0 2 [] (pw2 c4 (CCZ014 ∷ CCZ014 ∷ []) [] tt tt Eq.refl) ▸
       at 4 2 [] (lem-beta-inv-at0210243143 c4) ▸
       at 0 8 (CCZ014 ∷ []) (pw2 c4 (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (CCZ014 ∷ []) tt tt Eq.refl) ▸ done


-- SB2d: 33 steps
lem-SB2d : Complete 4 → ⟪ (Sb⁻2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ []) ⟫ʷ
lem-SB2d c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (run b4))))
  where
  b0 : Chain (Sb⁻2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ []) (CS03 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ Bx2-0413 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ Bx2-0413 ∷ [])
  b0 = at 0 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) (refl) ▸
       at 0 1 (CS03 ∷ []) (refl) ▸
       at 2 1 (CS03⁻ ∷ []) (refl) ▸
       at 4 1 (Bx2-0413 ∷ []) (lem-BOXd-BOX-at0210243143 c4) ▸
       at 5 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) (refl) ▸
       at 5 1 (CS03 ∷ []) (refl) ▸
       at 7 1 (CS03⁻ ∷ []) (refl) ▸
       at 9 1 (Bx2-0413 ∷ []) (lem-BOXd-BOX-at0210243143 c4) ▸ done

  b1 : Chain (CS03 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ Bx2-0413 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ Bx2-0413 ∷ []) (CS03 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ Bx2-4013 ∷ CCZ014 ∷ CS03⁻ ∷ Toff314 ∷ Bx2-0413 ∷ [])
  b1 = at 4 2 (CS03 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS14-at0210243143 c4) ▸
       at 5 0 (Toff314 ∷ Toff314 ∷ []) (lw0 c4 [] (Toff314 ∷ Toff314 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (Bx2-4013 ∷ []) (lem-sym12-at0210243143 c4) ▸
       at 7 1 (Bx2-4103 ∷ []) (lem-sym23-at0214203143 c4) ▸
       at 7 1 (Bx2-4130 ∷ []) (lem-sym34-at0214213043 c4) ▸
       at 6 3 (Bx2-4130 ∷ CCZ014 ∷ []) (lem-T312-beta-at02142140 c4) ▸
       at 6 1 (Bx2-4103 ∷ []) (lem-sym34-at02142140 c4) ▸
       at 6 1 (Bx2-4013 ∷ []) (lem-sym23-at0214213043 c4) ▸ done

  b2 : Chain (CS03 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ Bx2-4013 ∷ CCZ014 ∷ CS03⁻ ∷ Toff314 ∷ Bx2-0413 ∷ []) (CS03 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CCZ014 ∷ CS03⁻ ∷ Toff314 ∷ Bx2-4130 ∷ CCZ014 ∷ Bx2-0413 ∷ [])
  b2 = at 6 1 (Bx2-0413 ∷ []) (lem-sym12-at0214203143 c4) ▸
       at 6 2 (CCZ014 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0210243143 c4) ▸
       at 7 2 (CS03⁻ ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd14-at0210243143 c4) ▸
       at 8 0 (Toff314 ∷ Toff314 ∷ []) (lw0 c4 [] (Toff314 ∷ Toff314 ∷ []) tt tt Eq.refl) ▸
       at 10 1 (Bx2-4013 ∷ []) (lem-sym12-at0210243143 c4) ▸
       at 10 1 (Bx2-4103 ∷ []) (lem-sym23-at0214203143 c4) ▸
       at 10 1 (Bx2-4130 ∷ []) (lem-sym34-at0214213043 c4) ▸
       at 9 3 (Bx2-4130 ∷ CCZ014 ∷ []) (lem-T312-beta-at02142140 c4) ▸ done

  b3 : Chain (CS03 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CCZ014 ∷ CS03⁻ ∷ Toff314 ∷ Bx2-4130 ∷ CCZ014 ∷ Bx2-0413 ∷ []) (CS03 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ [])
  b3 = at 9 1 (Bx2-4103 ∷ []) (lem-sym34-at02142140 c4) ▸
       at 9 1 (Bx2-4013 ∷ []) (lem-sym23-at0214213043 c4) ▸
       at 9 1 (Bx2-0413 ∷ []) (lem-sym12-at0214203143 c4) ▸
       at 9 2 (CCZ014 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0210243143 c4) ▸
       at 4 3 (CCZ014 ∷ CS03 ∷ Toff314 ∷ []) (pw2 c4 (CS03 ∷ Toff314 ∷ CCZ014 ∷ []) (CCZ014 ∷ CS03 ∷ Toff314 ∷ []) tt tt Eq.refl) ▸
       at 5 5 (CCZ014 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ []) (pw2 c4 (CS03 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ CCZ014 ∷ []) (CCZ014 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (pw2 c4 (CCZ014 ∷ CCZ014 ∷ []) [] tt tt Eq.refl) ▸
       at 8 2 [] (lem-beta-inv-at0210243143 c4) ▸ done

  b4 : Chain (CS03 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ []) (CCZ014 ∷ [])
  b4 = at 0 8 (CCZ014 ∷ []) (pw2 c4 (CS03 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ []) (CCZ014 ∷ []) tt tt Eq.refl) ▸ done


-- F1 order-CS [nf of rhs]: 0 steps
lem-F1-order-CS-nf-of-rhs : Complete 4 → ⟪ [] ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-F1-order-CS-nf-of-rhs c4 = refl

-- F1 order-CS: 4 steps
lem-F1-order-CS : Complete 4 → ⟪ (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-F1-order-CS c4 = run b0
  where
  b0 : Chain (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ []) []
  b0 = at 0 2 (CCZ014 ∷ []) (lem-SB2 c4) ▸
       at 1 2 (CCZ014 ∷ []) (lem-SB2 c4) ▸
       at 0 2 [] (pw2 c4 (CCZ014 ∷ CCZ014 ∷ []) [] tt tt Eq.refl) ▸
       at 0 0 [] (sym (lem-F1-order-CS-nf-of-rhs c4)) ▸ done


-- auto BOX(0;1234) | CS21: 3 steps
lem-auto-BOX⟨0·1234⟩-∣-CS21 : Complete 4 → ⟪ (Bx0-1234 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS21 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ CS12 ∷ []) (CS12 ∷ Bx0-1234 ∷ [])
  b0 = at 1 1 (CS12 ∷ []) (lw4 c4 (CS12 ∷ []) (CS12 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (CS12 ∷ Bx0-1234 ∷ []) (sym (lem-CS12-beta c4)) ▸
       at 0 1 (CS12 ∷ []) (lw4 c4 (CS12 ∷ []) (CS12 ∷ []) tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CS21: 11 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS21 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS21 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-1-23-4 ∷ CS12 ∷ []) (Bx0-1234 ∷ Toff423 ∷ CS12 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 4 1 (CS14⁻ ∷ []) (refl) ▸
       at 4 2 (CS12 ∷ CS14⁻ ∷ []) (lw0 c4 (CS14⁻ ∷ CS12 ∷ []) (CS12 ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 3 2 (CS12 ∷ Toff423 ∷ []) (lw0 c4 (Toff423 ∷ CS12 ∷ []) (CS12 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (CS14 ∷ []) (refl) ▸
       at 2 2 (CS12 ∷ CS14 ∷ []) (lw0 c4 (CS14 ∷ CS12 ∷ []) (CS12 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Sb0-1-4-3 ∷ []) (refl) ▸ done

  b1 : Chain (Bx0-1234 ∷ Toff423 ∷ CS12 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (CS12 ∷ Sb0-1-23-4 ∷ [])
  b1 = at 1 2 (CS12 ∷ Toff423 ∷ []) (lw0 c4 (Toff423 ∷ CS12 ∷ []) (CS12 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (CS12 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS21 c4) ▸
       at 1 5 (Sb0-1-23-4 ∷ []) (refl) ▸ done


-- auto SBOX(0;1;23;4) | CS21 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS21-at2332 : Complete 4 → ⟪ (Sb0-1-32-4 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS21-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ CS13 ∷ []) (CS13 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 (CS12 ∷ Sw23 ∷ []) (lem-nat-2-CS13 c4) ▸
       at 1 2 (CS12 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS21 c4) ▸
       at 0 2 (CS13 ∷ Sw23 ∷ []) (lem-nat-2-CS12 c4) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CS21 @243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS21-at243243 : Complete 4 → ⟪ (Sb0-1-42-3 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS21-at243243 c4 = run b0
  where
  b0 : Chain (Sb0-1-42-3 ∷ CS14 ∷ []) (CS14 ∷ Sb0-1-42-3 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·42·3⟩ c4) ▸
       at 2 2 (CS13 ∷ Sw34 ∷ []) (lem-nat-3-CS14 c4) ▸
       at 1 2 (CS13 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS21-at2332 c4) ▸
       at 0 2 (CS14 ∷ Sw34 ∷ []) (lem-nat-3-CS13 c4) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CS21 @0110243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS21-at0110243243 : Complete 4 → ⟪ (Sb1-0-42-3 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS21-at0110243243 c4 = run b0
  where
  b0 : Chain (Sb1-0-42-3 ∷ CS04 ∷ []) (CS04 ∷ Sb1-0-42-3 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·42·3⟩ c4) ▸
       at 2 2 (CS14 ∷ Sw01 ∷ []) (lem-nat-0-CS04 c4) ▸
       at 1 2 (CS14 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS21-at243243 c4) ▸
       at 0 2 (CS04 ∷ Sw01 ∷ []) (lem-nat-0-CS14 c4) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CS21 @0210243143: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS21-at0210243143 : Complete 4 → ⟪ (Sb2-0-41-3 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS21-at0210243143 c4 = run b0
  where
  b0 : Chain (Sb2-0-41-3 ∷ CS04 ∷ []) (CS04 ∷ Sb2-0-41-3 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·41·3⟩ c4) ▸
       at 2 2 (CS04 ∷ Sw12 ∷ []) (lem-nat-1-CS04 c4) ▸
       at 1 2 (CS04 ∷ Sb1-0-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS21-at0110243243 c4) ▸
       at 0 2 (CS04 ∷ Sw12 ∷ []) (lem-nat-1-CS04 c4) ▸
       at 1 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- F1 comm-CS-S0: 1 steps
lem-F1-comm-CS-S0 : Complete 4 → ⟪ (Sb2-0-41-3 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-F1-comm-CS-S0 c4 = run b0
  where
  b0 : Chain (Sb2-0-41-3 ∷ CS04 ∷ []) (CS04 ∷ Sb2-0-41-3 ∷ [])
  b0 = at 0 2 (CS04 ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS21-at0210243143 c4) ▸ done


-- CS12-beta @122331: 7 steps
lem-CS12-beta-at122331 : Complete 4 → ⟪ (CS23 ∷ Bx0-2314 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2314 ∷ CS23 ∷ []) ⟫ʷ
lem-CS12-beta-at122331 c4 = run b0
  where
  b0 : Chain (CS23 ∷ Bx0-2314 ∷ []) (Bx0-2314 ∷ CS23 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS13 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS23 ∷ []) (CS13 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-1324 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2314⟩ c4) ▸
       at 1 2 (Bx0-1324 ∷ CS13 ∷ []) (lem-CS12-beta-at2332 c4) ▸
       at 0 2 (Bx0-2314 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1324⟩ c4) ▸
       at 1 2 (CS23 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS13 ∷ []) (CS23 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CS23: 5 steps
lem-auto-BOX⟨0·1234⟩-∣-CS23 : Complete 4 → ⟪ (Bx0-1234 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS23 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ CS23 ∷ []) (CS23 ∷ Bx0-1234 ∷ [])
  b0 = at 0 1 (Bx0-2134 ∷ []) (lem-sym12 c4) ▸
       at 0 1 (Bx0-2314 ∷ []) (lem-sym23-at1221 c4) ▸
       at 0 2 (CS23 ∷ Bx0-2314 ∷ []) (sym (lem-CS12-beta-at122331 c4)) ▸
       at 1 1 (Bx0-2134 ∷ []) (lem-sym23-at122331 c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym12-at1221 c4) ▸ done


-- auto SBOX(0;1;23;4) | CS23: 11 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS23 : Complete 4 → ⟪ (Sb0-1-23-4 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS23 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-1-23-4 ∷ CS23 ∷ []) (Bx0-1234 ∷ Toff423 ∷ CS23 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 4 1 (CS14⁻ ∷ []) (refl) ▸
       at 4 2 (CS23 ∷ CS14⁻ ∷ []) (lw0 c4 (CS14⁻ ∷ CS23 ∷ []) (CS23 ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 3 2 (CS23 ∷ Toff423 ∷ []) (lw0 c4 (Toff423 ∷ CS23 ∷ []) (CS23 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (CS14 ∷ []) (refl) ▸
       at 2 2 (CS23 ∷ CS14 ∷ []) (lw0 c4 (CS14 ∷ CS23 ∷ []) (CS23 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (Sb0-1-4-3 ∷ []) (refl) ▸ done

  b1 : Chain (Bx0-1234 ∷ Toff423 ∷ CS23 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (CS23 ∷ Sb0-1-23-4 ∷ [])
  b1 = at 1 2 (CS23 ∷ Toff423 ∷ []) (lw0 c4 (Toff423 ∷ CS23 ∷ []) (CS23 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (CS23 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS23 c4) ▸
       at 1 5 (Sb0-1-23-4 ∷ []) (refl) ▸ done


-- auto SBOX(0;1;23;4) | CS23 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS23-at2332 : Complete 4 → ⟪ (Sb0-1-32-4 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS23-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ CS23 ∷ []) (CS23 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 (CS23 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CS23 ∷ []) (CS23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS23 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS23 c4) ▸
       at 0 2 (CS23 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CS23 ∷ []) (CS23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CS23 @243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS23-at243243 : Complete 4 → ⟪ (Sb0-1-42-3 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS23-at243243 c4 = run b0
  where
  b0 : Chain (Sb0-1-42-3 ∷ CS24 ∷ []) (CS24 ∷ Sb0-1-42-3 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·42·3⟩ c4) ▸
       at 2 2 (CS23 ∷ Sw34 ∷ []) (lem-nat-3-CS24 c4) ▸
       at 1 2 (CS23 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS23-at2332 c4) ▸
       at 0 2 (CS24 ∷ Sw34 ∷ []) (lem-nat-3-CS23 c4) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CS23 @0110243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS23-at0110243243 : Complete 4 → ⟪ (Sb1-0-42-3 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS23-at0110243243 c4 = run b0
  where
  b0 : Chain (Sb1-0-42-3 ∷ CS24 ∷ []) (CS24 ∷ Sb1-0-42-3 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·42·3⟩ c4) ▸
       at 2 2 (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑)) ▸
       at 1 2 (CS24 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS23-at243243 c4) ▸
       at 0 2 (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑)) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CS23 @0210243143: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS23-at0210243143 : Complete 4 → ⟪ (Sb2-0-41-3 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CS23-at0210243143 c4 = run b0
  where
  b0 : Chain (Sb2-0-41-3 ∷ CS14 ∷ []) (CS14 ∷ Sb2-0-41-3 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·41·3⟩ c4) ▸
       at 2 2 (CS24 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS14 ∷ []) (CS24 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS24 ∷ Sb1-0-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS23-at0110243243 c4) ▸
       at 0 2 (CS14 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS24 ∷ []) (CS14 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- F1 comm-CS-S1: 1 steps
lem-F1-comm-CS-S1 : Complete 4 → ⟪ (Sb2-0-41-3 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-F1-comm-CS-S1 c4 = run b0
  where
  b0 : Chain (Sb2-0-41-3 ∷ CS14 ∷ []) (CS14 ∷ Sb2-0-41-3 ∷ [])
  b0 = at 0 2 (CS14 ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CS23-at0210243143 c4) ▸ done


-- auto BOX(0;1234) | CCZ324: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ324 : Complete 4 → ⟪ (Bx0-1234 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ324 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ CCZ234 ∷ []) (CCZ234 ∷ Bx0-1234 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ []) (lw0 c4 (CCZ234 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx0-2134 ∷ []) (lem-sym12 c4) ▸
       at 0 1 (Bx0-2314 ∷ []) (lem-sym23-at1221 c4) ▸
       at 0 2 (CCZ234 ∷ Bx0-2314 ∷ []) (sym (lem-c124-beta-at122331 c4)) ▸
       at 1 1 (Bx0-2134 ∷ []) (lem-sym23-at122331 c4) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-sym12-at1221 c4) ▸
       at 0 1 (CCZ234 ∷ []) (lw0 c4 (CCZ234 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸ done


-- sym12 @0214213043: 5 steps
lem-sym12-at0214213043 : Complete 4 → ⟪ (Bx2-4103 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1403 ∷ []) ⟫ʷ
lem-sym12-at0214213043 c4 = run b0
  where
  b0 : Chain (Bx2-4103 ∷ []) (Bx2-1403 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx2-4013 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·4103⟩ c4) ▸
       at 1 1 (Bx2-0413 ∷ []) (lem-sym12-at0214203143 c4) ▸
       at 0 2 (Bx2-1403 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·0413⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- CX23-beta @2332: 8 steps
lem-CX23-beta-at2332 : Complete 4 → ⟪ (CX32 ∷ Bx0-1324 ∷ CX32 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ CCZ134 ∷ []) ⟫ʷ
lem-CX23-beta-at2332 c4 = run b0
  where
  b0 : Chain (CX32 ∷ Bx0-1324 ∷ CX32 ∷ []) (Bx0-1324 ∷ CCZ134 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CX23 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CX32 ∷ []) (CX23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ c4) ▸
       at 3 2 (CX23 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CX32 ∷ []) (CX23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Bx0-1234 ∷ CCZ124 ∷ []) (lem-CX23-beta c4) ▸
       at 0 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ c4) ▸
       at 1 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- CX23-beta @243243: 8 steps
lem-CX23-beta-at243243 : Complete 4 → ⟪ (CX42 ∷ Bx0-1423 ∷ CX42 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ CCZ134 ∷ []) ⟫ʷ
lem-CX23-beta-at243243 c4 = run b0
  where
  b0 : Chain (CX42 ∷ Bx0-1423 ∷ CX42 ∷ []) (Bx0-1423 ∷ CCZ134 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CX32 ∷ Sw34 ∷ []) (lem-nat-3-CX42 c4) ▸
       at 2 2 (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ c4) ▸
       at 3 2 (CX32 ∷ Sw34 ∷ []) (lem-nat-3-CX42 c4) ▸
       at 1 3 (Bx0-1324 ∷ CCZ134 ∷ []) (lem-CX23-beta-at2332 c4) ▸
       at 0 2 (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ c4) ▸
       at 1 2 (CCZ134 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ CCZ134 ∷ []) (CCZ134 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- CX23-beta @0110243243: 8 steps
lem-CX23-beta-at0110243243 : Complete 4 → ⟪ (CX42 ∷ Bx1-0423 ∷ CX42 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0423 ∷ CCZ034 ∷ []) ⟫ʷ
lem-CX23-beta-at0110243243 c4 = run b0
  where
  b0 : Chain (CX42 ∷ Bx1-0423 ∷ CX42 ∷ []) (Bx1-0423 ∷ CCZ034 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CX42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CX₁₀ • Swap ↑)) ▸
       at 2 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ c4) ▸
       at 3 2 (CX42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CX₁₀ • Swap ↑)) ▸
       at 1 3 (Bx0-1423 ∷ CCZ134 ∷ []) (lem-CX23-beta-at243243 c4) ▸
       at 0 2 (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ c4) ▸
       at 1 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- CX23-beta @0210243143: 8 steps
lem-CX23-beta-at0210243143 : Complete 4 → ⟪ (CX41 ∷ Bx2-0413 ∷ CX41 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ CCZ034 ∷ []) ⟫ʷ
lem-CX23-beta-at0210243143 c4 = run b0
  where
  b0 : Chain (CX41 ∷ Bx2-0413 ∷ CX41 ∷ []) (Bx2-0413 ∷ CCZ034 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CX42 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CX41 ∷ []) (CX42 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ c4) ▸
       at 3 2 (CX42 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CX41 ∷ []) (CX42 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Bx1-0423 ∷ CCZ034 ∷ []) (lem-CX23-beta-at0110243243 c4) ▸
       at 0 2 (Bx2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0423⟩ c4) ▸
       at 1 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- CX23-beta @02243043: 8 steps
lem-CX23-beta-at02243043 : Complete 4 → ⟪ (CX40 ∷ Bx2-1403 ∷ CX40 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1403 ∷ CCZ134 ∷ []) ⟫ʷ
lem-CX23-beta-at02243043 c4 = run b0
  where
  b0 : Chain (CX40 ∷ Bx2-1403 ∷ CX40 ∷ []) (Bx2-1403 ∷ CCZ134 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CX41 ∷ Sw01 ∷ []) (lem-nat-0-CX40 c4) ▸
       at 2 2 (Bx2-0413 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·1403⟩ c4) ▸
       at 3 2 (CX41 ∷ Sw01 ∷ []) (lem-nat-0-CX40 c4) ▸
       at 1 3 (Bx2-0413 ∷ CCZ034 ∷ []) (lem-CX23-beta-at0210243143 c4) ▸
       at 0 2 (Bx2-1403 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·0413⟩ c4) ▸
       at 1 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym12 @02243043: 5 steps
lem-sym12-at02243043 : Complete 4 → ⟪ (Bx2-1403 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4103 ∷ []) ⟫ʷ
lem-sym12-at02243043 c4 = run b0
  where
  b0 : Chain (Bx2-1403 ∷ []) (Bx2-4103 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx2-0413 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·1403⟩ c4) ▸
       at 1 1 (Bx2-4013 ∷ []) (lem-sym12-at0210243143 c4) ▸
       at 0 2 (Bx2-4103 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·4013⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ324 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ324-at2332 : Complete 4 → ⟪ (Bx0-1324 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ324-at2332 c4 = run b0
  where
  b0 : Chain (Bx0-1324 ∷ CCZ234 ∷ []) (CCZ234 ∷ Bx0-1324 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ c4) ▸
       at 2 2 (CCZ234 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ234 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ324 c4) ▸
       at 0 2 (CCZ234 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done

