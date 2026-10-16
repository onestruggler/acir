{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D012 where

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
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-beta-T-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-sym34-at021021)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-X1-beta ; lem-sym12-at3443)
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-SBsymd)
open import Examples.Groups.Clifford+CS.Five.D.D007 using (lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·1·23·4⟩ ; lem-auto-SBOX⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.D008 using (lem-F5d-CS01 ; lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ124 ; lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS24 ; lem-auto-SBOXd⟨0·1·23·4⟩-∣-K4 ; lem-auto-SBOXd⟨0·1·23·4⟩-∣-Kd4 ; lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨0·1·4·3⟩ ; lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨0·1·4·3⟩)
open import Examples.Groups.Clifford+CS.Five.D.D009 using (lem-auto-BOXd⟨0·1234⟩-∣-CS40 ; lem-auto-BOXd⟨0·1234⟩-∣-CSd40 ; lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF012)
open import Examples.Groups.Clifford+CS.Five.D.D011 using (lem-auto-K0-∣-SBOX⟨1·2·34·0⟩-at03203442)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-1-CCZ034 ; lem-nat-2-BOX⟨0·1234⟩ ; lem-nat-2-BOX⟨0·1324⟩ ; lem-nat-2-TOFF012 ; lem-nat-2-TOFF013 ; lem-nat-3-BOX⟨0·1243⟩ ; lem-nat-3-BOX⟨0·1423⟩ ; lem-nat-3-TOFF013 ; lem-nat-3-TOFF014)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-3-BOX⟨0·1324⟩)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-0-CCZ024 ; lem-nat-0-CCZ124 ; lem-nat-1-TOFF103 ; lem-nat-2-CCZ124 ; lem-nat-2-CCZ134)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-0-TOFF014 ; lem-nat-0-TOFF104 ; lem-nat-1-TOFF104 ; lem-nat-1-TOFF204)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-0-CCZ034 ; lem-nat-0-CCZ134)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-0-BOX⟨0·1423⟩ ; lem-nat-1-BOX⟨1·0423⟩)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-nat-0-BOX⟨0·1243⟩ ; lem-nat-0-BOX⟨1·0243⟩ ; lem-nat-0-BOX⟨1·0423⟩ ; lem-nat-1-BOX⟨1·0243⟩ ; lem-nat-1-BOX⟨2·0143⟩ ; lem-nat-1-BOX⟨2·0413⟩ ; lem-nat-3-BOX⟨0·1234⟩)
open import Examples.Groups.Clifford+CS.Five.D.R012 using (lem-nat-0-BOX⟨0·2143⟩ ; lem-nat-0-BOXd⟨1·0423⟩ ; lem-nat-2-BOXd⟨0·1324⟩ ; lem-nat-3-BOXd⟨0·1423⟩)
open import Examples.Groups.Clifford+CS.Five.D.R013 using (lem-nat-1-BOXd⟨2·0413⟩)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-nat-0-SBOX⟨0·1·3·2⟩ ; lem-nat-0-SBOX⟨0·1·42·3⟩ ; lem-nat-0-SBOX⟨1·0·3·2⟩ ; lem-nat-0-SBOX⟨1·0·42·3⟩ ; lem-nat-0-SBOXd⟨0·1·3·2⟩ ; lem-nat-0-SBOXd⟨1·0·3·2⟩ ; lem-nat-1-CSd02 ; lem-nat-1-SBOX⟨1·0·3·2⟩ ; lem-nat-1-SBOX⟨1·0·42·3⟩ ; lem-nat-1-SBOX⟨2·0·3·1⟩ ; lem-nat-1-SBOX⟨2·0·41·3⟩ ; lem-nat-1-SBOXd⟨1·0·3·2⟩ ; lem-nat-1-SBOXd⟨2·0·3·1⟩ ; lem-nat-2-SBOX⟨0·1·23·4⟩ ; lem-nat-2-SBOX⟨0·1·32·4⟩ ; lem-nat-2-SBOX⟨0·1·4·2⟩ ; lem-nat-2-SBOX⟨0·1·4·3⟩ ; lem-nat-2-SBOXd⟨0·1·4·2⟩ ; lem-nat-2-SBOXd⟨0·1·4·3⟩ ; lem-nat-3-SBOX⟨0·1·32·4⟩ ; lem-nat-3-SBOX⟨0·1·3·2⟩ ; lem-nat-3-SBOX⟨0·1·42·3⟩ ; lem-nat-3-SBOX⟨0·1·4·2⟩ ; lem-nat-3-SBOXd⟨0·1·3·2⟩ ; lem-nat-3-SBOXd⟨0·1·4·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R016 using (lem-nat-0-BOX⟨1·0324⟩ ; lem-nat-1-BOX⟨2·0314⟩ ; lem-nat-1-CSd04 ; lem-nat-3-CS04 ; lem-nat-3-CSd04)
open import Examples.Groups.Clifford+CS.Five.D.R017 using (lem-nat-2-CS04 ; lem-nat-2-CSd04 ; lem-nat-3-CS03 ; lem-nat-3-CSd03)
open import Examples.Groups.Clifford+CS.Five.D.R018 using (lem-nat-2-BOXd⟨0·1234⟩ ; lem-nat-2-SBOXd⟨0·1·23·4⟩ ; lem-nat-2-SBOXd⟨0·1·32·4⟩)
open import Examples.Groups.Clifford+CS.Five.D.R019 using (lem-nat-0-BOX⟨2·1034⟩ ; lem-nat-0-BOX⟨2·1304⟩ ; lem-nat-2-CSd03 ; lem-nat-2-SBOX⟨0·1·2·3⟩ ; lem-nat-2-SBOX⟨0·1·3·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R020 using (lem-nat-2-SBOX⟨0·1·42·3⟩ ; lem-nat-2-SBOX⟨0·1·43·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R022 using (lem-nat-0-BOX⟨2·0143⟩ ; lem-nat-0-BOX⟨2·1043⟩ ; lem-nat-0-BOXd⟨0·1423⟩ ; lem-nat-0-SBOXd⟨0·1·42·3⟩ ; lem-nat-0-SBOXd⟨1·0·42·3⟩ ; lem-nat-1-BOX⟨1·2043⟩ ; lem-nat-1-BOXd⟨1·0423⟩ ; lem-nat-1-SBOXd⟨1·0·24·3⟩ ; lem-nat-1-SBOXd⟨1·0·42·3⟩ ; lem-nat-1-SBOXd⟨2·0·14·3⟩ ; lem-nat-1-SBOXd⟨2·0·41·3⟩ ; lem-nat-2-SBOXd⟨1·0·24·3⟩ ; lem-nat-2-SBOXd⟨1·0·34·2⟩ ; lem-nat-2-SBOXd⟨1·0·42·3⟩ ; lem-nat-2-SBOXd⟨1·0·43·2⟩ ; lem-nat-3-BOXd⟨0·1324⟩ ; lem-nat-3-SBOXd⟨0·1·32·4⟩ ; lem-nat-3-SBOXd⟨0·1·42·3⟩ ; lem-nat-3-SBOXd⟨1·0·34·2⟩ ; lem-nat-3-SBOXd⟨1·0·43·2⟩)
-- auto K0 | SBOX(1;2;34;0) @0312203441: 7 steps
lem-auto-K0-∣-SBOX⟨1·2·34·0⟩-at0312203441 : Complete 4 → ⟪ (K3 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ K3 ∷ []) ⟫ʷ
lem-auto-K0-∣-SBOX⟨1·2·34·0⟩-at0312203441 c4 = run b0
  where
  b0 : Chain (K3 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ K3 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (K3 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K)) ▸
       at 2 2 (Sb1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·41·3⟩ c4) ▸
       at 1 2 (Sb1-0-42-3 ∷ K3 ∷ []) (lem-auto-K0-∣-SBOX⟨1·2·34·0⟩-at03203442 c4) ▸
       at 0 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ c4) ▸
       at 1 2 (K3 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K)) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;2;3) | SBOX(0;1;43;2) @2332: 7 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩-at2332 : Complete 4 → ⟪ (Sb0-1-3-2 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ Sb0-1-3-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-3-2 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ Sb0-1-3-2 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-2-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·3·2⟩ c4) ▸
       at 2 2 (Sb0-1-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·42·3⟩ c4) ▸
       at 1 2 (Sb0-1-43-2 ∷ Sb0-1-2-3 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩ c4) ▸
       at 0 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·43·2⟩ c4) ▸
       at 1 2 (Sb0-1-3-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·2·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;2;3) | SBOX(0;1;43;2) @01102332: 7 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩-at01102332 : Complete 4 → ⟪ (Sb1-0-3-2 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-42-3 ∷ Sb1-0-3-2 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩-at01102332 c4 = run b0
  where
  b0 : Chain (Sb1-0-3-2 ∷ Sb1-0-42-3 ∷ []) (Sb1-0-42-3 ∷ Sb1-0-3-2 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·3·2⟩ c4) ▸
       at 2 2 (Sb0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·42·3⟩ c4) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sb0-1-3-2 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩-at2332 c4) ▸
       at 0 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ c4) ▸
       at 1 2 (Sb1-0-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·3·2⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;2;3) | SBOX(0;1;43;2) @02102331: 7 steps
lem-auto-SBOX⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩-at02102331 : Complete 4 → ⟪ (Sb2-0-3-1 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ Sb2-0-3-1 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩-at02102331 c4 = run b0
  where
  b0 : Chain (Sb2-0-3-1 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ Sb2-0-3-1 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·3·1⟩ c4) ▸
       at 2 2 (Sb1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·41·3⟩ c4) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sb1-0-3-2 ∷ []) (lem-auto-SBOX⟨0·1·2·3⟩-∣-SBOX⟨0·1·43·2⟩-at01102332 c4) ▸
       at 0 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ c4) ▸
       at 1 2 (Sb2-0-3-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·3·2⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym12 @01103443: 5 steps
lem-sym12-at01103443 : Complete 4 → ⟪ (Bx1-0243 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2043 ∷ []) ⟫ʷ
lem-sym12-at01103443 c4 = run b0
  where
  b0 : Chain (Bx1-0243 ∷ []) (Bx1-2043 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1243 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0243⟩ c4) ▸
       at 1 1 (Bx0-2143 ∷ []) (lem-sym12-at3443 c4) ▸
       at 0 2 (Bx1-2043 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·2143⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym12 @0210213443: 5 steps
lem-sym12-at0210213443 : Complete 4 → ⟪ (Bx2-0143 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1043 ∷ []) ⟫ʷ
lem-sym12-at0210213443 c4 = run b0
  where
  b0 : Chain (Bx2-0143 ∷ []) (Bx2-1043 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-0243 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0143⟩ c4) ▸
       at 1 1 (Bx1-2043 ∷ []) (lem-sym12-at01103443 c4) ▸
       at 0 2 (Bx2-1043 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·2043⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- X1-beta @3443: 8 steps
lem-X1-beta-at3443 : Complete 4 → ⟪ (X1 ∷ Bx0-1243 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Bx0-1243 ∷ []) ⟫ʷ
lem-X1-beta-at3443 c4 = run b0
  where
  b0 : Chain (X1 ∷ Bx0-1243 ∷ X1 ∷ []) (CCZ234 ∷ Bx0-1243 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (X1 ∷ Sw34 ∷ []) (sym (c₂ (X ↑) (Swap ↑))) ▸
       at 2 2 (Bx0-1234 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1243⟩ c4) ▸
       at 3 2 (X1 ∷ Sw34 ∷ []) (sym (c₂ (X ↑) (Swap ↑))) ▸
       at 1 3 (CCZ234 ∷ Bx0-1234 ∷ []) (lem-X1-beta c4) ▸
       at 0 2 (CCZ234 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1243 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1234⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- X1-beta @01103443: 8 steps
lem-X1-beta-at01103443 : Complete 4 → ⟪ (X0 ∷ Bx1-0243 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Bx1-0243 ∷ []) ⟫ʷ
lem-X1-beta-at01103443 c4 = run b0
  where
  b0 : Chain (X0 ∷ Bx1-0243 ∷ X0 ∷ []) (CCZ234 ∷ Bx1-0243 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (X1 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ X0 ∷ []) (X1 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-1243 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0243⟩ c4) ▸
       at 3 2 (X1 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ X0 ∷ []) (X1 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (CCZ234 ∷ Bx0-1243 ∷ []) (lem-X1-beta-at3443 c4) ▸
       at 0 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 1 2 (Bx1-0243 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1243⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- X1-beta @0210213443: 8 steps
lem-X1-beta-at0210213443 : Complete 4 → ⟪ (X0 ∷ Bx2-0143 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Bx2-0143 ∷ []) ⟫ʷ
lem-X1-beta-at0210213443 c4 = run b0
  where
  b0 : Chain (X0 ∷ Bx2-0143 ∷ X0 ∷ []) (CCZ134 ∷ Bx2-0143 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (X0 ∷ Sw12 ∷ []) (sym (c₁ (X) (Swap))) ▸
       at 2 2 (Bx1-0243 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0143⟩ c4) ▸
       at 3 2 (X0 ∷ Sw12 ∷ []) (sym (c₁ (X) (Swap))) ▸
       at 1 3 (CCZ234 ∷ Bx1-0243 ∷ []) (lem-X1-beta-at01103443 c4) ▸
       at 0 2 (CCZ134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ234 ∷ []) (CCZ134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx2-0143 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0243⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- X1-beta @02203443: 8 steps
lem-X1-beta-at02203443 : Complete 4 → ⟪ (X1 ∷ Bx2-1043 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Bx2-1043 ∷ []) ⟫ʷ
lem-X1-beta-at02203443 c4 = run b0
  where
  b0 : Chain (X1 ∷ Bx2-1043 ∷ X1 ∷ []) (CCZ034 ∷ Bx2-1043 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (X0 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ X1 ∷ []) (X0 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx2-0143 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·1043⟩ c4) ▸
       at 3 2 (X0 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ X1 ∷ []) (X0 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (CCZ134 ∷ Bx2-0143 ∷ []) (lem-X1-beta-at0210213443 c4) ▸
       at 0 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 1 2 (Bx2-1043 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·0143⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym12 @02203443: 5 steps
lem-sym12-at02203443 : Complete 4 → ⟪ (Bx2-1043 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0143 ∷ []) ⟫ʷ
lem-sym12-at02203443 c4 = run b0
  where
  b0 : Chain (Bx2-1043 ∷ []) (Bx2-0143 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx2-0143 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·1043⟩ c4) ▸
       at 1 1 (Bx2-1043 ∷ []) (lem-sym12-at0210213443 c4) ▸
       at 0 2 (Bx2-0143 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·1043⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | SBOX(0;1;23;4) @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·1·23·4⟩-at2332 : Complete 4 → ⟪ (Bx0-1324 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-32-4 ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·1·23·4⟩-at2332 c4 = run b0
  where
  b0 : Chain (Bx0-1324 ∷ Sb0-1-32-4 ∷ []) (Sb0-1-32-4 ∷ Bx0-1324 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ c4) ▸
       at 2 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ c4) ▸
       at 1 2 (Sb0-1-23-4 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·1·23·4⟩ c4) ▸
       at 0 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ c4) ▸
       at 1 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | SBOX(0;1;23;4) @243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·1·23·4⟩-at243243 : Complete 4 → ⟪ (Bx0-1423 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ Bx0-1423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·1·23·4⟩-at243243 c4 = run b0
  where
  b0 : Chain (Bx0-1423 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ Bx0-1423 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ c4) ▸
       at 2 2 (Sb0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·42·3⟩ c4) ▸
       at 1 2 (Sb0-1-32-4 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·1·23·4⟩-at2332 c4) ▸
       at 0 2 (Sb0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·32·4⟩ c4) ▸
       at 1 2 (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | SBOX(0;1;23;4) @0110243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·1·23·4⟩-at0110243243 : Complete 4 → ⟪ (Bx1-0423 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-42-3 ∷ Bx1-0423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·1·23·4⟩-at0110243243 c4 = run b0
  where
  b0 : Chain (Bx1-0423 ∷ Sb1-0-42-3 ∷ []) (Sb1-0-42-3 ∷ Bx1-0423 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ c4) ▸
       at 2 2 (Sb0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·42·3⟩ c4) ▸
       at 1 2 (Sb0-1-42-3 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·1·23·4⟩-at243243 c4) ▸
       at 0 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ c4) ▸
       at 1 2 (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | SBOX(0;1;23;4) @0210243143: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·1·23·4⟩-at0210243143 : Complete 4 → ⟪ (Bx2-0413 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ Bx2-0413 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·1·23·4⟩-at0210243143 c4 = run b0
  where
  b0 : Chain (Bx2-0413 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ Bx2-0413 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ c4) ▸
       at 2 2 (Sb1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·41·3⟩ c4) ▸
       at 1 2 (Sb1-0-42-3 ∷ Bx1-0423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-SBOX⟨0·1·23·4⟩-at0110243243 c4) ▸
       at 0 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ c4) ▸
       at 1 2 (Bx2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0423⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CCZ124 @2332: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ124-at2332 : Complete 4 → ⟪ (Sb0-1-32-4 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ124-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-32-4 ∷ CCZ134 ∷ []) (CCZ134 ∷ Sb0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 1 2 (CCZ124 ∷ Sb0-1-23-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ124 c4) ▸
       at 0 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CCZ124 @243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ124-at243243 : Complete 4 → ⟪ (Sb0-1-42-3 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ124-at243243 c4 = run b0
  where
  b0 : Chain (Sb0-1-42-3 ∷ CCZ134 ∷ []) (CCZ134 ∷ Sb0-1-42-3 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·42·3⟩ c4) ▸
       at 2 2 (CCZ134 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ CCZ134 ∷ []) (CCZ134 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ134 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ124-at2332 c4) ▸
       at 0 2 (CCZ134 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ CCZ134 ∷ []) (CCZ134 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·32·4⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CCZ124 @0110243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ124-at0110243243 : Complete 4 → ⟪ (Sb1-0-42-3 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ124-at0110243243 c4 = run b0
  where
  b0 : Chain (Sb1-0-42-3 ∷ CCZ034 ∷ []) (CCZ034 ∷ Sb1-0-42-3 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·42·3⟩ c4) ▸
       at 2 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4) ▸
       at 1 2 (CCZ134 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ124-at243243 c4) ▸
       at 0 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOX(0;1;23;4) | CCZ124 @0210243143: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ124-at0210243143 : Complete 4 → ⟪ (Sb2-0-41-3 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ124-at0210243143 c4 = run b0
  where
  b0 : Chain (Sb2-0-41-3 ∷ CCZ034 ∷ []) (CCZ034 ∷ Sb2-0-41-3 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·41·3⟩ c4) ▸
       at 2 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 1 2 (CCZ034 ∷ Sb1-0-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-CCZ124-at0110243243 c4) ▸
       at 0 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 1 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- F5d CS01 @1221: 8 steps
lem-F5d-CS01-at1221 : Complete 4 → ⟪ (CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-42-3 ∷ X4 ∷ Sb⁻1-0-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-F5d-CS01-at1221 c4 = run b0
  where
  b0 : Chain (CS02⁻ ∷ []) (Sb⁻1-0-42-3 ∷ X4 ∷ Sb⁻1-0-42-3 ∷ X4 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS01⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd02 c4) ▸
       at 1 1 (Sb⁻2-0-41-3 ∷ X4 ∷ Sb⁻2-0-41-3 ∷ X4 ∷ []) (lem-F5d-CS01 c4) ▸
       at 0 2 (Sb⁻1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·41·3⟩ c4) ▸
       at 1 2 (X4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (X ↑)) ▸
       at 2 2 (Sb⁻1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·41·3⟩ c4) ▸
       at 3 2 (X4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (X ↑)) ▸
       at 4 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- F5d CS01 @132132: 8 steps
lem-F5d-CS01-at132132 : Complete 4 → ⟪ (CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-43-2 ∷ X4 ∷ Sb⁻1-0-43-2 ∷ X4 ∷ []) ⟫ʷ
lem-F5d-CS01-at132132 c4 = run b0
  where
  b0 : Chain (CS03⁻ ∷ []) (Sb⁻1-0-43-2 ∷ X4 ∷ Sb⁻1-0-43-2 ∷ X4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS02⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd03 c4) ▸
       at 1 1 (Sb⁻1-0-42-3 ∷ X4 ∷ Sb⁻1-0-42-3 ∷ X4 ∷ []) (lem-F5d-CS01-at1221 c4) ▸
       at 0 2 (Sb⁻1-0-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·0·42·3⟩ c4) ▸
       at 1 2 (X4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (X)) ▸
       at 2 2 (Sb⁻1-0-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·0·42·3⟩ c4) ▸
       at 3 2 (X4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (X)) ▸
       at 4 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- F5d CS01 @14213243: 8 steps
lem-F5d-CS01-at14213243 : Complete 4 → ⟪ (CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-34-2 ∷ X3 ∷ Sb⁻1-0-34-2 ∷ X3 ∷ []) ⟫ʷ
lem-F5d-CS01-at14213243 c4 = run b0
  where
  b0 : Chain (CS04⁻ ∷ []) (Sb⁻1-0-34-2 ∷ X3 ∷ Sb⁻1-0-34-2 ∷ X3 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS03⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd04 c4) ▸
       at 1 1 (Sb⁻1-0-43-2 ∷ X4 ∷ Sb⁻1-0-43-2 ∷ X4 ∷ []) (lem-F5d-CS01-at132132 c4) ▸
       at 0 2 (Sb⁻1-0-34-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨1·0·43·2⟩ c4) ▸
       at 1 2 (X3 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ X4 ∷ []) (X3 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb⁻1-0-34-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨1·0·43·2⟩ c4) ▸
       at 3 2 (X3 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ X4 ∷ []) (X3 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- F5d CS01 @142142: 8 steps
lem-F5d-CS01-at142142 : Complete 4 → ⟪ (CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-24-3 ∷ X2 ∷ Sb⁻1-0-24-3 ∷ X2 ∷ []) ⟫ʷ
lem-F5d-CS01-at142142 c4 = run b0
  where
  b0 : Chain (CS04⁻ ∷ []) (Sb⁻1-0-24-3 ∷ X2 ∷ Sb⁻1-0-24-3 ∷ X2 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS04⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd04 c4) ▸
       at 1 1 (Sb⁻1-0-34-2 ∷ X3 ∷ Sb⁻1-0-34-2 ∷ X3 ∷ []) (lem-F5d-CS01-at14213243 c4) ▸
       at 0 2 (Sb⁻1-0-24-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·0·34·2⟩ c4) ▸
       at 1 2 (X2 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ X3 ∷ []) (X2 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb⁻1-0-24-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·0·34·2⟩ c4) ▸
       at 3 2 (X2 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ X3 ∷ []) (X2 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- F5d CS01 @1441: 8 steps
lem-F5d-CS01-at1441 : Complete 4 → ⟪ (CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-0-14-3 ∷ X1 ∷ Sb⁻2-0-14-3 ∷ X1 ∷ []) ⟫ʷ
lem-F5d-CS01-at1441 c4 = run b0
  where
  b0 : Chain (CS04⁻ ∷ []) (Sb⁻2-0-14-3 ∷ X1 ∷ Sb⁻2-0-14-3 ∷ X1 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS04⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd04 c4) ▸
       at 1 1 (Sb⁻1-0-24-3 ∷ X2 ∷ Sb⁻1-0-24-3 ∷ X2 ∷ []) (lem-F5d-CS01-at142142 c4) ▸
       at 0 2 (Sb⁻2-0-14-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·0·24·3⟩ c4) ▸
       at 1 2 (X1 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ X2 ∷ []) (X1 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb⁻2-0-14-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·0·24·3⟩ c4) ▸
       at 3 2 (X1 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ X2 ∷ []) (X1 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- SBsymd @1221: 5 steps
lem-SBsymd-at1221 : Complete 4 → ⟪ (Sb⁻1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-24-3 ∷ []) ⟫ʷ
lem-SBsymd-at1221 c4 = run b0
  where
  b0 : Chain (Sb⁻1-0-42-3 ∷ []) (Sb⁻1-0-24-3 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·0·42·3⟩ c4) ▸
       at 1 1 (Sb⁻2-0-14-3 ∷ []) (lem-SBsymd c4) ▸
       at 0 2 (Sb⁻1-0-24-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·14·3⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- SBsymd @132132: 5 steps
lem-SBsymd-at132132 : Complete 4 → ⟪ (Sb⁻1-0-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-34-2 ∷ []) ⟫ʷ
lem-SBsymd-at132132 c4 = run b0
  where
  b0 : Chain (Sb⁻1-0-43-2 ∷ []) (Sb⁻1-0-34-2 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻1-0-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·0·43·2⟩ c4) ▸
       at 1 1 (Sb⁻1-0-24-3 ∷ []) (lem-SBsymd-at1221 c4) ▸
       at 0 2 (Sb⁻1-0-34-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·0·24·3⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- SBsymd @14213243: 5 steps
lem-SBsymd-at14213243 : Complete 4 → ⟪ (Sb⁻1-0-34-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-43-2 ∷ []) ⟫ʷ
lem-SBsymd-at14213243 c4 = run b0
  where
  b0 : Chain (Sb⁻1-0-34-2 ∷ []) (Sb⁻1-0-43-2 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻1-0-43-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨1·0·34·2⟩ c4) ▸
       at 1 1 (Sb⁻1-0-34-2 ∷ []) (lem-SBsymd-at132132 c4) ▸
       at 0 2 (Sb⁻1-0-43-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨1·0·34·2⟩ c4) ▸
       at 1 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- SBsymd @142142: 5 steps
lem-SBsymd-at142142 : Complete 4 → ⟪ (Sb⁻1-0-24-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-42-3 ∷ []) ⟫ʷ
lem-SBsymd-at142142 c4 = run b0
  where
  b0 : Chain (Sb⁻1-0-24-3 ∷ []) (Sb⁻1-0-42-3 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻1-0-34-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·0·24·3⟩ c4) ▸
       at 1 1 (Sb⁻1-0-43-2 ∷ []) (lem-SBsymd-at14213243 c4) ▸
       at 0 2 (Sb⁻1-0-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·0·43·2⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- SBsymd @1441: 5 steps
lem-SBsymd-at1441 : Complete 4 → ⟪ (Sb⁻2-0-14-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-0-41-3 ∷ []) ⟫ʷ
lem-SBsymd-at1441 c4 = run b0
  where
  b0 : Chain (Sb⁻2-0-14-3 ∷ []) (Sb⁻2-0-41-3 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻1-0-24-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·14·3⟩ c4) ▸
       at 1 1 (Sb⁻1-0-42-3 ∷ []) (lem-SBsymd-at142142 c4) ▸
       at 0 2 (Sb⁻2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·0·42·3⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;23;4) | SBOX(0;1;4;3) @2332: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨0·1·4·3⟩-at2332 : Complete 4 → ⟪ (Sb⁻0-1-32-4 ∷ Sb0-1-4-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-4-2 ∷ Sb⁻0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨0·1·4·3⟩-at2332 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-32-4 ∷ Sb0-1-4-2 ∷ []) (Sb0-1-4-2 ∷ Sb⁻0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·32·4⟩ c4) ▸
       at 2 2 (Sb0-1-4-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·4·2⟩ c4) ▸
       at 1 2 (Sb0-1-4-3 ∷ Sb⁻0-1-23-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨0·1·4·3⟩ c4) ▸
       at 0 2 (Sb0-1-4-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·4·3⟩ c4) ▸
       at 1 2 (Sb⁻0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;23;4) | SBOX(0;1;4;3) @243243: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨0·1·4·3⟩-at243243 : Complete 4 → ⟪ (Sb⁻0-1-42-3 ∷ Sb0-1-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-3-2 ∷ Sb⁻0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨0·1·4·3⟩-at243243 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-42-3 ∷ Sb0-1-3-2 ∷ []) (Sb0-1-3-2 ∷ Sb⁻0-1-42-3 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·42·3⟩ c4) ▸
       at 2 2 (Sb0-1-4-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·3·2⟩ c4) ▸
       at 1 2 (Sb0-1-4-2 ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨0·1·4·3⟩-at2332 c4) ▸
       at 0 2 (Sb0-1-3-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·4·2⟩ c4) ▸
       at 1 2 (Sb⁻0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·32·4⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;23;4) | SBOX(0;1;4;3) @0110243243: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨0·1·4·3⟩-at0110243243 : Complete 4 → ⟪ (Sb⁻1-0-42-3 ∷ Sb1-0-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-3-2 ∷ Sb⁻1-0-42-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨0·1·4·3⟩-at0110243243 c4 = run b0
  where
  b0 : Chain (Sb⁻1-0-42-3 ∷ Sb1-0-3-2 ∷ []) (Sb1-0-3-2 ∷ Sb⁻1-0-42-3 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·42·3⟩ c4) ▸
       at 2 2 (Sb0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·3·2⟩ c4) ▸
       at 1 2 (Sb0-1-3-2 ∷ Sb⁻0-1-42-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨0·1·4·3⟩-at243243 c4) ▸
       at 0 2 (Sb1-0-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·3·2⟩ c4) ▸
       at 1 2 (Sb⁻1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨0·1·42·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;23;4) | SBOX(0;1;4;3) @0210243143: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨0·1·4·3⟩-at0210243143 : Complete 4 → ⟪ (Sb⁻2-0-41-3 ∷ Sb2-0-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-3-1 ∷ Sb⁻2-0-41-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨0·1·4·3⟩-at0210243143 c4 = run b0
  where
  b0 : Chain (Sb⁻2-0-41-3 ∷ Sb2-0-3-1 ∷ []) (Sb2-0-3-1 ∷ Sb⁻2-0-41-3 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·41·3⟩ c4) ▸
       at 2 2 (Sb1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·3·1⟩ c4) ▸
       at 1 2 (Sb1-0-3-2 ∷ Sb⁻1-0-42-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOX⟨0·1·4·3⟩-at0110243243 c4) ▸
       at 0 2 (Sb2-0-3-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·3·2⟩ c4) ▸
       at 1 2 (Sb⁻2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·0·42·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;23;4) | K4 @2332: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-K4-at2332 : Complete 4 → ⟪ (Sb⁻0-1-32-4 ∷ K4 ∷ []) ⟫ʷ ≈ ⟪ (K4 ∷ Sb⁻0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-K4-at2332 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-32-4 ∷ K4 ∷ []) (K4 ∷ Sb⁻0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·32·4⟩ c4) ▸
       at 2 2 (K4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K)) ▸
       at 1 2 (K4 ∷ Sb⁻0-1-23-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-K4 c4) ▸
       at 0 2 (K4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K)) ▸
       at 1 2 (Sb⁻0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;23;4) | K4 @243243: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-K4-at243243 : Complete 4 → ⟪ (Sb⁻0-1-42-3 ∷ K3 ∷ []) ⟫ʷ ≈ ⟪ (K3 ∷ Sb⁻0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-K4-at243243 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-42-3 ∷ K3 ∷ []) (K3 ∷ Sb⁻0-1-42-3 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·42·3⟩ c4) ▸
       at 2 2 (K4 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ K3 ∷ []) (K4 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (K4 ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-K4-at2332 c4) ▸
       at 0 2 (K3 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ K4 ∷ []) (K3 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·32·4⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;23;4) | K4 @0110243243: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-K4-at0110243243 : Complete 4 → ⟪ (Sb⁻1-0-42-3 ∷ K3 ∷ []) ⟫ʷ ≈ ⟪ (K3 ∷ Sb⁻1-0-42-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-K4-at0110243243 c4 = run b0
  where
  b0 : Chain (Sb⁻1-0-42-3 ∷ K3 ∷ []) (K3 ∷ Sb⁻1-0-42-3 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·42·3⟩ c4) ▸
       at 2 2 (K3 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑)) ▸
       at 1 2 (K3 ∷ Sb⁻0-1-42-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-K4-at243243 c4) ▸
       at 0 2 (K3 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑)) ▸
       at 1 2 (Sb⁻1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨0·1·42·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;23;4) | K4 @0210243143: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-K4-at0210243143 : Complete 4 → ⟪ (Sb⁻2-0-41-3 ∷ K3 ∷ []) ⟫ʷ ≈ ⟪ (K3 ∷ Sb⁻2-0-41-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-K4-at0210243143 c4 = run b0
  where
  b0 : Chain (Sb⁻2-0-41-3 ∷ K3 ∷ []) (K3 ∷ Sb⁻2-0-41-3 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·41·3⟩ c4) ▸
       at 2 2 (K3 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K)) ▸
       at 1 2 (K3 ∷ Sb⁻1-0-42-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-K4-at0110243243 c4) ▸
       at 0 2 (K3 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K)) ▸
       at 1 2 (Sb⁻2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·0·42·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;23;4) | CS24 @2332: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS24-at2332 : Complete 4 → ⟪ (Sb⁻0-1-32-4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ Sb⁻0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS24-at2332 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-32-4 ∷ CS34 ∷ []) (CS34 ∷ Sb⁻0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·32·4⟩ c4) ▸
       at 2 2 (CS24 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS34 ∷ []) (CS24 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS24 ∷ Sb⁻0-1-23-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS24 c4) ▸
       at 0 2 (CS34 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS24 ∷ []) (CS34 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;23;4) | CS24 @243243: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS24-at243243 : Complete 4 → ⟪ (Sb⁻0-1-42-3 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ Sb⁻0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS24-at243243 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-42-3 ∷ CS34 ∷ []) (CS34 ∷ Sb⁻0-1-42-3 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·42·3⟩ c4) ▸
       at 2 2 (CS34 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ CS34 ∷ []) (CS34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS34 ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS24-at2332 c4) ▸
       at 0 2 (CS34 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ CS34 ∷ []) (CS34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·32·4⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;23;4) | CS24 @0110243243: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS24-at0110243243 : Complete 4 → ⟪ (Sb⁻1-0-42-3 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ Sb⁻1-0-42-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS24-at0110243243 c4 = run b0
  where
  b0 : Chain (Sb⁻1-0-42-3 ∷ CS34 ∷ []) (CS34 ∷ Sb⁻1-0-42-3 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·42·3⟩ c4) ▸
       at 2 2 (CS34 ∷ Sw01 ∷ []) (c₂ (Swap) (CS ↑)) ▸
       at 1 2 (CS34 ∷ Sb⁻0-1-42-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS24-at243243 c4) ▸
       at 0 2 (CS34 ∷ Sw01 ∷ []) (c₂ (Swap) (CS ↑)) ▸
       at 1 2 (Sb⁻1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨0·1·42·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;23;4) | CS24 @0210243143: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS24-at0210243143 : Complete 4 → ⟪ (Sb⁻2-0-41-3 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ Sb⁻2-0-41-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS24-at0210243143 c4 = run b0
  where
  b0 : Chain (Sb⁻2-0-41-3 ∷ CS34 ∷ []) (CS34 ∷ Sb⁻2-0-41-3 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·41·3⟩ c4) ▸
       at 2 2 (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS)) ▸
       at 1 2 (CS34 ∷ Sb⁻1-0-42-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-CS24-at0110243243 c4) ▸
       at 0 2 (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS)) ▸
       at 1 2 (Sb⁻2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·0·42·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;23;4) | Kd4 @2332: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-Kd4-at2332 : Complete 4 → ⟪ (Sb⁻0-1-32-4 ∷ K4⁻ ∷ []) ⟫ʷ ≈ ⟪ (K4⁻ ∷ Sb⁻0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-Kd4-at2332 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-32-4 ∷ K4⁻ ∷ []) (K4⁻ ∷ Sb⁻0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·32·4⟩ c4) ▸
       at 2 2 (K4⁻ ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K • iI)) ▸
       at 1 2 (K4⁻ ∷ Sb⁻0-1-23-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-Kd4 c4) ▸
       at 0 2 (K4⁻ ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K • iI)) ▸
       at 1 2 (Sb⁻0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;23;4) | Kd4 @243243: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-Kd4-at243243 : Complete 4 → ⟪ (Sb⁻0-1-42-3 ∷ K3⁻ ∷ []) ⟫ʷ ≈ ⟪ (K3⁻ ∷ Sb⁻0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-Kd4-at243243 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-42-3 ∷ K3⁻ ∷ []) (K3⁻ ∷ Sb⁻0-1-42-3 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·42·3⟩ c4) ▸
       at 2 2 (K4⁻ ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ K3⁻ ∷ []) (K4⁻ ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (K4⁻ ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-Kd4-at2332 c4) ▸
       at 0 2 (K3⁻ ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ K4⁻ ∷ []) (K3⁻ ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·32·4⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;23;4) | Kd4 @0110243243: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-Kd4-at0110243243 : Complete 4 → ⟪ (Sb⁻1-0-42-3 ∷ K3⁻ ∷ []) ⟫ʷ ≈ ⟪ (K3⁻ ∷ Sb⁻1-0-42-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-Kd4-at0110243243 c4 = run b0
  where
  b0 : Chain (Sb⁻1-0-42-3 ∷ K3⁻ ∷ []) (K3⁻ ∷ Sb⁻1-0-42-3 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·42·3⟩ c4) ▸
       at 2 2 (K3⁻ ∷ Sw01 ∷ []) (c₂ (Swap) ((K • iI) ↑)) ▸
       at 1 2 (K3⁻ ∷ Sb⁻0-1-42-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-Kd4-at243243 c4) ▸
       at 0 2 (K3⁻ ∷ Sw01 ∷ []) (c₂ (Swap) ((K • iI) ↑)) ▸
       at 1 2 (Sb⁻1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨0·1·42·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;23;4) | Kd4 @0210243143: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-Kd4-at0210243143 : Complete 4 → ⟪ (Sb⁻2-0-41-3 ∷ K3⁻ ∷ []) ⟫ʷ ≈ ⟪ (K3⁻ ∷ Sb⁻2-0-41-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-Kd4-at0210243143 c4 = run b0
  where
  b0 : Chain (Sb⁻2-0-41-3 ∷ K3⁻ ∷ []) (K3⁻ ∷ Sb⁻2-0-41-3 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·41·3⟩ c4) ▸
       at 2 2 (K3⁻ ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K • iI)) ▸
       at 1 2 (K3⁻ ∷ Sb⁻1-0-42-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-Kd4-at0110243243 c4) ▸
       at 0 2 (K3⁻ ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K • iI)) ▸
       at 1 2 (Sb⁻2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·0·42·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;23;4) | SBOXd(0;1;4;3) @2332: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨0·1·4·3⟩-at2332 : Complete 4 → ⟪ (Sb⁻0-1-32-4 ∷ Sb⁻0-1-4-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-4-2 ∷ Sb⁻0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨0·1·4·3⟩-at2332 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-32-4 ∷ Sb⁻0-1-4-2 ∷ []) (Sb⁻0-1-4-2 ∷ Sb⁻0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·32·4⟩ c4) ▸
       at 2 2 (Sb⁻0-1-4-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·4·2⟩ c4) ▸
       at 1 2 (Sb⁻0-1-4-3 ∷ Sb⁻0-1-23-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨0·1·4·3⟩ c4) ▸
       at 0 2 (Sb⁻0-1-4-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·4·3⟩ c4) ▸
       at 1 2 (Sb⁻0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;23;4) | SBOXd(0;1;4;3) @243243: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨0·1·4·3⟩-at243243 : Complete 4 → ⟪ (Sb⁻0-1-42-3 ∷ Sb⁻0-1-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-3-2 ∷ Sb⁻0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨0·1·4·3⟩-at243243 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-42-3 ∷ Sb⁻0-1-3-2 ∷ []) (Sb⁻0-1-3-2 ∷ Sb⁻0-1-42-3 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·42·3⟩ c4) ▸
       at 2 2 (Sb⁻0-1-4-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·3·2⟩ c4) ▸
       at 1 2 (Sb⁻0-1-4-2 ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨0·1·4·3⟩-at2332 c4) ▸
       at 0 2 (Sb⁻0-1-3-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·4·2⟩ c4) ▸
       at 1 2 (Sb⁻0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·32·4⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;23;4) | SBOXd(0;1;4;3) @0110243243: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨0·1·4·3⟩-at0110243243 : Complete 4 → ⟪ (Sb⁻1-0-42-3 ∷ Sb⁻1-0-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-3-2 ∷ Sb⁻1-0-42-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨0·1·4·3⟩-at0110243243 c4 = run b0
  where
  b0 : Chain (Sb⁻1-0-42-3 ∷ Sb⁻1-0-3-2 ∷ []) (Sb⁻1-0-3-2 ∷ Sb⁻1-0-42-3 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·42·3⟩ c4) ▸
       at 2 2 (Sb⁻0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·3·2⟩ c4) ▸
       at 1 2 (Sb⁻0-1-3-2 ∷ Sb⁻0-1-42-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨0·1·4·3⟩-at243243 c4) ▸
       at 0 2 (Sb⁻1-0-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨0·1·3·2⟩ c4) ▸
       at 1 2 (Sb⁻1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨0·1·42·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;23;4) | SBOXd(0;1;4;3) @0210243143: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨0·1·4·3⟩-at0210243143 : Complete 4 → ⟪ (Sb⁻2-0-41-3 ∷ Sb⁻2-0-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-0-3-1 ∷ Sb⁻2-0-41-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨0·1·4·3⟩-at0210243143 c4 = run b0
  where
  b0 : Chain (Sb⁻2-0-41-3 ∷ Sb⁻2-0-3-1 ∷ []) (Sb⁻2-0-3-1 ∷ Sb⁻2-0-41-3 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·41·3⟩ c4) ▸
       at 2 2 (Sb⁻1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·3·1⟩ c4) ▸
       at 1 2 (Sb⁻1-0-3-2 ∷ Sb⁻1-0-42-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-SBOXd⟨0·1·4·3⟩-at0110243243 c4) ▸
       at 0 2 (Sb⁻2-0-3-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·0·3·2⟩ c4) ▸
       at 1 2 (Sb⁻2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·0·42·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;23;4) | TOFF012 @2332: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF012-at2332 : Complete 4 → ⟪ (Sb⁻0-1-32-4 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ Sb⁻0-1-32-4 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF012-at2332 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-32-4 ∷ Toff013 ∷ []) (Toff013 ∷ Sb⁻0-1-32-4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-23-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·32·4⟩ c4) ▸
       at 2 2 (Toff012 ∷ Sw23 ∷ []) (lem-nat-2-TOFF013 c4) ▸
       at 1 2 (Toff012 ∷ Sb⁻0-1-23-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF012 c4) ▸
       at 0 2 (Toff013 ∷ Sw23 ∷ []) (lem-nat-2-TOFF012 c4) ▸
       at 1 2 (Sb⁻0-1-32-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·23·4⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;23;4) | TOFF012 @243243: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF012-at243243 : Complete 4 → ⟪ (Sb⁻0-1-42-3 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ Sb⁻0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF012-at243243 c4 = run b0
  where
  b0 : Chain (Sb⁻0-1-42-3 ∷ Toff014 ∷ []) (Toff014 ∷ Sb⁻0-1-42-3 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·42·3⟩ c4) ▸
       at 2 2 (Toff013 ∷ Sw34 ∷ []) (lem-nat-3-TOFF014 c4) ▸
       at 1 2 (Toff013 ∷ Sb⁻0-1-32-4 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF012-at2332 c4) ▸
       at 0 2 (Toff014 ∷ Sw34 ∷ []) (lem-nat-3-TOFF013 c4) ▸
       at 1 2 (Sb⁻0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·32·4⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;23;4) | TOFF012 @0110243243: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF012-at0110243243 : Complete 4 → ⟪ (Sb⁻1-0-42-3 ∷ Toff104 ∷ []) ⟫ʷ ≈ ⟪ (Toff104 ∷ Sb⁻1-0-42-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF012-at0110243243 c4 = run b0
  where
  b0 : Chain (Sb⁻1-0-42-3 ∷ Toff104 ∷ []) (Toff104 ∷ Sb⁻1-0-42-3 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·42·3⟩ c4) ▸
       at 2 2 (Toff014 ∷ Sw01 ∷ []) (lem-nat-0-TOFF104 c4) ▸
       at 1 2 (Toff014 ∷ Sb⁻0-1-42-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF012-at243243 c4) ▸
       at 0 2 (Toff104 ∷ Sw01 ∷ []) (lem-nat-0-TOFF014 c4) ▸
       at 1 2 (Sb⁻1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨0·1·42·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto SBOXd(0;1;23;4) | TOFF012 @0210243143: 7 steps
lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF012-at0210243143 : Complete 4 → ⟪ (Sb⁻2-0-41-3 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ Sb⁻2-0-41-3 ∷ []) ⟫ʷ
lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF012-at0210243143 c4 = run b0
  where
  b0 : Chain (Sb⁻2-0-41-3 ∷ Toff204 ∷ []) (Toff204 ∷ Sb⁻2-0-41-3 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb⁻1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·41·3⟩ c4) ▸
       at 2 2 (Toff104 ∷ Sw12 ∷ []) (lem-nat-1-TOFF204 c4) ▸
       at 1 2 (Toff104 ∷ Sb⁻1-0-42-3 ∷ []) (lem-auto-SBOXd⟨0·1·23·4⟩-∣-TOFF012-at0110243243 c4) ▸
       at 0 2 (Toff204 ∷ Sw12 ∷ []) (lem-nat-1-TOFF104 c4) ▸
       at 1 2 (Sb⁻2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·0·42·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOXd(0;1234) | CS40 @2332: 7 steps
lem-auto-BOXd⟨0·1234⟩-∣-CS40-at2332 : Complete 4 → ⟪ (Bx⁻0-1324 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ Bx⁻0-1324 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-CS40-at2332 c4 = run b0
  where
  b0 : Chain (Bx⁻0-1324 ∷ CS04 ∷ []) (CS04 ∷ Bx⁻0-1324 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx⁻0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·1324⟩ c4) ▸
       at 2 2 (CS04 ∷ Sw23 ∷ []) (lem-nat-2-CS04 c4) ▸
       at 1 2 (CS04 ∷ Bx⁻0-1234 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-CS40 c4) ▸
       at 0 2 (CS04 ∷ Sw23 ∷ []) (lem-nat-2-CS04 c4) ▸
       at 1 2 (Bx⁻0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·1234⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOXd(0;1234) | CS40 @243243: 7 steps
lem-auto-BOXd⟨0·1234⟩-∣-CS40-at243243 : Complete 4 → ⟪ (Bx⁻0-1423 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Bx⁻0-1423 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-CS40-at243243 c4 = run b0
  where
  b0 : Chain (Bx⁻0-1423 ∷ CS03 ∷ []) (CS03 ∷ Bx⁻0-1423 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx⁻0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨0·1423⟩ c4) ▸
       at 2 2 (CS04 ∷ Sw34 ∷ []) (lem-nat-3-CS03 c4) ▸
       at 1 2 (CS04 ∷ Bx⁻0-1324 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-CS40-at2332 c4) ▸
       at 0 2 (CS03 ∷ Sw34 ∷ []) (lem-nat-3-CS04 c4) ▸
       at 1 2 (Bx⁻0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨0·1324⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOXd(0;1234) | CS40 @0110243243: 7 steps
lem-auto-BOXd⟨0·1234⟩-∣-CS40-at0110243243 : Complete 4 → ⟪ (Bx⁻1-0423 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Bx⁻1-0423 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-CS40-at0110243243 c4 = run b0
  where
  b0 : Chain (Bx⁻1-0423 ∷ CS13 ∷ []) (CS13 ∷ Bx⁻1-0423 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx⁻0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨1·0423⟩ c4) ▸
       at 2 2 (CS03 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS13 ∷ []) (CS03 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS03 ∷ Bx⁻0-1423 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-CS40-at243243 c4) ▸
       at 0 2 (CS13 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS03 ∷ []) (CS13 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx⁻1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨0·1423⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOXd(0;1234) | CS40 @0210243143: 7 steps
lem-auto-BOXd⟨0·1234⟩-∣-CS40-at0210243143 : Complete 4 → ⟪ (Bx⁻2-0413 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ Bx⁻2-0413 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-CS40-at0210243143 c4 = run b0
  where
  b0 : Chain (Bx⁻2-0413 ∷ CS23 ∷ []) (CS23 ∷ Bx⁻2-0413 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx⁻1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨2·0413⟩ c4) ▸
       at 2 2 (CS13 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS23 ∷ []) (CS13 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS13 ∷ Bx⁻1-0423 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-CS40-at0110243243 c4) ▸
       at 0 2 (CS23 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS13 ∷ []) (CS23 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx⁻2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨1·0423⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- beta-T @01102332: 8 steps
lem-beta-T-at01102332 : Complete 4 → ⟪ (Bx1-0324 ∷ []) ⟫ʷ ≈ ⟪ (Toff103 ∷ CCZ124 ∷ Toff103 ∷ CCZ124 ∷ []) ⟫ʷ
lem-beta-T-at01102332 c4 = run b0
  where
  b0 : Chain (Bx1-0324 ∷ []) (Toff103 ∷ CCZ124 ∷ Toff103 ∷ CCZ124 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1324 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0324⟩ c4) ▸
       at 1 1 (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) (lem-beta-T-at2332 c4) ▸
       at 0 2 (Toff103 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff013 ∷ []) (Toff103 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 2 2 (Toff103 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff013 ∷ []) (Toff103 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 4 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- beta-T @02102331: 8 steps
lem-beta-T-at02102331 : Complete 4 → ⟪ (Bx2-0314 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ []) ⟫ʷ
lem-beta-T-at02102331 c4 = run b0
  where
  b0 : Chain (Bx2-0314 ∷ []) (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-0324 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0314⟩ c4) ▸
       at 1 1 (Toff103 ∷ CCZ124 ∷ Toff103 ∷ CCZ124 ∷ []) (lem-beta-T-at01102332 c4) ▸
       at 0 2 (Toff203 ∷ Sw12 ∷ []) (lem-nat-1-TOFF103 c4) ▸
       at 1 2 (CCZ124 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff203 ∷ Sw12 ∷ []) (lem-nat-1-TOFF103 c4) ▸
       at 3 2 (CCZ124 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- beta-T @022330: 8 steps
lem-beta-T-at022330 : Complete 4 → ⟪ (Bx2-1304 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ []) ⟫ʷ
lem-beta-T-at022330 c4 = run b0
  where
  b0 : Chain (Bx2-1304 ∷ []) (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx2-0314 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·1304⟩ c4) ▸
       at 1 1 (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ []) (lem-beta-T-at02102331 c4) ▸
       at 0 2 (Toff213 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff203 ∷ []) (Toff213 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 2 2 (Toff213 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff203 ∷ []) (Toff213 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 4 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym34 @0220: 5 steps
lem-sym34-at0220 : Complete 4 → ⟪ (Bx2-1034 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1043 ∷ []) ⟫ʷ
lem-sym34-at0220 c4 = run b0
  where
  b0 : Chain (Bx2-1034 ∷ []) (Bx2-1043 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx2-0134 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·1034⟩ c4) ▸
       at 1 1 (Bx2-0143 ∷ []) (lem-sym34-at021021 c4) ▸
       at 0 2 (Bx2-1043 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·0143⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOXd(0;1234) | CSd40 @2332: 7 steps
lem-auto-BOXd⟨0·1234⟩-∣-CSd40-at2332 : Complete 4 → ⟪ (Bx⁻0-1324 ∷ CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS04⁻ ∷ Bx⁻0-1324 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-CSd40-at2332 c4 = run b0
  where
  b0 : Chain (Bx⁻0-1324 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ Bx⁻0-1324 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx⁻0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·1324⟩ c4) ▸
       at 2 2 (CS04⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd04 c4) ▸
       at 1 2 (CS04⁻ ∷ Bx⁻0-1234 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-CSd40 c4) ▸
       at 0 2 (CS04⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd04 c4) ▸
       at 1 2 (Bx⁻0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·1234⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOXd(0;1234) | CSd40 @243243: 7 steps
lem-auto-BOXd⟨0·1234⟩-∣-CSd40-at243243 : Complete 4 → ⟪ (Bx⁻0-1423 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ Bx⁻0-1423 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-CSd40-at243243 c4 = run b0
  where
  b0 : Chain (Bx⁻0-1423 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ Bx⁻0-1423 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx⁻0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨0·1423⟩ c4) ▸
       at 2 2 (CS04⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd03 c4) ▸
       at 1 2 (CS04⁻ ∷ Bx⁻0-1324 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-CSd40-at2332 c4) ▸
       at 0 2 (CS03⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd04 c4) ▸
       at 1 2 (Bx⁻0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨0·1324⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOXd(0;1234) | CSd40 @0110243243: 7 steps
lem-auto-BOXd⟨0·1234⟩-∣-CSd40-at0110243243 : Complete 4 → ⟪ (Bx⁻1-0423 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ Bx⁻1-0423 ∷ []) ⟫ʷ
lem-auto-BOXd⟨0·1234⟩-∣-CSd40-at0110243243 c4 = run b0
  where
  b0 : Chain (Bx⁻1-0423 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ Bx⁻1-0423 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx⁻0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨1·0423⟩ c4) ▸
       at 2 2 (CS03⁻ ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS13⁻ ∷ []) (CS03⁻ ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS03⁻ ∷ Bx⁻0-1423 ∷ []) (lem-auto-BOXd⟨0·1234⟩-∣-CSd40-at243243 c4) ▸
       at 0 2 (CS13⁻ ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS03⁻ ∷ []) (CS13⁻ ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx⁻1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨0·1423⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done

