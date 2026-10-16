{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D139 where

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
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-T312-beta-at0314203142 ; lem-T312-beta-at0314213240 ; lem-beta-inv-at0310243142 ; lem-sym12-at0314203142 ; lem-sym23-at0314203142 ; lem-sym23-at0314213042 ; lem-sym34-at0314213042 ; lem-sym34-at0314213240)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-F0 ; lem-T312-beta-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-SB2)
open import Examples.Groups.Clifford+CS.Five.D.D080 using (lem-sym12-at0310243142)
open import Examples.Groups.Clifford+CS.Five.D.D081 using (lem-sym34-at0310243142)
open import Examples.Groups.Clifford+CS.Five.D.D082 using (lem-sym34-at0310243241)
open import Examples.Groups.Clifford+CS.Five.D.D135 using (lem-auto-BOX⟨0·1234⟩-∣-CCZ243)
open import Examples.Groups.Clifford+CS.Five.D.D138 using (lem-F0-at011220 ; lem-F1-rel-266-nf-of-rhs ; lem-SB2-at011220 ; lem-T312-beta-at03143041 ; lem-T312-beta-at03143140 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ123 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0310243142 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0310243241 ; lem-auto-BOX⟨0·1234⟩-∣-CCZ241-at0310243142 ; lem-auto-BOX⟨0·1234⟩-∣-CS14-at0310243142 ; lem-auto-BOX⟨0·1234⟩-∣-CSd14-at0310243142 ; lem-sym12-at0314213240 ; lem-sym12-at03243240 ; lem-sym23-at0314213240 ; lem-sym23-at03143140 ; lem-sym34-at03143041 ; lem-sym34-at03143140)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-1-CCZ024 ; lem-nat-1-CCZ034 ; lem-nat-2-BOX⟨0·1234⟩ ; lem-nat-2-BOX⟨0·1324⟩ ; lem-nat-2-CCZ034 ; lem-nat-3-BOX⟨0·1423⟩)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-1-CCZ014 ; lem-nat-3-BOX⟨0·1324⟩)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-0-CCZ024 ; lem-nat-0-CCZ124 ; lem-nat-2-CCZ124 ; lem-nat-2-CCZ134)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-0-TOFF014 ; lem-nat-1-TOFF104)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-0-CCZ134)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-0-TOFF204 ; lem-nat-3-TOFF214)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-nat-2-TOFF104)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-0-BOX⟨0·1423⟩ ; lem-nat-1-BOX⟨1·0423⟩)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-nat-0-BOX⟨1·0423⟩ ; lem-nat-1-BOX⟨2·0413⟩ ; lem-nat-2-BOX⟨2·0413⟩ ; lem-nat-2-BOX⟨3·0412⟩ ; lem-nat-3-CCZ123 ; lem-nat-3-CCZ124)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-nat-2-CCZ014)
open import Examples.Groups.Clifford+CS.Five.D.R012 using (lem-nat-1-CS01 ; lem-nat-1-CS02)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-nat-1-BOX⟨3·0412⟩ ; lem-nat-1-CSd02)
open import Examples.Groups.Clifford+CS.Five.D.R015 using (lem-nat-1-CSd01)
open import Examples.Groups.Clifford+CS.Five.D.R024 using (lem-nat-0-BOX⟨3·0412⟩)
open import Examples.Groups.Clifford+CS.Five.D.R028 using (lem-nat-1-BOX⟨3·0421⟩)
open import Examples.Groups.Clifford+CS.Five.D.R032 using (lem-nat-0-BOX⟨3·0421⟩ ; lem-nat-0-BOX⟨3·1402⟩ ; lem-nat-0-BOX⟨3·1420⟩)
-- auto BOX(0;1234) | CCZ231 @03243240: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at03243240 : Complete 4 → ⟪ (Bx3-1420 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Bx3-1420 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at03243240 c4 = run b0
  where
  b0 : Chain (Bx3-1420 ∷ CCZ124 ∷ []) (CCZ124 ∷ Bx3-1420 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-0421 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1420⟩ c4) ▸
       at 2 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 1 2 (CCZ024 ∷ Bx3-0421 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0310243241 c4) ▸
       at 0 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 1 2 (Bx3-1420 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·0421⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CS14 @0310243241: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS14-at0310243241 : Complete 4 → ⟪ (Bx3-0421 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ Bx3-0421 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS14-at0310243241 c4 = run b0
  where
  b0 : Chain (Bx3-0421 ∷ CS01 ∷ []) (CS01 ∷ Bx3-0421 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-0412 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0421⟩ c4) ▸
       at 2 2 (CS02 ∷ Sw12 ∷ []) (lem-nat-1-CS01 c4) ▸
       at 1 2 (CS02 ∷ Bx3-0412 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS14-at0310243142 c4) ▸
       at 0 2 (CS01 ∷ Sw12 ∷ []) (lem-nat-1-CS02 c4) ▸
       at 1 2 (Bx3-0421 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0412⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CS14 @03243240: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CS14-at03243240 : Complete 4 → ⟪ (Bx3-1420 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ Bx3-1420 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CS14-at03243240 c4 = run b0
  where
  b0 : Chain (Bx3-1420 ∷ CS01 ∷ []) (CS01 ∷ Bx3-1420 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-0421 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1420⟩ c4) ▸
       at 2 2 (CS01 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS01 ∷ []) (CS01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS01 ∷ Bx3-0421 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS14-at0310243241 c4) ▸
       at 0 2 (CS01 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS01 ∷ []) (CS01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-1420 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·0421⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CSd14 @0310243241: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd14-at0310243241 : Complete 4 → ⟪ (Bx3-0421 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ Bx3-0421 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd14-at0310243241 c4 = run b0
  where
  b0 : Chain (Bx3-0421 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ Bx3-0421 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-0412 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0421⟩ c4) ▸
       at 2 2 (CS02⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd01 c4) ▸
       at 1 2 (CS02⁻ ∷ Bx3-0412 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd14-at0310243142 c4) ▸
       at 0 2 (CS01⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd02 c4) ▸
       at 1 2 (Bx3-0421 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0412⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CSd14 @03243240: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd14-at03243240 : Complete 4 → ⟪ (Bx3-1420 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ Bx3-1420 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd14-at03243240 c4 = run b0
  where
  b0 : Chain (Bx3-1420 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ Bx3-1420 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-0421 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1420⟩ c4) ▸
       at 2 2 (CS01⁻ ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS01⁻ ∷ Bx3-0421 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd14-at0310243241 c4) ▸
       at 0 2 (CS01⁻ ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-1420 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·0421⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ243 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at2332 : Complete 4 → ⟪ (Bx0-1324 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at2332 c4 = run b0
  where
  b0 : Chain (Bx0-1324 ∷ CCZ234 ∷ []) (CCZ234 ∷ Bx0-1324 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ c4) ▸
       at 2 2 (CCZ234 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ234 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ243 c4) ▸
       at 0 2 (CCZ234 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ243 @243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at243243 : Complete 4 → ⟪ (Bx0-1423 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Bx0-1423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at243243 c4 = run b0
  where
  b0 : Chain (Bx0-1423 ∷ CCZ234 ∷ []) (CCZ234 ∷ Bx0-1423 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ c4) ▸
       at 2 2 (CCZ234 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ234 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at2332 c4) ▸
       at 0 2 (CCZ234 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ243 @0110243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at0110243243 : Complete 4 → ⟪ (Bx1-0423 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Bx1-0423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at0110243243 c4 = run b0
  where
  b0 : Chain (Bx1-0423 ∷ CCZ234 ∷ []) (CCZ234 ∷ Bx1-0423 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ c4) ▸
       at 2 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 1 2 (CCZ234 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at243243 c4) ▸
       at 0 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 1 2 (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ243 @0210243143: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at0210243143 : Complete 4 → ⟪ (Bx2-0413 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Bx2-0413 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at0210243143 c4 = run b0
  where
  b0 : Chain (Bx2-0413 ∷ CCZ134 ∷ []) (CCZ134 ∷ Bx2-0413 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ c4) ▸
       at 2 2 (CCZ234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ134 ∷ []) (CCZ234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ234 ∷ Bx1-0423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at0110243243 c4) ▸
       at 0 2 (CCZ134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ234 ∷ []) (CCZ134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0423⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ243 @0310243142: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at0310243142 : Complete 4 → ⟪ (Bx3-0412 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Bx3-0412 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at0310243142 c4 = run b0
  where
  b0 : Chain (Bx3-0412 ∷ CCZ124 ∷ []) (CCZ124 ∷ Bx3-0412 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx2-0413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0412⟩ c4) ▸
       at 2 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 1 2 (CCZ134 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at0210243143 c4) ▸
       at 0 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 1 2 (Bx3-0412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0413⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ243 @0310243241: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at0310243241 : Complete 4 → ⟪ (Bx3-0421 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Bx3-0421 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at0310243241 c4 = run b0
  where
  b0 : Chain (Bx3-0421 ∷ CCZ124 ∷ []) (CCZ124 ∷ Bx3-0421 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-0412 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0421⟩ c4) ▸
       at 2 2 (CCZ124 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ124 ∷ Bx3-0412 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at0310243142 c4) ▸
       at 0 2 (CCZ124 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-0421 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0412⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ243 @03243240: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at03243240 : Complete 4 → ⟪ (Bx3-1420 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Bx3-1420 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at03243240 c4 = run b0
  where
  b0 : Chain (Bx3-1420 ∷ CCZ024 ∷ []) (CCZ024 ∷ Bx3-1420 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-0421 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1420⟩ c4) ▸
       at 2 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 1 2 (CCZ124 ∷ Bx3-0421 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at0310243241 c4) ▸
       at 0 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 1 2 (Bx3-1420 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·0421⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym34 @03243240: 5 steps
lem-sym34-at03243240 : Complete 4 → ⟪ (Bx3-1420 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1402 ∷ []) ⟫ʷ
lem-sym34-at03243240 c4 = run b0
  where
  b0 : Chain (Bx3-1420 ∷ []) (Bx3-1402 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-0421 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1420⟩ c4) ▸
       at 1 1 (Bx3-0412 ∷ []) (lem-sym34-at0310243241 c4) ▸
       at 0 2 (Bx3-1402 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·0412⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- T312-beta @243243: 8 steps
lem-T312-beta-at243243 : Complete 4 → ⟪ (Toff214 ∷ Bx0-1423 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ CCZ134 ∷ []) ⟫ʷ
lem-T312-beta-at243243 c4 = run b0
  where
  b0 : Chain (Toff214 ∷ Bx0-1423 ∷ Toff214 ∷ []) (Bx0-1423 ∷ CCZ134 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff213 ∷ Sw34 ∷ []) (lem-nat-3-TOFF214 c4) ▸
       at 2 2 (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ c4) ▸
       at 3 2 (Toff213 ∷ Sw34 ∷ []) (lem-nat-3-TOFF214 c4) ▸
       at 1 3 (Bx0-1324 ∷ CCZ134 ∷ []) (lem-T312-beta-at2332 c4) ▸
       at 0 2 (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ c4) ▸
       at 1 2 (CCZ134 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ CCZ134 ∷ []) (CCZ134 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- T312-beta @0110243243: 8 steps
lem-T312-beta-at0110243243 : Complete 4 → ⟪ (Toff204 ∷ Bx1-0423 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0423 ∷ CCZ034 ∷ []) ⟫ʷ
lem-T312-beta-at0110243243 c4 = run b0
  where
  b0 : Chain (Toff204 ∷ Bx1-0423 ∷ Toff204 ∷ []) (Bx1-0423 ∷ CCZ034 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff214 ∷ Sw01 ∷ []) (lem-nat-0-TOFF204 c4) ▸
       at 2 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ c4) ▸
       at 3 2 (Toff214 ∷ Sw01 ∷ []) (lem-nat-0-TOFF204 c4) ▸
       at 1 3 (Bx0-1423 ∷ CCZ134 ∷ []) (lem-T312-beta-at243243 c4) ▸
       at 0 2 (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ c4) ▸
       at 1 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- T312-beta @0210243143: 8 steps
lem-T312-beta-at0210243143 : Complete 4 → ⟪ (Toff104 ∷ Bx2-0413 ∷ Toff104 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ CCZ034 ∷ []) ⟫ʷ
lem-T312-beta-at0210243143 c4 = run b0
  where
  b0 : Chain (Toff104 ∷ Bx2-0413 ∷ Toff104 ∷ []) (Bx2-0413 ∷ CCZ034 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff204 ∷ Sw12 ∷ []) (lem-nat-1-TOFF104 c4) ▸
       at 2 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ c4) ▸
       at 3 2 (Toff204 ∷ Sw12 ∷ []) (lem-nat-1-TOFF104 c4) ▸
       at 1 3 (Bx1-0423 ∷ CCZ034 ∷ []) (lem-T312-beta-at0110243243 c4) ▸
       at 0 2 (Bx2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0423⟩ c4) ▸
       at 1 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- T312-beta @0310243142: 8 steps
lem-T312-beta-at0310243142 : Complete 4 → ⟪ (Toff104 ∷ Bx3-0412 ∷ Toff104 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ CCZ024 ∷ []) ⟫ʷ
lem-T312-beta-at0310243142 c4 = run b0
  where
  b0 : Chain (Toff104 ∷ Bx3-0412 ∷ Toff104 ∷ []) (Bx3-0412 ∷ CCZ024 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff104 ∷ Sw23 ∷ []) (lem-nat-2-TOFF104 c4) ▸
       at 2 2 (Bx2-0413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0412⟩ c4) ▸
       at 3 2 (Toff104 ∷ Sw23 ∷ []) (lem-nat-2-TOFF104 c4) ▸
       at 1 3 (Bx2-0413 ∷ CCZ034 ∷ []) (lem-T312-beta-at0210243143 c4) ▸
       at 0 2 (Bx3-0412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0413⟩ c4) ▸
       at 1 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- T312-beta @03243042: 8 steps
lem-T312-beta-at03243042 : Complete 4 → ⟪ (Toff014 ∷ Bx3-1402 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1402 ∷ CCZ124 ∷ []) ⟫ʷ
lem-T312-beta-at03243042 c4 = run b0
  where
  b0 : Chain (Toff014 ∷ Bx3-1402 ∷ Toff014 ∷ []) (Bx3-1402 ∷ CCZ124 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff104 ∷ Sw01 ∷ []) (lem-nat-0-TOFF014 c4) ▸
       at 2 2 (Bx3-0412 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1402⟩ c4) ▸
       at 3 2 (Toff104 ∷ Sw01 ∷ []) (lem-nat-0-TOFF014 c4) ▸
       at 1 3 (Bx3-0412 ∷ CCZ024 ∷ []) (lem-T312-beta-at0310243142 c4) ▸
       at 0 2 (Bx3-1402 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·0412⟩ c4) ▸
       at 1 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym34 @03243042: 5 steps
lem-sym34-at03243042 : Complete 4 → ⟪ (Bx3-1402 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1420 ∷ []) ⟫ʷ
lem-sym34-at03243042 c4 = run b0
  where
  b0 : Chain (Bx3-1402 ∷ []) (Bx3-1420 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-0412 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1402⟩ c4) ▸
       at 1 1 (Bx3-0421 ∷ []) (lem-sym34-at0310243142 c4) ▸
       at 0 2 (Bx3-1420 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·0421⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ123 @2332: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ123-at2332 : Complete 4 → ⟪ (Bx0-1324 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Bx0-1324 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ123-at2332 c4 = run b0
  where
  b0 : Chain (Bx0-1324 ∷ CCZ123 ∷ []) (CCZ123 ∷ Bx0-1324 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ c4) ▸
       at 2 2 (CCZ123 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ123 ∷ Bx0-1234 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ123 c4) ▸
       at 0 2 (CCZ123 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ123 @243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ123-at243243 : Complete 4 → ⟪ (Bx0-1423 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Bx0-1423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ123-at243243 c4 = run b0
  where
  b0 : Chain (Bx0-1423 ∷ CCZ124 ∷ []) (CCZ124 ∷ Bx0-1423 ∷ [])
  b0 = at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ c4) ▸
       at 2 2 (CCZ123 ∷ Sw34 ∷ []) (lem-nat-3-CCZ124 c4) ▸
       at 1 2 (CCZ123 ∷ Bx0-1324 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ123-at2332 c4) ▸
       at 0 2 (CCZ124 ∷ Sw34 ∷ []) (lem-nat-3-CCZ123 c4) ▸
       at 1 2 (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ c4) ▸
       at 2 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ123 @0110243243: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ123-at0110243243 : Complete 4 → ⟪ (Bx1-0423 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Bx1-0423 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ123-at0110243243 c4 = run b0
  where
  b0 : Chain (Bx1-0423 ∷ CCZ024 ∷ []) (CCZ024 ∷ Bx1-0423 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ c4) ▸
       at 2 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 1 2 (CCZ124 ∷ Bx0-1423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ123-at243243 c4) ▸
       at 0 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 1 2 (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ123 @0210243143: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ123-at0210243143 : Complete 4 → ⟪ (Bx2-0413 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ Bx2-0413 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ123-at0210243143 c4 = run b0
  where
  b0 : Chain (Bx2-0413 ∷ CCZ014 ∷ []) (CCZ014 ∷ Bx2-0413 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ c4) ▸
       at 2 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 1 2 (CCZ024 ∷ Bx1-0423 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ123-at0110243243 c4) ▸
       at 0 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 1 2 (Bx2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0423⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ123 @0310243142: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ123-at0310243142 : Complete 4 → ⟪ (Bx3-0412 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ Bx3-0412 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ123-at0310243142 c4 = run b0
  where
  b0 : Chain (Bx3-0412 ∷ CCZ014 ∷ []) (CCZ014 ∷ Bx3-0412 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx2-0413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0412⟩ c4) ▸
       at 2 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 1 2 (CCZ014 ∷ Bx2-0413 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ123-at0210243143 c4) ▸
       at 0 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 1 2 (Bx3-0412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0413⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ123 @0310243241: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ123-at0310243241 : Complete 4 → ⟪ (Bx3-0421 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Bx3-0421 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ123-at0310243241 c4 = run b0
  where
  b0 : Chain (Bx3-0421 ∷ CCZ024 ∷ []) (CCZ024 ∷ Bx3-0421 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-0412 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0421⟩ c4) ▸
       at 2 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 1 2 (CCZ014 ∷ Bx3-0412 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ123-at0310243142 c4) ▸
       at 0 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 1 2 (Bx3-0421 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0412⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- auto BOX(0;1234) | CCZ123 @03243240: 7 steps
lem-auto-BOX⟨0·1234⟩-∣-CCZ123-at03243240 : Complete 4 → ⟪ (Bx3-1420 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Bx3-1420 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CCZ123-at03243240 c4 = run b0
  where
  b0 : Chain (Bx3-1420 ∷ CCZ124 ∷ []) (CCZ124 ∷ Bx3-1420 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-0421 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1420⟩ c4) ▸
       at 2 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 1 2 (CCZ024 ∷ Bx3-0421 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ123-at0310243241 c4) ▸
       at 0 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 1 2 (Bx3-1420 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·0421⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- F1 rel-266: 55 steps
lem-F1-rel-266 : Complete 4 → ⟪ (CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ S4 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ []) ⟫ʷ
lem-F1-rel-266 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (run b6))))))
  where
  b0 : Chain (CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ S4 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ S4 ∷ []) (Toff014 ∷ Toff104 ∷ Sb0-1-42-3 ∷ Toff104 ∷ Toff014 ∷ [])
  b0 = at 1 2 (CCZ014 ∷ []) (lem-SB2 c4) ▸
       at 5 2 (CCZ014 ∷ []) (lem-SB2 c4) ▸
       at 10 2 (CCZ014 ∷ []) (lem-SB2 c4) ▸
       at 14 2 (CCZ014 ∷ []) (lem-SB2 c4) ▸
       at 0 4 (Toff014 ∷ []) (pw2 c4 (CK40 ∷ CCZ014 ∷ CK40 ∷ S4 ∷ []) (Toff014 ∷ []) tt tt Eq.refl) ▸
       at 1 4 (Toff104 ∷ []) (pw2 c4 (CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ []) (Toff104 ∷ []) tt tt Eq.refl) ▸
       at 3 4 (Toff104 ∷ []) (pw2 c4 (CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ []) (Toff104 ∷ []) tt tt Eq.refl) ▸
       at 4 4 (Toff014 ∷ []) (pw2 c4 (CK40 ∷ CCZ014 ∷ CK40 ∷ S4 ∷ []) (Toff014 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Toff014 ∷ Toff104 ∷ Sb0-1-42-3 ∷ Toff104 ∷ Toff014 ∷ []) (Toff014 ∷ Toff104 ∷ Toff024 ∷ Toff024 ∷ Bx3-4201 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ Toff014 ∷ [])
  b1 = at 2 1 (Sb3-1-42-0 ∷ []) (lem-F0-at011220 c4) ▸
       at 2 1 (Bx3-1420 ∷ Toff024 ∷ Sb3-1-0-2 ∷ Toff024 ∷ Sb⁻3-1-0-2 ∷ []) (refl) ▸
       at 4 1 (CS01 ∷ []) (refl) ▸
       at 6 1 (CS01⁻ ∷ []) (refl) ▸
       at 2 0 (Toff024 ∷ Toff024 ∷ []) (pw1 c4 [] (Toff024 ∷ Toff024 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Bx3-4120 ∷ []) (lem-sym12-at03243240 c4) ▸
       at 4 1 (Bx3-4210 ∷ []) (lem-sym23-at0314213240 c4) ▸
       at 4 1 (Bx3-4201 ∷ []) (lem-sym34-at03143140 c4) ▸ done

  b2 : Chain (Toff014 ∷ Toff104 ∷ Toff024 ∷ Toff024 ∷ Bx3-4201 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ Toff014 ∷ []) (Toff014 ∷ Toff104 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ Toff024 ∷ Bx3-4120 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ Toff014 ∷ [])
  b2 = at 3 3 (Bx3-4201 ∷ CCZ124 ∷ []) (lem-T312-beta-at03143041 c4) ▸
       at 3 1 (Bx3-4210 ∷ []) (lem-sym34-at03143041 c4) ▸
       at 3 1 (Bx3-4120 ∷ []) (lem-sym23-at03143140 c4) ▸
       at 3 1 (Bx3-1420 ∷ []) (lem-sym12-at0314213240 c4) ▸
       at 3 2 (CCZ124 ∷ Bx3-1420 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at03243240 c4) ▸
       at 4 2 (CS01 ∷ Bx3-1420 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS14-at03243240 c4) ▸
       at 5 0 (Toff024 ∷ Toff024 ∷ []) (pw1 c4 [] (Toff024 ∷ Toff024 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (Bx3-4120 ∷ []) (lem-sym12-at03243240 c4) ▸ done

  b3 : Chain (Toff014 ∷ Toff104 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ Toff024 ∷ Bx3-4120 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ Toff014 ∷ []) (Toff014 ∷ Toff104 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Bx3-1420 ∷ Toff104 ∷ Toff014 ∷ [])
  b3 = at 7 1 (Bx3-4210 ∷ []) (lem-sym23-at0314213240 c4) ▸
       at 7 1 (Bx3-4201 ∷ []) (lem-sym34-at03143140 c4) ▸
       at 6 3 (Bx3-4201 ∷ CCZ124 ∷ []) (lem-T312-beta-at03143041 c4) ▸
       at 6 1 (Bx3-4210 ∷ []) (lem-sym34-at03143041 c4) ▸
       at 6 1 (Bx3-4120 ∷ []) (lem-sym23-at03143140 c4) ▸
       at 6 1 (Bx3-1420 ∷ []) (lem-sym12-at0314213240 c4) ▸
       at 6 2 (CCZ124 ∷ Bx3-1420 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at03243240 c4) ▸
       at 7 2 (CS01⁻ ∷ Bx3-1420 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd14-at03243240 c4) ▸ done

  b4 : Chain (Toff014 ∷ Toff104 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Bx3-1420 ∷ Toff104 ∷ Toff014 ∷ []) (Toff014 ∷ Toff104 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ Bx3-1420 ∷ CCZ024 ∷ Toff014 ∷ [])
  b4 = at 8 0 (Toff104 ∷ Toff104 ∷ []) (pw2 c4 [] (Toff104 ∷ Toff104 ∷ []) tt tt Eq.refl) ▸
       at 10 1 (Bx3-4120 ∷ []) (lem-sym12-at03243240 c4) ▸
       at 10 1 (Bx3-4102 ∷ []) (lem-sym34-at0314213240 c4) ▸
       at 10 1 (Bx3-4012 ∷ []) (lem-sym23-at0314213042 c4) ▸
       at 9 3 (Bx3-4012 ∷ CCZ024 ∷ []) (lem-T312-beta-at0314203142 c4) ▸
       at 9 1 (Bx3-4102 ∷ []) (lem-sym23-at0314203142 c4) ▸
       at 9 1 (Bx3-4120 ∷ []) (lem-sym34-at0314213042 c4) ▸
       at 9 1 (Bx3-1420 ∷ []) (lem-sym12-at0314213240 c4) ▸ done

  b5 : Chain (Toff014 ∷ Toff104 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ Bx3-1420 ∷ CCZ024 ∷ Toff014 ∷ []) (Toff014 ∷ Toff104 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff014 ∷ CCZ124 ∷ Bx3-1420 ∷ [])
  b5 = at 9 2 (CCZ024 ∷ Bx3-1420 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ243-at03243240 c4) ▸
       at 10 0 (Toff014 ∷ Toff014 ∷ []) (pw2 c4 [] (Toff014 ∷ Toff014 ∷ []) tt tt Eq.refl) ▸
       at 11 1 (Toff014 ∷ []) (pw2 c4 (Toff014 ∷ []) (Toff014 ∷ []) tt tt Eq.refl) ▸
       at 13 1 (Toff014 ∷ []) (pw2 c4 (Toff014 ∷ []) (Toff014 ∷ []) tt tt Eq.refl) ▸
       at 12 1 (Bx3-1402 ∷ []) (lem-sym34-at03243240 c4) ▸
       at 11 3 (Bx3-1402 ∷ CCZ124 ∷ []) (lem-T312-beta-at03243042 c4) ▸
       at 11 1 (Bx3-1420 ∷ []) (lem-sym34-at03243042 c4) ▸
       at 11 2 (CCZ124 ∷ Bx3-1420 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ123-at03243240 c4) ▸ done

  b6 : Chain (Toff014 ∷ Toff104 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff014 ∷ CCZ124 ∷ Bx3-1420 ∷ []) (CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ [])
  b6 = at 12 1 (Bx3-4120 ∷ []) (lem-sym12-at03243240 c4) ▸
       at 12 1 (Bx3-4102 ∷ []) (lem-sym34-at0314213240 c4) ▸
       at 12 1 (Bx3-4012 ∷ []) (lem-sym23-at0314213042 c4) ▸
       at 12 1 (Bx3-0412 ∷ []) (lem-sym12-at0314203142 c4) ▸
       at 9 2 (Toff014 ∷ CCZ024 ∷ CCZ124 ∷ []) (pw3 c4 (CCZ024 ∷ Toff014 ∷ []) (Toff014 ∷ CCZ024 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 0 13 (Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ Toff124 ∷ CCZ014 ∷ CCZ024 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ []) (pw3 c4 (Toff014 ∷ Toff104 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ Toff014 ∷ CCZ024 ∷ CCZ124 ∷ CCZ124 ∷ []) (Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ Toff124 ∷ CCZ014 ∷ CCZ024 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 0 15 (CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ []) (sym (lem-F1-rel-266-nf-of-rhs c4)) ▸ done


-- F1 rel-267 [nf of rhs]: 7 steps
lem-F1-rel-267-nf-of-rhs : Complete 4 → ⟪ (CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Toff104 ∷ Toff104 ∷ CCZ024 ∷ CCZ124 ∷ CCZ124 ∷ []) ⟫ʷ
lem-F1-rel-267-nf-of-rhs c4 = run b0
  where
  b0 : Chain (CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ []) (Toff104 ∷ Toff104 ∷ CCZ024 ∷ CCZ124 ∷ CCZ124 ∷ [])
  b0 = at 1 2 (CCZ014 ∷ []) (lem-SB2 c4) ▸
       at 4 2 (CCZ124 ∷ []) (lem-SB2-at011220 c4) ▸
       at 6 2 (CCZ014 ∷ []) (lem-SB2 c4) ▸
       at 9 2 (CCZ124 ∷ []) (lem-SB2-at011220 c4) ▸
       at 0 4 (Toff104 ∷ []) (pw2 c4 (CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ []) (Toff104 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Toff104 ∷ []) (pw2 c4 (CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ []) (Toff104 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff104 ∷ CCZ024 ∷ CCZ124 ∷ []) (pw3 c4 (CCZ124 ∷ Toff104 ∷ []) (Toff104 ∷ CCZ024 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸ done


-- F1 rel-267: 15 steps
lem-F1-rel-267 : Complete 4 → ⟪ (CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ S4 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-F1-rel-267 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ S4 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ S4 ∷ []) (Toff014 ∷ Toff104 ∷ CCZ124 ∷ Toff104 ∷ CK40 ∷ CCZ014 ∷ CK40 ∷ S4 ∷ [])
  b0 = at 1 2 (CCZ014 ∷ []) (lem-SB2 c4) ▸
       at 5 2 (CCZ014 ∷ []) (lem-SB2 c4) ▸
       at 8 2 (CCZ124 ∷ []) (lem-SB2-at011220 c4) ▸
       at 10 2 (CCZ014 ∷ []) (lem-SB2 c4) ▸
       at 14 2 (CCZ014 ∷ []) (lem-SB2 c4) ▸
       at 0 4 (Toff014 ∷ []) (pw2 c4 (CK40 ∷ CCZ014 ∷ CK40 ∷ S4 ∷ []) (Toff014 ∷ []) tt tt Eq.refl) ▸
       at 1 4 (Toff104 ∷ []) (pw2 c4 (CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ []) (Toff104 ∷ []) tt tt Eq.refl) ▸
       at 3 4 (Toff104 ∷ []) (pw2 c4 (CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ []) (Toff104 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Toff014 ∷ Toff104 ∷ CCZ124 ∷ Toff104 ∷ CK40 ∷ CCZ014 ∷ CK40 ∷ S4 ∷ []) (CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ [])
  b1 = at 4 4 (Toff014 ∷ []) (pw2 c4 (CK40 ∷ CCZ014 ∷ CK40 ∷ S4 ∷ []) (Toff014 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff104 ∷ CCZ024 ∷ CCZ124 ∷ []) (pw3 c4 (CCZ124 ∷ Toff104 ∷ []) (Toff104 ∷ CCZ024 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff014 ∷ CCZ124 ∷ []) (pw3 c4 (CCZ124 ∷ Toff014 ∷ []) (Toff014 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff014 ∷ CCZ024 ∷ CCZ124 ∷ []) (pw3 c4 (CCZ024 ∷ Toff014 ∷ []) (Toff014 ∷ CCZ024 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 5 2 [] (lw0 c4 (CCZ124 ∷ CCZ124 ∷ []) [] tt tt Eq.refl) ▸
       at 0 5 (Toff104 ∷ Toff104 ∷ CCZ024 ∷ CCZ124 ∷ CCZ124 ∷ []) (pw3 c4 (Toff014 ∷ Toff104 ∷ Toff104 ∷ Toff014 ∷ CCZ024 ∷ []) (Toff104 ∷ Toff104 ∷ CCZ024 ∷ CCZ124 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 0 5 (CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F1-rel-267-nf-of-rhs c4)) ▸ done


-- F1 rel-268 [nf of rhs]: 122 steps
lem-F1-rel-268-nf-of-rhs : Complete 4 → ⟪ (Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ Toff124 ∷ CCZ014 ∷ CCZ024 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ Toff124 ∷ CS02⁻ ∷ []) ⟫ʷ
lem-F1-rel-268-nf-of-rhs c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (run b15)))))))))))))))
  where
  b0 : Chain (Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ []) (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ Toff124 ∷ CCZ014 ∷ Sb2-0-41-3 ∷ Toff124 ∷ [])
  b0 = at 2 2 (CCZ124 ∷ []) (lem-SB2-at011220 c4) ▸
       at 5 2 (CCZ014 ∷ []) (lem-SB2 c4) ▸
       at 8 2 (CCZ124 ∷ []) (lem-SB2-at011220 c4) ▸
       at 1 4 (Toff124 ∷ []) (lw0 c4 (CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ []) (Toff124 ∷ []) tt tt Eq.refl) ▸
       at 4 4 (Toff124 ∷ []) (lw0 c4 (CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ []) (Toff124 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb3-0-41-2 ∷ []) (lem-F0 c4) ▸
       at 0 1 (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (refl) ▸
       at 2 1 (CS02 ∷ []) (refl) ▸ done

  b1 : Chain (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ Toff124 ∷ CCZ014 ∷ Sb2-0-41-3 ∷ Toff124 ∷ []) (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff124 ∷ CCZ014 ∷ Toff214 ∷ Toff214 ∷ Bx3-4102 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff124 ∷ [])
  b1 = at 4 1 (CS02⁻ ∷ []) (refl) ▸
       at 7 1 (Sb3-0-41-2 ∷ []) (lem-F0 c4) ▸
       at 7 1 (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (refl) ▸
       at 9 1 (CS02 ∷ []) (refl) ▸
       at 11 1 (CS02⁻ ∷ []) (refl) ▸
       at 7 0 (Toff214 ∷ Toff214 ∷ []) (lw0 c4 [] (Toff214 ∷ Toff214 ∷ []) tt tt Eq.refl) ▸
       at 9 1 (Bx3-4012 ∷ []) (lem-sym12-at0310243142 c4) ▸
       at 9 1 (Bx3-4102 ∷ []) (lem-sym23-at0314203142 c4) ▸ done

  b2 : Chain (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff124 ∷ CCZ014 ∷ Toff214 ∷ Toff214 ∷ Bx3-4102 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff124 ∷ []) (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff124 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ Toff214 ∷ Bx3-0412 ∷ Toff214 ∷ CS02⁻ ∷ Toff124 ∷ [])
  b2 = at 9 1 (Bx3-4120 ∷ []) (lem-sym34-at0314213042 c4) ▸
       at 8 3 (Bx3-4120 ∷ CCZ014 ∷ []) (lem-T312-beta-at0314213240 c4) ▸
       at 8 1 (Bx3-4102 ∷ []) (lem-sym34-at0314213240 c4) ▸
       at 8 1 (Bx3-4012 ∷ []) (lem-sym23-at0314213042 c4) ▸
       at 8 1 (Bx3-0412 ∷ []) (lem-sym12-at0314203142 c4) ▸
       at 8 2 (CCZ014 ∷ Bx3-0412 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0310243142 c4) ▸
       at 9 2 (CS02 ∷ Bx3-0412 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS14-at0310243142 c4) ▸
       at 10 0 (Toff214 ∷ Toff214 ∷ []) (lw0 c4 [] (Toff214 ∷ Toff214 ∷ []) tt tt Eq.refl) ▸ done

  b3 : Chain (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff124 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ Toff214 ∷ Bx3-0412 ∷ Toff214 ∷ CS02⁻ ∷ Toff124 ∷ []) (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff124 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ CS02⁻ ∷ Toff124 ∷ [])
  b3 = at 12 1 (Bx3-4012 ∷ []) (lem-sym12-at0310243142 c4) ▸
       at 12 1 (Bx3-4102 ∷ []) (lem-sym23-at0314203142 c4) ▸
       at 12 1 (Bx3-4120 ∷ []) (lem-sym34-at0314213042 c4) ▸
       at 11 3 (Bx3-4120 ∷ CCZ014 ∷ []) (lem-T312-beta-at0314213240 c4) ▸
       at 11 1 (Bx3-4102 ∷ []) (lem-sym34-at0314213240 c4) ▸
       at 11 1 (Bx3-4012 ∷ []) (lem-sym23-at0314213042 c4) ▸
       at 11 1 (Bx3-0412 ∷ []) (lem-sym12-at0314203142 c4) ▸
       at 11 2 (CCZ014 ∷ Bx3-0412 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0310243142 c4) ▸ done

  b4 : Chain (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff124 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ CS02⁻ ∷ Toff124 ∷ []) (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff124 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff124 ∷ Bx3-4120 ∷ CCZ024 ∷ [])
  b4 = at 12 2 (CS02⁻ ∷ Bx3-0412 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd14-at0310243142 c4) ▸
       at 13 0 (Toff124 ∷ Toff124 ∷ []) (lw0 c4 [] (Toff124 ∷ Toff124 ∷ []) tt tt Eq.refl) ▸
       at 15 1 (Bx3-4012 ∷ []) (lem-sym12-at0310243142 c4) ▸
       at 15 1 (Bx3-4102 ∷ []) (lem-sym23-at0314203142 c4) ▸
       at 15 1 (Bx3-4120 ∷ []) (lem-sym34-at0314213042 c4) ▸
       at 15 1 (Bx3-4210 ∷ []) (lem-sym23-at0314213240 c4) ▸
       at 14 3 (Bx3-4210 ∷ CCZ024 ∷ []) (lem-T312-beta-at03143140 c4) ▸
       at 14 1 (Bx3-4120 ∷ []) (lem-sym23-at03143140 c4) ▸ done

  b5 : Chain (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff124 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff124 ∷ Bx3-4120 ∷ CCZ024 ∷ []) (Toff214 ∷ Toff214 ∷ Bx3-4120 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff124 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff124 ∷ CCZ024 ∷ Bx3-0412 ∷ [])
  b5 = at 14 1 (Bx3-4102 ∷ []) (lem-sym34-at0314213240 c4) ▸
       at 14 1 (Bx3-4012 ∷ []) (lem-sym23-at0314213042 c4) ▸
       at 14 1 (Bx3-0412 ∷ []) (lem-sym12-at0314203142 c4) ▸
       at 14 2 (CCZ024 ∷ Bx3-0412 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ241-at0310243142 c4) ▸
       at 0 0 (Toff214 ∷ Toff214 ∷ []) (lw0 c4 [] (Toff214 ∷ Toff214 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Bx3-4012 ∷ []) (lem-sym12-at0310243142 c4) ▸
       at 2 1 (Bx3-4102 ∷ []) (lem-sym23-at0314203142 c4) ▸
       at 2 1 (Bx3-4120 ∷ []) (lem-sym34-at0314213042 c4) ▸ done

  b6 : Chain (Toff214 ∷ Toff214 ∷ Bx3-4120 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff124 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff124 ∷ CCZ024 ∷ Bx3-0412 ∷ []) (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ Toff214 ∷ Bx3-4012 ∷ Toff214 ∷ CS02⁻ ∷ Toff124 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff124 ∷ CCZ024 ∷ Bx3-0412 ∷ [])
  b6 = at 1 3 (Bx3-4120 ∷ CCZ014 ∷ []) (lem-T312-beta-at0314213240 c4) ▸
       at 1 1 (Bx3-4102 ∷ []) (lem-sym34-at0314213240 c4) ▸
       at 1 1 (Bx3-4012 ∷ []) (lem-sym23-at0314213042 c4) ▸
       at 1 1 (Bx3-0412 ∷ []) (lem-sym12-at0314203142 c4) ▸
       at 1 2 (CCZ014 ∷ Bx3-0412 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0310243142 c4) ▸
       at 2 2 (CS02 ∷ Bx3-0412 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS14-at0310243142 c4) ▸
       at 3 0 (Toff214 ∷ Toff214 ∷ []) (lw0 c4 [] (Toff214 ∷ Toff214 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Bx3-4012 ∷ []) (lem-sym12-at0310243142 c4) ▸ done

  b7 : Chain (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ Toff214 ∷ Bx3-4012 ∷ Toff214 ∷ CS02⁻ ∷ Toff124 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff124 ∷ CCZ024 ∷ Bx3-0412 ∷ []) (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Bx3-0412 ∷ Toff124 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff124 ∷ CCZ024 ∷ Bx3-0412 ∷ [])
  b7 = at 5 1 (Bx3-4102 ∷ []) (lem-sym23-at0314203142 c4) ▸
       at 5 1 (Bx3-4120 ∷ []) (lem-sym34-at0314213042 c4) ▸
       at 4 3 (Bx3-4120 ∷ CCZ014 ∷ []) (lem-T312-beta-at0314213240 c4) ▸
       at 4 1 (Bx3-4102 ∷ []) (lem-sym34-at0314213240 c4) ▸
       at 4 1 (Bx3-4012 ∷ []) (lem-sym23-at0314213042 c4) ▸
       at 4 1 (Bx3-0412 ∷ []) (lem-sym12-at0314203142 c4) ▸
       at 4 2 (CCZ014 ∷ Bx3-0412 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0310243142 c4) ▸
       at 5 2 (CS02⁻ ∷ Bx3-0412 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd14-at0310243142 c4) ▸ done

  b8 : Chain (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Bx3-0412 ∷ Toff124 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff124 ∷ CCZ024 ∷ Bx3-0412 ∷ []) (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff124 ∷ Bx3-4102 ∷ CCZ024 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff124 ∷ CCZ024 ∷ Bx3-0412 ∷ [])
  b8 = at 6 0 (Toff124 ∷ Toff124 ∷ []) (lw0 c4 [] (Toff124 ∷ Toff124 ∷ []) tt tt Eq.refl) ▸
       at 8 1 (Bx3-4012 ∷ []) (lem-sym12-at0310243142 c4) ▸
       at 8 1 (Bx3-4102 ∷ []) (lem-sym23-at0314203142 c4) ▸
       at 8 1 (Bx3-4120 ∷ []) (lem-sym34-at0314213042 c4) ▸
       at 8 1 (Bx3-4210 ∷ []) (lem-sym23-at0314213240 c4) ▸
       at 7 3 (Bx3-4210 ∷ CCZ024 ∷ []) (lem-T312-beta-at03143140 c4) ▸
       at 7 1 (Bx3-4120 ∷ []) (lem-sym23-at03143140 c4) ▸
       at 7 1 (Bx3-4102 ∷ []) (lem-sym34-at0314213240 c4) ▸ done

  b9 : Chain (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff124 ∷ Bx3-4102 ∷ CCZ024 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff124 ∷ CCZ024 ∷ Bx3-0412 ∷ []) (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff124 ∷ CCZ024 ∷ CCZ014 ∷ Toff214 ∷ Toff214 ∷ Bx3-4120 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff124 ∷ CCZ024 ∷ Bx3-0412 ∷ [])
  b9 = at 7 1 (Bx3-4012 ∷ []) (lem-sym23-at0314213042 c4) ▸
       at 7 1 (Bx3-0412 ∷ []) (lem-sym12-at0314203142 c4) ▸
       at 7 2 (CCZ024 ∷ Bx3-0412 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ241-at0310243142 c4) ▸
       at 8 2 (CCZ014 ∷ Bx3-0412 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ123-at0310243142 c4) ▸
       at 9 0 (Toff214 ∷ Toff214 ∷ []) (lw0 c4 [] (Toff214 ∷ Toff214 ∷ []) tt tt Eq.refl) ▸
       at 11 1 (Bx3-4012 ∷ []) (lem-sym12-at0310243142 c4) ▸
       at 11 1 (Bx3-4102 ∷ []) (lem-sym23-at0314203142 c4) ▸
       at 11 1 (Bx3-4120 ∷ []) (lem-sym34-at0314213042 c4) ▸ done

  b10 : Chain (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff124 ∷ CCZ024 ∷ CCZ014 ∷ Toff214 ∷ Toff214 ∷ Bx3-4120 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff124 ∷ CCZ024 ∷ Bx3-0412 ∷ []) (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff124 ∷ CCZ024 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ Toff214 ∷ Bx3-0412 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff124 ∷ CCZ024 ∷ Bx3-0412 ∷ [])
  b10 = at 10 3 (Bx3-4120 ∷ CCZ014 ∷ []) (lem-T312-beta-at0314213240 c4) ▸
       at 10 1 (Bx3-4102 ∷ []) (lem-sym34-at0314213240 c4) ▸
       at 10 1 (Bx3-4012 ∷ []) (lem-sym23-at0314213042 c4) ▸
       at 10 1 (Bx3-0412 ∷ []) (lem-sym12-at0314203142 c4) ▸
       at 10 2 (CCZ014 ∷ Bx3-0412 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0310243142 c4) ▸
       at 11 2 (CCZ014 ∷ Bx3-0412 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0310243142 c4) ▸
       at 12 2 (CS02 ∷ Bx3-0412 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CS14-at0310243142 c4) ▸
       at 13 0 (Toff214 ∷ Toff214 ∷ []) (lw0 c4 [] (Toff214 ∷ Toff214 ∷ []) tt tt Eq.refl) ▸ done

  b11 : Chain (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff124 ∷ CCZ024 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ Toff214 ∷ Bx3-0412 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff124 ∷ CCZ024 ∷ Bx3-0412 ∷ []) (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff124 ∷ CCZ024 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ CCZ014 ∷ CS02⁻ ∷ Toff124 ∷ CCZ024 ∷ Bx3-0412 ∷ [])
  b11 = at 15 1 (Bx3-4012 ∷ []) (lem-sym12-at0310243142 c4) ▸
       at 15 1 (Bx3-4102 ∷ []) (lem-sym23-at0314203142 c4) ▸
       at 15 1 (Bx3-4120 ∷ []) (lem-sym34-at0314213042 c4) ▸
       at 14 3 (Bx3-4120 ∷ CCZ014 ∷ []) (lem-T312-beta-at0314213240 c4) ▸
       at 14 1 (Bx3-4102 ∷ []) (lem-sym34-at0314213240 c4) ▸
       at 14 1 (Bx3-4012 ∷ []) (lem-sym23-at0314213042 c4) ▸
       at 14 1 (Bx3-0412 ∷ []) (lem-sym12-at0314203142 c4) ▸
       at 14 2 (CCZ014 ∷ Bx3-0412 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0310243142 c4) ▸ done

  b12 : Chain (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff124 ∷ CCZ024 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ CCZ014 ∷ CS02⁻ ∷ Toff124 ∷ CCZ024 ∷ Bx3-0412 ∷ []) (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff124 ∷ CCZ024 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ Toff124 ∷ Bx3-4210 ∷ CCZ024 ∷ CCZ024 ∷ Bx3-0412 ∷ [])
  b12 = at 15 2 (CCZ014 ∷ Bx3-0412 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ231-at0310243142 c4) ▸
       at 16 2 (CS02⁻ ∷ Bx3-0412 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CSd14-at0310243142 c4) ▸
       at 17 0 (Toff124 ∷ Toff124 ∷ []) (lw0 c4 [] (Toff124 ∷ Toff124 ∷ []) tt tt Eq.refl) ▸
       at 19 1 (Bx3-4012 ∷ []) (lem-sym12-at0310243142 c4) ▸
       at 19 1 (Bx3-4102 ∷ []) (lem-sym23-at0314203142 c4) ▸
       at 19 1 (Bx3-4120 ∷ []) (lem-sym34-at0314213042 c4) ▸
       at 19 1 (Bx3-4210 ∷ []) (lem-sym23-at0314213240 c4) ▸
       at 18 3 (Bx3-4210 ∷ CCZ024 ∷ []) (lem-T312-beta-at03143140 c4) ▸ done

  b13 : Chain (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff124 ∷ CCZ024 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ Toff124 ∷ Bx3-4210 ∷ CCZ024 ∷ CCZ024 ∷ Bx3-0412 ∷ []) (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff124 ∷ CCZ024 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Toff124 ∷ CS02⁻ ∷ CCZ024 ∷ CCZ024 ∷ [])
  b13 = at 18 1 (Bx3-4120 ∷ []) (lem-sym23-at03143140 c4) ▸
       at 18 1 (Bx3-4102 ∷ []) (lem-sym34-at0314213240 c4) ▸
       at 18 1 (Bx3-4012 ∷ []) (lem-sym23-at0314213042 c4) ▸
       at 18 1 (Bx3-0412 ∷ []) (lem-sym12-at0314203142 c4) ▸
       at 18 2 (CCZ024 ∷ Bx3-0412 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ241-at0310243142 c4) ▸
       at 19 2 (CCZ024 ∷ Bx3-0412 ∷ []) (lem-auto-BOX⟨0·1234⟩-∣-CCZ241-at0310243142 c4) ▸
       at 20 2 [] (lem-beta-inv-at0310243142 c4) ▸
       at 16 2 (Toff124 ∷ CS02⁻ ∷ []) (pw3 c4 (CS02⁻ ∷ Toff124 ∷ []) (Toff124 ∷ CS02⁻ ∷ []) tt tt Eq.refl) ▸ done

  b14 : Chain (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff124 ∷ CCZ024 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Toff124 ∷ CS02⁻ ∷ CCZ024 ∷ CCZ024 ∷ []) (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ Toff124 ∷ CCZ014 ∷ CCZ024 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ Toff124 ∷ CCZ024 ∷ CCZ024 ∷ CS02⁻ ∷ CCZ024 ∷ CCZ024 ∷ [])
  b14 = at 15 2 (Toff124 ∷ CCZ014 ∷ CCZ024 ∷ []) (pw3 c4 (CCZ014 ∷ Toff124 ∷ []) (Toff124 ∷ CCZ014 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 14 2 (Toff124 ∷ CCZ014 ∷ CCZ024 ∷ []) (pw3 c4 (CCZ014 ∷ Toff124 ∷ []) (Toff124 ∷ CCZ014 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (Toff214 ∷ CCZ014 ∷ []) (pw3 c4 (CCZ014 ∷ Toff214 ∷ []) (Toff214 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff214 ∷ CCZ014 ∷ CCZ024 ∷ []) (pw3 c4 (CCZ024 ∷ Toff214 ∷ []) (Toff214 ∷ CCZ014 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff124 ∷ CS02⁻ ∷ []) (pw3 c4 (CS02⁻ ∷ Toff124 ∷ []) (Toff124 ∷ CS02⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff124 ∷ CCZ014 ∷ CCZ024 ∷ []) (pw3 c4 (CCZ014 ∷ Toff124 ∷ []) (Toff124 ∷ CCZ014 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 18 2 (CCZ014 ∷ CCZ024 ∷ []) (pw3 c4 (CCZ024 ∷ CCZ014 ∷ []) (CCZ014 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 17 2 [] (pw2 c4 (CCZ014 ∷ CCZ014 ∷ []) [] tt tt Eq.refl) ▸ done

  b15 : Chain (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ Toff124 ∷ CCZ014 ∷ CCZ024 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ Toff124 ∷ CCZ024 ∷ CCZ024 ∷ CS02⁻ ∷ CCZ024 ∷ CCZ024 ∷ []) (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ Toff124 ∷ CCZ014 ∷ CCZ024 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ Toff124 ∷ CS02⁻ ∷ [])
  b15 = at 17 2 [] (pw1 c4 (CCZ024 ∷ CCZ024 ∷ []) [] tt tt Eq.refl) ▸
       at 18 2 [] (pw1 c4 (CCZ024 ∷ CCZ024 ∷ []) [] tt tt Eq.refl) ▸ done


-- beta-inv @0310243241: 5 steps
lem-beta-inv-at0310243241 : Complete 4 → ⟪ (Bx3-0421 ∷ Bx3-0421 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-beta-inv-at0310243241 c4 = run b0
  where
  b0 : Chain (Bx3-0421 ∷ Bx3-0421 ∷ []) []
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-0412 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0421⟩ c4) ▸
       at 2 2 (Bx3-0412 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0421⟩ c4) ▸
       at 1 2 [] (lem-beta-inv-at0310243142 c4) ▸
       at 0 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- beta-inv @03243240: 5 steps
lem-beta-inv-at03243240 : Complete 4 → ⟪ (Bx3-1420 ∷ Bx3-1420 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-beta-inv-at03243240 c4 = run b0
  where
  b0 : Chain (Bx3-1420 ∷ Bx3-1420 ∷ []) []
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx3-0421 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1420⟩ c4) ▸
       at 2 2 (Bx3-0421 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1420⟩ c4) ▸
       at 1 2 [] (lem-beta-inv-at0310243241 c4) ▸
       at 0 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done

