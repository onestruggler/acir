{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.R014 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (WsL ; wl0001 ; wl0002 ; wl0006 ; wl0007 ; wl0008 ; wl0009 ; wl0011 ; wl0012 ; wl0014 ; wl0015 ; wl0016 ; wl0017 ; wl0018 ; wl0020 ; wl0021 ; wl0026 ; wl0029 ; wl0033 ; wl0034 ; wl0037 ; wl0044 ; wl0045 ; wl0047 ; wl0053 ; wl0063 ; wl0064 ; wl0065 ; wl0078 ; wl0079 ; wl0084 ; wl0086 ; wl0088 ; wl0089 ; wl0092 ; wl0093 ; wl0095 ; wl0096 ; wl0098 ; wl0107 ; wl0109 ; wl0111 ; wl0112 ; wl0122 ; wl0124 ; wl0125 ; wl0126 ; wl0127 ; wl0128 ; wl0129 ; wl0132 ; wl0133 ; wl0136 ; wl0141 ; wl0142 ; wl0146 ; wl0154 ; wl0155 ; wl0156)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-nat-1-CCZ023 ; lem-nat-1-CCZ024 ; lem-nat-1-CCZ034 ; lem-nat-1-TOFF014 ; lem-nat-1-TOFF024 ; lem-nat-2-CCZ012 ; lem-nat-2-CCZ013 ; lem-nat-2-CCZ024 ; lem-nat-2-CCZ034 ; lem-nat-2-TOFF012 ; lem-nat-2-TOFF013 ; lem-nat-2-TOFF103 ; lem-nat-2-TOFF301 ; lem-nat-3-CCZ014 ; lem-nat-3-CCZ024 ; lem-nat-3-TOFF013 ; lem-nat-3-TOFF104)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-0-CCZ024 ; lem-nat-0-CCZ124 ; lem-nat-1-CCZ013 ; lem-nat-1-CCZ014 ; lem-nat-1-TOFF302 ; lem-nat-2-BOX⟨0·34⟩ ; lem-nat-2-CCZ124 ; lem-nat-2-CCZ134 ; lem-nat-2-TOFF204 ; lem-nat-2-TOFF304 ; lem-nat-3-CCZ013 ; lem-nat-3-CCZ023 ; lem-nat-3-CZ14 ; lem-nat-3-TOFF203 ; lem-nat-3-TOFF402)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-0-BOX⟨3·4102⟩ ; lem-nat-0-CCZ014 ; lem-nat-0-CCZ034 ; lem-nat-0-CCZ134 ; lem-nat-0-TOFF014 ; lem-nat-0-TOFF304 ; lem-nat-0-TOFF314 ; lem-nat-0-TOFF403 ; lem-nat-1-TOFF104 ; lem-nat-2-TOFF413 ; lem-nat-3-CZ23)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-0-BOX⟨3·4012⟩ ; lem-nat-0-TOFF402 ; lem-nat-0-TOFF413 ; lem-nat-1-BOX⟨3·41⟩ ; lem-nat-1-BOX⟨3·42⟩ ; lem-nat-1-TOFF013 ; lem-nat-1-TOFF304 ; lem-nat-2-BOX⟨0·2314⟩ ; lem-nat-2-BOX⟨2·41⟩ ; lem-nat-2-TOFF412 ; lem-nat-3-TOFF023 ; lem-nat-3-TOFF301 ; lem-nat-3-TOFF302)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-0-TOFF024 ; lem-nat-0-TOFF401 ; lem-nat-1-TOFF023 ; lem-nat-1-TOFF401 ; lem-nat-2-CCZ014 ; lem-nat-2-CZ02 ; lem-nat-2-TOFF214 ; lem-nat-2-TOFF402 ; lem-nat-3-CCZ123 ; lem-nat-3-TOFF103)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-0-BOX⟨0·1324⟩ ; lem-nat-0-BOX⟨0·23⟩ ; lem-nat-0-BOX⟨1·23⟩ ; lem-nat-1-BOX⟨1·24⟩ ; lem-nat-2-TOFF314 ; lem-nat-3-BOX⟨0·24⟩ ; lem-nat-3-CS14 ; lem-nat-3-CSd14)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-0-CS14 ; lem-nat-2-TOFF014 ; lem-nat-2-TOFF403 ; lem-nat-3-CS23 ; lem-nat-3-CS24)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-nat-0-BOX⟨4·01⟩ ; lem-nat-0-CSd14 ; lem-nat-1-TOFF403 ; lem-nat-2-BOX⟨1·04⟩ ; lem-nat-3-BOX⟨3·04⟩ ; lem-nat-3-TOFF024 ; lem-nat-3-TOFF401)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-0-BOX⟨4·10⟩ ; lem-nat-1-BOX⟨4·01⟩ ; lem-nat-1-TOFF402 ; lem-nat-2-BOX⟨4·02⟩ ; lem-nat-2-BOX⟨4·03⟩)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-nat-0-TOFF124 ; lem-nat-3-TOFF123)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-nat-1-BOX⟨3·01⟩ ; lem-nat-2-BOX⟨2·01⟩)
open import Examples.Groups.Clifford+CS.Five.D.R012 using (lem-nat-1-BOX⟨0·3214⟩ ; lem-nat-3-BOX⟨1·03⟩ ; lem-nat-3-BOX⟨1·04⟩ ; lem-nat-3-CSd24 ; lem-nat-3-SBOX⟨1·4·2·0⟩ ; lem-nat-3-SBOXd⟨1·4·2·0⟩)
open import Examples.Groups.Clifford+CS.Five.D.R013 using (lem-nat-3-BOXd⟨1·42⟩ ; lem-nat-3-CSd23)
-- nat 3 BOXd(4;102): 8 steps
lem-nat-3-BOXd⟨4·102⟩ : WsL → ⟪ (Sw34 ∷ Bx⁻4-102 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻3-102 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨4·102⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx⁻4-102 ∷ []) (Bx⁻3-102 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx⁻1-42 ∷ CCZ014 ∷ Toff401 ∷ Bx⁻1-42 ∷ Toff401 ∷ CCZ014 ∷ []) (refl) ▸
       at 0 2 (Bx⁻1-32 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨1·42⟩ c4) ▸
       at 1 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4) ▸
       at 2 2 (Toff301 ∷ Sw34 ∷ []) (lem-nat-3-TOFF401 c4) ▸
       at 3 2 (Bx⁻1-32 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨1·42⟩ c4) ▸
       at 4 2 (Toff301 ∷ Sw34 ∷ []) (lem-nat-3-TOFF401 c4) ▸
       at 5 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4) ▸
       at 0 6 (Bx⁻3-102 ∷ []) (refl) ▸ done


-- nat 3 BOXd(1;4302): 8 steps
lem-nat-3-BOXd⟨1·4302⟩ : WsL → ⟪ (Sw34 ∷ Bx⁻1-4302 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-3402 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨1·4302⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx⁻1-4302 ∷ []) (Bx⁻1-3402 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx⁻4-102 ∷ CCZ134 ∷ Toff134 ∷ Bx⁻4-102 ∷ Toff134 ∷ CCZ134 ∷ []) (refl) ▸
       at 0 2 (Bx⁻3-102 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨4·102⟩ c4) ▸
       at 1 2 (CCZ134 ∷ Sw34 ∷ []) (sym (wl0154 c4)) ▸
       at 2 2 (Toff134 ∷ Sw34 ∷ []) (wl0129 c4) ▸
       at 3 2 (Bx⁻3-102 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨4·102⟩ c4) ▸
       at 4 2 (Toff134 ∷ Sw34 ∷ []) (wl0129 c4) ▸
       at 5 2 (CCZ134 ∷ Sw34 ∷ []) (sym (wl0154 c4)) ▸
       at 0 6 (Bx⁻1-3402 ∷ []) (refl) ▸ done


-- nat 3 SBOXd(1;4;30;2): 7 steps
lem-nat-3-SBOXd⟨1·4·30·2⟩ : WsL → ⟪ (Sw34 ∷ Sb⁻1-4-30-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-3-40-2 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨1·4·30·2⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb⁻1-4-30-2 ∷ []) (Sb⁻1-3-40-2 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sb1-4-2-0 ∷ Toff203 ∷ Sb⁻1-4-2-0 ∷ Toff203 ∷ Bx⁻1-4302 ∷ []) (refl) ▸
       at 0 2 (Sb1-3-2-0 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨1·4·2·0⟩ c4) ▸
       at 1 2 (Toff204 ∷ Sw34 ∷ []) (lem-nat-3-TOFF203 c4) ▸
       at 2 2 (Sb⁻1-3-2-0 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨1·4·2·0⟩ c4) ▸
       at 3 2 (Toff204 ∷ Sw34 ∷ []) (lem-nat-3-TOFF203 c4) ▸
       at 4 2 (Bx⁻1-3402 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨1·4302⟩ c4) ▸
       at 0 5 (Sb⁻1-3-40-2 ∷ []) (refl) ▸ done


-- nat 2 BOXd(3;02): 3 steps
lem-nat-2-BOXd⟨3·02⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻3-02 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-03 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨3·02⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻3-02 ∷ []) (Bx⁻2-03 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ02 ∷ []) (refl) ▸
       at 0 2 (CZ03 ∷ Sw23 ∷ []) (lem-nat-2-CZ02 c4) ▸
       at 0 1 (Bx⁻2-03 ∷ []) (refl) ▸ done


-- nat 2 BOXd(0;312): 8 steps
lem-nat-2-BOXd⟨0·312⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻0-312 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-213 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨0·312⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻0-312 ∷ []) (Bx⁻0-213 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx⁻3-02 ∷ CCZ013 ∷ Toff013 ∷ Bx⁻3-02 ∷ Toff013 ∷ CCZ013 ∷ []) (refl) ▸
       at 0 2 (Bx⁻2-03 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨3·02⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 2 2 (Toff012 ∷ Sw23 ∷ []) (lem-nat-2-TOFF013 c4) ▸
       at 3 2 (Bx⁻2-03 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨3·02⟩ c4) ▸
       at 4 2 (Toff012 ∷ Sw23 ∷ []) (lem-nat-2-TOFF013 c4) ▸
       at 5 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 0 6 (Bx⁻0-213 ∷ []) (refl) ▸ done


-- nat 2 BOXd(3;0412): 8 steps
lem-nat-2-BOXd⟨3·0412⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-0413 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨3·0412⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻3-0412 ∷ []) (Bx⁻2-0413 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx⁻0-312 ∷ CCZ034 ∷ Toff304 ∷ Bx⁻0-312 ∷ Toff304 ∷ CCZ034 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-213 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·312⟩ c4) ▸
       at 1 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 2 2 (Toff204 ∷ Sw23 ∷ []) (lem-nat-2-TOFF304 c4) ▸
       at 3 2 (Bx⁻0-213 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·312⟩ c4) ▸
       at 4 2 (Toff204 ∷ Sw23 ∷ []) (lem-nat-2-TOFF304 c4) ▸
       at 5 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 0 6 (Bx⁻2-0413 ∷ []) (refl) ▸ done


-- nat 2 BOX(0;231): 8 steps
lem-nat-2-BOX⟨0·231⟩ : WsL → ⟪ (Sw23 ∷ Bx0-231 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-321 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·231⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-231 ∷ []) (Bx0-321 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff023 ∷ Bx2-01 ∷ Toff023 ∷ CCZ023 ∷ Bx2-01 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw23 ∷ []) (sym (wl0065 c4)) ▸
       at 1 2 (Toff023 ∷ Sw23 ∷ []) (wl0093 c4) ▸
       at 2 2 (Bx3-01 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·01⟩ c4) ▸
       at 3 2 (Toff023 ∷ Sw23 ∷ []) (wl0093 c4) ▸
       at 4 2 (CCZ023 ∷ Sw23 ∷ []) (sym (wl0065 c4)) ▸
       at 5 2 (Bx3-01 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·01⟩ c4) ▸
       at 0 6 (Bx0-321 ∷ []) (refl) ▸ done


-- nat 2 BOX(2;0431): 8 steps
lem-nat-2-BOX⟨2·0431⟩ : WsL → ⟪ (Sw23 ∷ Bx2-0431 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0421 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·0431⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx2-0431 ∷ []) (Bx3-0421 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff204 ∷ Bx0-231 ∷ Toff204 ∷ CCZ024 ∷ Bx0-231 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 1 2 (Toff304 ∷ Sw23 ∷ []) (lem-nat-2-TOFF204 c4) ▸
       at 2 2 (Bx0-321 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·231⟩ c4) ▸
       at 3 2 (Toff304 ∷ Sw23 ∷ []) (lem-nat-2-TOFF204 c4) ▸
       at 4 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 5 2 (Bx0-321 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·231⟩ c4) ▸
       at 0 6 (Bx3-0421 ∷ []) (refl) ▸ done


-- nat 1 BOX(0;321): 8 steps
lem-nat-1-BOX⟨0·321⟩ : WsL → ⟪ (Sw12 ∷ Bx0-321 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-312 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·321⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-321 ∷ []) (Bx0-312 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff023 ∷ Bx3-01 ∷ Toff023 ∷ CCZ023 ∷ Bx3-01 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 1 2 (Toff013 ∷ Sw12 ∷ []) (lem-nat-1-TOFF023 c4) ▸
       at 2 2 (Bx3-02 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·01⟩ c4) ▸
       at 3 2 (Toff013 ∷ Sw12 ∷ []) (lem-nat-1-TOFF023 c4) ▸
       at 4 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 5 2 (Bx3-02 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·01⟩ c4) ▸
       at 0 6 (Bx0-312 ∷ []) (refl) ▸ done


-- nat 1 BOX(3;0421): 8 steps
lem-nat-1-BOX⟨3·0421⟩ : WsL → ⟪ (Sw12 ∷ Bx3-0421 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·0421⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-0421 ∷ []) (Bx3-0412 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff304 ∷ Bx0-321 ∷ Toff304 ∷ CCZ034 ∷ Bx0-321 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 1 2 (Toff304 ∷ Sw12 ∷ []) (lem-nat-1-TOFF304 c4) ▸
       at 2 2 (Bx0-312 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·321⟩ c4) ▸
       at 3 2 (Toff304 ∷ Sw12 ∷ []) (lem-nat-1-TOFF304 c4) ▸
       at 4 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 5 2 (Bx0-312 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·321⟩ c4) ▸
       at 0 6 (Bx3-0412 ∷ []) (refl) ▸ done


-- resp CX41 at 3: 6 steps
lem-resp-CX41-at-3 : WsL → ⟪ (CX41 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ CX42 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-CX41-at-3 c4 = run b0
  where
  b0 : Chain (CX41 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ CX42 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 0 2 (Sw23 ∷ CX41 ∷ []) (wl0156 c4) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 1 2 (Sw12 ∷ CX42 ∷ []) (wl0125 c4) ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 c4)) ▸
       at 2 2 (Sw01 ∷ CX42 ∷ []) (sym (c₂ (Swap) (Swap ↑ • CX₁₀ • Swap ↑))) ▸ done


-- resp CX30 at 2: 4 steps
lem-resp-CX30-at-2 : WsL → ⟪ (CX30 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CX31 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CX30-at-2 c4 = run b0
  where
  b0 : Chain (CX30 ∷ []) (Sw12 ∷ Sw01 ∷ CX31 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 0 2 (Sw12 ∷ CX30 ∷ []) (wl0124 c4) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 c4)) ▸
       at 1 2 (Sw01 ∷ CX31 ∷ []) (wl0122 c4) ▸ done


-- resp CX03 at 1: 2 steps
lem-resp-CX03-at-1 : WsL → ⟪ (CX03 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CX13 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CX03-at-1 c4 = run b0
  where
  b0 : Chain (CX03 ∷ []) (Sw01 ∷ CX13 ∷ Sw01 ∷ [])
  b0 = at 1 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 c4)) ▸
       at 0 2 (Sw01 ∷ CX13 ∷ []) (wl0020 c4) ▸ done


-- resp CX03 at 2: 4 steps
lem-resp-CX03-at-2 : WsL → ⟪ (CX03 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CX13 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CX03-at-2 c4 = run b0
  where
  b0 : Chain (CX03 ∷ []) (Sw12 ∷ Sw01 ∷ CX13 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 0 2 (Sw12 ∷ CX03 ∷ []) (wl0014 c4) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 c4)) ▸
       at 1 2 (Sw01 ∷ CX13 ∷ []) (wl0020 c4) ▸ done


-- nat 1 BOX(4;301): 8 steps
lem-nat-1-BOX⟨4·301⟩ : WsL → ⟪ (Sw12 ∷ Bx4-301 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-302 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·301⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx4-301 ∷ []) (Bx4-302 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff403 ∷ Bx3-41 ∷ Toff403 ∷ CCZ034 ∷ Bx3-41 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 1 2 (Toff403 ∷ Sw12 ∷ []) (lem-nat-1-TOFF403 c4) ▸
       at 2 2 (Bx3-42 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·41⟩ c4) ▸
       at 3 2 (Toff403 ∷ Sw12 ∷ []) (lem-nat-1-TOFF403 c4) ▸
       at 4 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 5 2 (Bx3-42 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·41⟩ c4) ▸
       at 0 6 (Bx4-302 ∷ []) (refl) ▸ done


-- nat 1 BOX(3;4201): 8 steps
lem-nat-1-BOX⟨3·4201⟩ : WsL → ⟪ (Sw12 ∷ Bx3-4201 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4102 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·4201⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-4201 ∷ []) (Bx3-4102 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff324 ∷ Bx4-301 ∷ Toff324 ∷ CCZ234 ∷ Bx4-301 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0034 c4)) ▸
       at 1 2 (Toff314 ∷ Sw12 ∷ []) (wl0063 c4) ▸
       at 2 2 (Bx4-302 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·301⟩ c4) ▸
       at 3 2 (Toff314 ∷ Sw12 ∷ []) (wl0063 c4) ▸
       at 4 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0034 c4)) ▸
       at 5 2 (Bx4-302 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·301⟩ c4) ▸
       at 0 6 (Bx3-4102 ∷ []) (refl) ▸ done


-- nat 1 BOX(4;302): 8 steps
lem-nat-1-BOX⟨4·302⟩ : WsL → ⟪ (Sw12 ∷ Bx4-302 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-301 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·302⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx4-302 ∷ []) (Bx4-301 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff403 ∷ Bx3-42 ∷ Toff403 ∷ CCZ034 ∷ Bx3-42 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 1 2 (Toff403 ∷ Sw12 ∷ []) (lem-nat-1-TOFF403 c4) ▸
       at 2 2 (Bx3-41 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·42⟩ c4) ▸
       at 3 2 (Toff403 ∷ Sw12 ∷ []) (lem-nat-1-TOFF403 c4) ▸
       at 4 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 5 2 (Bx3-41 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·42⟩ c4) ▸
       at 0 6 (Bx4-301 ∷ []) (refl) ▸ done


-- nat 1 BOX(3;4102): 8 steps
lem-nat-1-BOX⟨3·4102⟩ : WsL → ⟪ (Sw12 ∷ Bx3-4102 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4201 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·4102⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-4102 ∷ []) (Bx3-4201 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff314 ∷ Bx4-302 ∷ Toff314 ∷ CCZ134 ∷ Bx4-302 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw12 ∷ []) (sym (wl0084 c4)) ▸
       at 1 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 c4) ▸
       at 2 2 (Bx4-301 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·302⟩ c4) ▸
       at 3 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 c4) ▸
       at 4 2 (CCZ234 ∷ Sw12 ∷ []) (sym (wl0084 c4)) ▸
       at 5 2 (Bx4-301 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·302⟩ c4) ▸
       at 0 6 (Bx3-4201 ∷ []) (refl) ▸ done


-- nat 2 BOX(4;201): 8 steps
lem-nat-2-BOX⟨4·201⟩ : WsL → ⟪ (Sw23 ∷ Bx4-201 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-301 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·201⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx4-201 ∷ []) (Bx4-301 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff402 ∷ Bx2-41 ∷ Toff402 ∷ CCZ024 ∷ Bx2-41 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 1 2 (Toff403 ∷ Sw23 ∷ []) (lem-nat-2-TOFF402 c4) ▸
       at 2 2 (Bx3-41 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·41⟩ c4) ▸
       at 3 2 (Toff403 ∷ Sw23 ∷ []) (lem-nat-2-TOFF402 c4) ▸
       at 4 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 5 2 (Bx3-41 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·41⟩ c4) ▸
       at 0 6 (Bx4-301 ∷ []) (refl) ▸ done


-- nat 2 BOX(2;4301): 8 steps
lem-nat-2-BOX⟨2·4301⟩ : WsL → ⟪ (Sw23 ∷ Bx2-4301 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4201 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·4301⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx2-4301 ∷ []) (Bx3-4201 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff234 ∷ Bx4-201 ∷ Toff234 ∷ CCZ234 ∷ Bx4-201 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw23 ∷ []) (sym (wl0086 c4)) ▸
       at 1 2 (Toff324 ∷ Sw23 ∷ []) (wl0127 c4) ▸
       at 2 2 (Bx4-301 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·201⟩ c4) ▸
       at 3 2 (Toff324 ∷ Sw23 ∷ []) (wl0127 c4) ▸
       at 4 2 (CCZ234 ∷ Sw23 ∷ []) (sym (wl0086 c4)) ▸
       at 5 2 (Bx4-301 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·201⟩ c4) ▸
       at 0 6 (Bx3-4201 ∷ []) (refl) ▸ done


-- nat 3 BOX(2;41): 3 steps
lem-nat-3-BOX⟨2·41⟩ : WsL → ⟪ (Sw34 ∷ Bx2-41 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-31 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨2·41⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx2-41 ∷ []) (Bx2-31 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CZ14 ∷ []) (refl) ▸
       at 0 2 (CZ13 ∷ Sw34 ∷ []) (lem-nat-3-CZ14 c4) ▸
       at 0 1 (Bx2-31 ∷ []) (refl) ▸ done


-- nat 3 BOX(4;201): 8 steps
lem-nat-3-BOX⟨4·201⟩ : WsL → ⟪ (Sw34 ∷ Bx4-201 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-201 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨4·201⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx4-201 ∷ []) (Bx3-201 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff402 ∷ Bx2-41 ∷ Toff402 ∷ CCZ024 ∷ Bx2-41 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 c4) ▸
       at 1 2 (Toff302 ∷ Sw34 ∷ []) (lem-nat-3-TOFF402 c4) ▸
       at 2 2 (Bx2-31 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·41⟩ c4) ▸
       at 3 2 (Toff302 ∷ Sw34 ∷ []) (lem-nat-3-TOFF402 c4) ▸
       at 4 2 (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 c4) ▸
       at 5 2 (Bx2-31 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·41⟩ c4) ▸
       at 0 6 (Bx3-201 ∷ []) (refl) ▸ done


-- nat 3 BOX(2;4301): 8 steps
lem-nat-3-BOX⟨2·4301⟩ : WsL → ⟪ (Sw34 ∷ Bx2-4301 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3401 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨2·4301⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx2-4301 ∷ []) (Bx2-3401 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff234 ∷ Bx4-201 ∷ Toff234 ∷ CCZ234 ∷ Bx4-201 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw34 ∷ []) (sym (wl0155 c4)) ▸
       at 1 2 (Toff234 ∷ Sw34 ∷ []) (wl0128 c4) ▸
       at 2 2 (Bx3-201 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·201⟩ c4) ▸
       at 3 2 (Toff234 ∷ Sw34 ∷ []) (wl0128 c4) ▸
       at 4 2 (CCZ234 ∷ Sw34 ∷ []) (sym (wl0155 c4)) ▸
       at 5 2 (Bx3-201 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·201⟩ c4) ▸
       at 0 6 (Bx2-3401 ∷ []) (refl) ▸ done


-- nat 0 SBOX(3;4;2;0): 2 steps
lem-nat-0-SBOX⟨3·4·2·0⟩ : WsL → ⟪ (Sw01 ∷ Sb3-4-2-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-4-2-1 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨3·4·2·0⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb3-4-2-0 ∷ []) (Sb3-4-2-1 ∷ Sw01 ∷ [])
  b0 = at 0 2 (Sb3-4-2-0 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑)) ▸
       at 0 1 (Sb3-4-2-1 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 SBOXd(3;4;2;0): 2 steps
lem-nat-0-SBOXd⟨3·4·2·0⟩ : WsL → ⟪ (Sw01 ∷ Sb⁻3-4-2-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻3-4-2-1 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨3·4·2·0⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻3-4-2-0 ∷ []) (Sb⁻3-4-2-1 ∷ Sw01 ∷ [])
  b0 = at 0 2 (Sb⁻3-4-2-0 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • (CS • CS • CS) • Swap ↑)) ▸
       at 0 1 (Sb⁻3-4-2-1 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 SBOX(3;4;10;2): 7 steps
lem-nat-0-SBOX⟨3·4·10·2⟩ : WsL → ⟪ (Sw01 ∷ Sb3-4-10-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-4-01-2 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨3·4·10·2⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb3-4-10-2 ∷ []) (Sb3-4-01-2 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx3-4102 ∷ Toff201 ∷ Sb3-4-2-0 ∷ Toff201 ∷ Sb⁻3-4-2-0 ∷ []) (refl) ▸
       at 0 2 (Bx3-4012 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·4102⟩ c4) ▸
       at 1 2 (Toff201 ∷ Sw01 ∷ []) (wl0107 c4) ▸
       at 2 2 (Sb3-4-2-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·4·2·0⟩ c4) ▸
       at 3 2 (Toff201 ∷ Sw01 ∷ []) (wl0107 c4) ▸
       at 4 2 (Sb⁻3-4-2-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨3·4·2·0⟩ c4) ▸
       at 0 5 (Sb3-4-01-2 ∷ []) (refl) ▸ done


-- nat 0 SBOX(3;4;2;1): 2 steps
lem-nat-0-SBOX⟨3·4·2·1⟩ : WsL → ⟪ (Sw01 ∷ Sb3-4-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-4-2-0 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨3·4·2·1⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb3-4-2-1 ∷ []) (Sb3-4-2-0 ∷ Sw01 ∷ [])
  b0 = at 0 2 (Sb3-4-2-1 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑)) ▸
       at 0 1 (Sb3-4-2-0 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 SBOXd(3;4;2;1): 2 steps
lem-nat-0-SBOXd⟨3·4·2·1⟩ : WsL → ⟪ (Sw01 ∷ Sb⁻3-4-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻3-4-2-0 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨3·4·2·1⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻3-4-2-1 ∷ []) (Sb⁻3-4-2-0 ∷ Sw01 ∷ [])
  b0 = at 0 2 (Sb⁻3-4-2-1 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • (CS • CS • CS) • Swap ↑)) ▸
       at 0 1 (Sb⁻3-4-2-0 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 SBOX(3;4;01;2): 7 steps
lem-nat-0-SBOX⟨3·4·01·2⟩ : WsL → ⟪ (Sw01 ∷ Sb3-4-01-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-4-10-2 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨3·4·01·2⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb3-4-01-2 ∷ []) (Sb3-4-10-2 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx3-4012 ∷ Toff201 ∷ Sb3-4-2-1 ∷ Toff201 ∷ Sb⁻3-4-2-1 ∷ []) (refl) ▸
       at 0 2 (Bx3-4102 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·4012⟩ c4) ▸
       at 1 2 (Toff201 ∷ Sw01 ∷ []) (wl0107 c4) ▸
       at 2 2 (Sb3-4-2-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·4·2·1⟩ c4) ▸
       at 3 2 (Toff201 ∷ Sw01 ∷ []) (wl0107 c4) ▸
       at 4 2 (Sb⁻3-4-2-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨3·4·2·1⟩ c4) ▸
       at 0 5 (Sb3-4-10-2 ∷ []) (refl) ▸ done


-- nat 1 SBOX(3;4;1;0): 3 steps
lem-nat-1-SBOX⟨3·4·1·0⟩ : WsL → ⟪ (Sw12 ∷ Sb3-4-1-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-4-2-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨3·4·1·0⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb3-4-1-0 ∷ []) (Sb3-4-2-0 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS14 ∷ []) (refl) ▸
       at 0 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0008 c4)) ▸
       at 0 1 (Sb3-4-2-0 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(3;4;1;0): 3 steps
lem-nat-1-SBOXd⟨3·4·1·0⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻3-4-1-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻3-4-2-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨3·4·1·0⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻3-4-1-0 ∷ []) (Sb⁻3-4-2-0 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS14⁻ ∷ []) (refl) ▸
       at 0 2 (CS24⁻ ∷ Sw12 ∷ []) (sym (wl0009 c4)) ▸
       at 0 1 (Sb⁻3-4-2-0 ∷ []) (refl) ▸ done


-- nat 1 SBOX(3;4;20;1): 7 steps
lem-nat-1-SBOX⟨3·4·20·1⟩ : WsL → ⟪ (Sw12 ∷ Sb3-4-20-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-4-10-2 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨3·4·20·1⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb3-4-20-1 ∷ []) (Sb3-4-10-2 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx3-4201 ∷ Toff102 ∷ Sb3-4-1-0 ∷ Toff102 ∷ Sb⁻3-4-1-0 ∷ []) (refl) ▸
       at 0 2 (Bx3-4102 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·4201⟩ c4) ▸
       at 1 2 (Toff201 ∷ Sw12 ∷ []) (wl0047 c4) ▸
       at 2 2 (Sb3-4-2-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·4·1·0⟩ c4) ▸
       at 3 2 (Toff201 ∷ Sw12 ∷ []) (wl0047 c4) ▸
       at 4 2 (Sb⁻3-4-2-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨3·4·1·0⟩ c4) ▸
       at 0 5 (Sb3-4-10-2 ∷ []) (refl) ▸ done


-- nat 1 SBOX(3;4;2;0): 3 steps
lem-nat-1-SBOX⟨3·4·2·0⟩ : WsL → ⟪ (Sw12 ∷ Sb3-4-2-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-4-1-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨3·4·2·0⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb3-4-2-0 ∷ []) (Sb3-4-1-0 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS24 ∷ []) (refl) ▸
       at 0 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0017 c4)) ▸
       at 0 1 (Sb3-4-1-0 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(3;4;2;0): 3 steps
lem-nat-1-SBOXd⟨3·4·2·0⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻3-4-2-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻3-4-1-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨3·4·2·0⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻3-4-2-0 ∷ []) (Sb⁻3-4-1-0 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS24⁻ ∷ []) (refl) ▸
       at 0 2 (CS14⁻ ∷ Sw12 ∷ []) (sym (wl0018 c4)) ▸
       at 0 1 (Sb⁻3-4-1-0 ∷ []) (refl) ▸ done


-- nat 1 SBOX(3;4;10;2): 7 steps
lem-nat-1-SBOX⟨3·4·10·2⟩ : WsL → ⟪ (Sw12 ∷ Sb3-4-10-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-4-20-1 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨3·4·10·2⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb3-4-10-2 ∷ []) (Sb3-4-20-1 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx3-4102 ∷ Toff201 ∷ Sb3-4-2-0 ∷ Toff201 ∷ Sb⁻3-4-2-0 ∷ []) (refl) ▸
       at 0 2 (Bx3-4201 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·4102⟩ c4) ▸
       at 1 2 (Toff102 ∷ Sw12 ∷ []) (wl0044 c4) ▸
       at 2 2 (Sb3-4-1-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·4·2·0⟩ c4) ▸
       at 3 2 (Toff102 ∷ Sw12 ∷ []) (wl0044 c4) ▸
       at 4 2 (Sb⁻3-4-1-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨3·4·2·0⟩ c4) ▸
       at 0 5 (Sb3-4-20-1 ∷ []) (refl) ▸ done


-- nat 2 SBOX(2;4;1;0): 3 steps
lem-nat-2-SBOX⟨2·4·1·0⟩ : WsL → ⟪ (Sw23 ∷ Sb2-4-1-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-4-1-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨2·4·1·0⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb2-4-1-0 ∷ []) (Sb3-4-1-0 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS14 ∷ []) (refl) ▸
       at 0 2 (CS14 ∷ Sw23 ∷ []) (sym (wl0021 c4)) ▸
       at 0 1 (Sb3-4-1-0 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(2;4;1;0): 3 steps
lem-nat-2-SBOXd⟨2·4·1·0⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻2-4-1-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻3-4-1-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨2·4·1·0⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻2-4-1-0 ∷ []) (Sb⁻3-4-1-0 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS14⁻ ∷ []) (refl) ▸
       at 0 2 (CS14⁻ ∷ Sw23 ∷ []) (sym (wl0033 c4)) ▸
       at 0 1 (Sb⁻3-4-1-0 ∷ []) (refl) ▸ done


-- nat 2 SBOX(2;4;30;1): 7 steps
lem-nat-2-SBOX⟨2·4·30·1⟩ : WsL → ⟪ (Sw23 ∷ Sb2-4-30-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-4-20-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨2·4·30·1⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb2-4-30-1 ∷ []) (Sb3-4-20-1 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx2-4301 ∷ Toff103 ∷ Sb2-4-1-0 ∷ Toff103 ∷ Sb⁻2-4-1-0 ∷ []) (refl) ▸
       at 0 2 (Bx3-4201 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·4301⟩ c4) ▸
       at 1 2 (Toff102 ∷ Sw23 ∷ []) (lem-nat-2-TOFF103 c4) ▸
       at 2 2 (Sb3-4-1-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨2·4·1·0⟩ c4) ▸
       at 3 2 (Toff102 ∷ Sw23 ∷ []) (lem-nat-2-TOFF103 c4) ▸
       at 4 2 (Sb⁻3-4-1-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨2·4·1·0⟩ c4) ▸
       at 0 5 (Sb3-4-20-1 ∷ []) (refl) ▸ done


-- nat 3 SBOX(2;4;1;0): 3 steps
lem-nat-3-SBOX⟨2·4·1·0⟩ : WsL → ⟪ (Sw34 ∷ Sb2-4-1-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-3-1-0 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨2·4·1·0⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb2-4-1-0 ∷ []) (Sb2-3-1-0 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS14 ∷ []) (refl) ▸
       at 0 2 (CS13 ∷ Sw34 ∷ []) (lem-nat-3-CS14 c4) ▸
       at 0 1 (Sb2-3-1-0 ∷ []) (refl) ▸ done


-- nat 3 SBOXd(2;4;1;0): 3 steps
lem-nat-3-SBOXd⟨2·4·1·0⟩ : WsL → ⟪ (Sw34 ∷ Sb⁻2-4-1-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-3-1-0 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨2·4·1·0⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb⁻2-4-1-0 ∷ []) (Sb⁻2-3-1-0 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS14⁻ ∷ []) (refl) ▸
       at 0 2 (CS13⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd14 c4) ▸
       at 0 1 (Sb⁻2-3-1-0 ∷ []) (refl) ▸ done


-- nat 3 SBOX(2;4;30;1): 7 steps
lem-nat-3-SBOX⟨2·4·30·1⟩ : WsL → ⟪ (Sw34 ∷ Sb2-4-30-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-3-40-1 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨2·4·30·1⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb2-4-30-1 ∷ []) (Sb2-3-40-1 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx2-4301 ∷ Toff103 ∷ Sb2-4-1-0 ∷ Toff103 ∷ Sb⁻2-4-1-0 ∷ []) (refl) ▸
       at 0 2 (Bx2-3401 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·4301⟩ c4) ▸
       at 1 2 (Toff104 ∷ Sw34 ∷ []) (lem-nat-3-TOFF103 c4) ▸
       at 2 2 (Sb2-3-1-0 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨2·4·1·0⟩ c4) ▸
       at 3 2 (Toff104 ∷ Sw34 ∷ []) (lem-nat-3-TOFF103 c4) ▸
       at 4 2 (Sb⁻2-3-1-0 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨2·4·1·0⟩ c4) ▸
       at 0 5 (Sb2-3-40-1 ∷ []) (refl) ▸ done


-- nat 2 BOX(0;124): 8 steps
lem-nat-2-BOX⟨0·124⟩ : WsL → ⟪ (Sw23 ∷ Bx0-124 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-134 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·124⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-124 ∷ []) (Bx0-134 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff012 ∷ Bx1-04 ∷ Toff012 ∷ CCZ012 ∷ Bx1-04 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 1 2 (Toff013 ∷ Sw23 ∷ []) (lem-nat-2-TOFF012 c4) ▸
       at 2 2 (Bx1-04 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·04⟩ c4) ▸
       at 3 2 (Toff013 ∷ Sw23 ∷ []) (lem-nat-2-TOFF012 c4) ▸
       at 4 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 5 2 (Bx1-04 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·04⟩ c4) ▸
       at 0 6 (Bx0-134 ∷ []) (refl) ▸ done


-- nat 2 BOX(1;0324): 8 steps
lem-nat-2-BOX⟨1·0324⟩ : WsL → ⟪ (Sw23 ∷ Bx1-0324 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0234 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·0324⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx1-0324 ∷ []) (Bx1-0234 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff103 ∷ Bx0-124 ∷ Toff103 ∷ CCZ013 ∷ Bx0-124 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 1 2 (Toff102 ∷ Sw23 ∷ []) (lem-nat-2-TOFF103 c4) ▸
       at 2 2 (Bx0-134 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·124⟩ c4) ▸
       at 3 2 (Toff102 ∷ Sw23 ∷ []) (lem-nat-2-TOFF103 c4) ▸
       at 4 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 5 2 (Bx0-134 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·124⟩ c4) ▸
       at 0 6 (Bx1-0234 ∷ []) (refl) ▸ done


-- nat 3 BOX(0;123): 8 steps
lem-nat-3-BOX⟨0·123⟩ : WsL → ⟪ (Sw34 ∷ Bx0-123 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-124 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·123⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx0-123 ∷ []) (Bx0-124 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff012 ∷ Bx1-03 ∷ Toff012 ∷ CCZ012 ∷ Bx1-03 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 1 2 (Toff012 ∷ Sw34 ∷ []) (sym (c₃ (Toff) (Swap))) ▸
       at 2 2 (Bx1-04 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·03⟩ c4) ▸
       at 3 2 (Toff012 ∷ Sw34 ∷ []) (sym (c₃ (Toff) (Swap))) ▸
       at 4 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 5 2 (Bx1-04 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·03⟩ c4) ▸
       at 0 6 (Bx0-124 ∷ []) (refl) ▸ done


-- nat 3 BOX(1;0423): 8 steps
lem-nat-3-BOX⟨1·0423⟩ : WsL → ⟪ (Sw34 ∷ Bx1-0423 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0324 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨1·0423⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx1-0423 ∷ []) (Bx1-0324 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff104 ∷ Bx0-123 ∷ Toff104 ∷ CCZ014 ∷ Bx0-123 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4) ▸
       at 1 2 (Toff103 ∷ Sw34 ∷ []) (lem-nat-3-TOFF104 c4) ▸
       at 2 2 (Bx0-124 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·123⟩ c4) ▸
       at 3 2 (Toff103 ∷ Sw34 ∷ []) (lem-nat-3-TOFF104 c4) ▸
       at 4 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4) ▸
       at 5 2 (Bx0-124 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·123⟩ c4) ▸
       at 0 6 (Bx1-0324 ∷ []) (refl) ▸ done


-- nat 3 BOX(0;124): 8 steps
lem-nat-3-BOX⟨0·124⟩ : WsL → ⟪ (Sw34 ∷ Bx0-124 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-123 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·124⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx0-124 ∷ []) (Bx0-123 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff012 ∷ Bx1-04 ∷ Toff012 ∷ CCZ012 ∷ Bx1-04 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 1 2 (Toff012 ∷ Sw34 ∷ []) (sym (c₃ (Toff) (Swap))) ▸
       at 2 2 (Bx1-03 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·04⟩ c4) ▸
       at 3 2 (Toff012 ∷ Sw34 ∷ []) (sym (c₃ (Toff) (Swap))) ▸
       at 4 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 5 2 (Bx1-03 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·04⟩ c4) ▸
       at 0 6 (Bx0-123 ∷ []) (refl) ▸ done


-- nat 3 BOX(1;0324): 8 steps
lem-nat-3-BOX⟨1·0324⟩ : WsL → ⟪ (Sw34 ∷ Bx1-0324 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0423 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨1·0324⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx1-0324 ∷ []) (Bx1-0423 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff103 ∷ Bx0-124 ∷ Toff103 ∷ CCZ013 ∷ Bx0-124 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4) ▸
       at 1 2 (Toff104 ∷ Sw34 ∷ []) (lem-nat-3-TOFF103 c4) ▸
       at 2 2 (Bx0-123 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·124⟩ c4) ▸
       at 3 2 (Toff104 ∷ Sw34 ∷ []) (lem-nat-3-TOFF103 c4) ▸
       at 4 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4) ▸
       at 5 2 (Bx0-123 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·124⟩ c4) ▸
       at 0 6 (Bx1-0423 ∷ []) (refl) ▸ done


-- comm CCZ134 CX20: 23 steps
lem-comm-CCZ134-CX20 : WsL → ⟪ (CCZ134 ∷ CX20 ∷ []) ⟫ʷ ≈ ⟪ (CX20 ∷ CCZ134 ∷ []) ⟫ʷ
lem-comm-CCZ134-CX20 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CCZ134 ∷ CX20 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ CCZ124 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b0 = at 0 1 (Sw23 ∷ Sw34 ∷ CCZ123 ∷ Sw34 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 4 3 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 5 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 3 3 (CX40 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 3 3 (CCZ124 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ CCZ124 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ CCZ123 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b1 = at 3 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 4 3 (CCZ134 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw12 ∷ CCZ234 ∷ []) (wl0034 c4) ▸
       at 5 2 (CX10 ∷ CCZ234 ∷ []) (sym (c₂ (CX₁₀) (CCZ))) ▸
       at 6 2 (Sw12 ∷ CCZ134 ∷ []) (wl0084 c4) ▸
       at 7 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (wl0006 c4) ▸
       at 8 1 (Sw34 ∷ CCZ123 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ CCZ123 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (CX20 ∷ CCZ134 ∷ [])
  b2 = at 10 2 [] (wl0007 c4) ▸
       at 2 7 (CX40 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ CX30 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (wl0007 c4) ▸
       at 1 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0006 c4) ▸
       at 1 5 (CCZ134 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CSd04 CCZ123: 13 steps
lem-comm-CSd04-CCZ123 : WsL → ⟪ (CS04⁻ ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CS04⁻ ∷ []) ⟫ʷ
lem-comm-CSd04-CCZ123 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CS04⁻ ∷ CCZ123 ∷ []) (Sw34 ∷ Sw23 ∷ CCZ134 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 0 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 6 3 (CCZ124 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 5 3 (CCZ134 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CCZ234 ∷ Sw12 ∷ []) (sym (wl0084 c4)) ▸
       at 3 2 (CCZ234 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (CCZ)) ▸
       at 2 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0034 c4)) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ CCZ134 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (CCZ123 ∷ CS04⁻ ∷ [])
  b1 = at 2 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (wl0006 c4) ▸
       at 1 1 (Sw34 ∷ CCZ123 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0007 c4) ▸
       at 1 7 (CS04⁻ ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 1 SBOX(0;3;4;1): 2 steps
lem-nat-1-SBOX⟨0·3·4·1⟩ : WsL → ⟪ (Sw12 ∷ Sb0-3-4-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-3-4-2 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨0·3·4·1⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb0-3-4-1 ∷ []) (Sb0-3-4-2 ∷ Sw12 ∷ [])
  b0 = at 0 2 (Sb0-3-4-1 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS)) ▸
       at 0 1 (Sb0-3-4-2 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 1 SBOXd(0;3;4;1): 2 steps
lem-nat-1-SBOXd⟨0·3·4·1⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻0-3-4-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-3-4-2 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨0·3·4·1⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻0-3-4-1 ∷ []) (Sb⁻0-3-4-2 ∷ Sw12 ∷ [])
  b0 = at 0 2 (Sb⁻0-3-4-1 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS • CS • CS)) ▸
       at 0 1 (Sb⁻0-3-4-2 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 1 SBOX(0;3;21;4): 7 steps
lem-nat-1-SBOX⟨0·3·21·4⟩ : WsL → ⟪ (Sw12 ∷ Sb0-3-21-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-3-12-4 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨0·3·21·4⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb0-3-21-4 ∷ []) (Sb0-3-12-4 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx0-3214 ∷ Toff412 ∷ Sb0-3-4-1 ∷ Toff412 ∷ Sb⁻0-3-4-1 ∷ []) (refl) ▸
       at 0 2 (Bx0-3124 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·3214⟩ c4) ▸
       at 1 2 (Toff412 ∷ Sw12 ∷ []) (wl0079 c4) ▸
       at 2 2 (Sb0-3-4-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·3·4·1⟩ c4) ▸
       at 3 2 (Toff412 ∷ Sw12 ∷ []) (wl0079 c4) ▸
       at 4 2 (Sb⁻0-3-4-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨0·3·4·1⟩ c4) ▸
       at 0 5 (Sb0-3-12-4 ∷ []) (refl) ▸ done


-- nat 1 BOX(3;024): 8 steps
lem-nat-1-BOX⟨3·024⟩ : WsL → ⟪ (Sw12 ∷ Bx3-024 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-014 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·024⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-024 ∷ []) (Bx3-014 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff302 ∷ Bx0-34 ∷ Toff302 ∷ CCZ023 ∷ Bx0-34 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 1 2 (Toff301 ∷ Sw12 ∷ []) (lem-nat-1-TOFF302 c4) ▸
       at 2 2 (Bx0-34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CZ)) ▸
       at 3 2 (Toff301 ∷ Sw12 ∷ []) (lem-nat-1-TOFF302 c4) ▸
       at 4 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 5 2 (Bx0-34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CZ)) ▸
       at 0 6 (Bx3-014 ∷ []) (refl) ▸ done


-- nat 1 BOX(0;3124): 8 steps
lem-nat-1-BOX⟨0·3124⟩ : WsL → ⟪ (Sw12 ∷ Bx0-3124 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3214 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·3124⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-3124 ∷ []) (Bx0-3214 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff013 ∷ Bx3-024 ∷ Toff013 ∷ CCZ013 ∷ Bx3-024 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 1 2 (Toff023 ∷ Sw12 ∷ []) (lem-nat-1-TOFF013 c4) ▸
       at 2 2 (Bx3-014 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·024⟩ c4) ▸
       at 3 2 (Toff023 ∷ Sw12 ∷ []) (lem-nat-1-TOFF013 c4) ▸
       at 4 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 5 2 (Bx3-014 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·024⟩ c4) ▸
       at 0 6 (Bx0-3214 ∷ []) (refl) ▸ done


-- nat 1 SBOX(0;3;4;2): 2 steps
lem-nat-1-SBOX⟨0·3·4·2⟩ : WsL → ⟪ (Sw12 ∷ Sb0-3-4-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-3-4-1 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨0·3·4·2⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb0-3-4-2 ∷ []) (Sb0-3-4-1 ∷ Sw12 ∷ [])
  b0 = at 0 2 (Sb0-3-4-2 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS)) ▸
       at 0 1 (Sb0-3-4-1 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 1 SBOXd(0;3;4;2): 2 steps
lem-nat-1-SBOXd⟨0·3·4·2⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻0-3-4-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-3-4-1 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨0·3·4·2⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻0-3-4-2 ∷ []) (Sb⁻0-3-4-1 ∷ Sw12 ∷ [])
  b0 = at 0 2 (Sb⁻0-3-4-2 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS • CS • CS)) ▸
       at 0 1 (Sb⁻0-3-4-1 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 1 SBOX(0;3;12;4): 7 steps
lem-nat-1-SBOX⟨0·3·12·4⟩ : WsL → ⟪ (Sw12 ∷ Sb0-3-12-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-3-21-4 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨0·3·12·4⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb0-3-12-4 ∷ []) (Sb0-3-21-4 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx0-3124 ∷ Toff412 ∷ Sb0-3-4-2 ∷ Toff412 ∷ Sb⁻0-3-4-2 ∷ []) (refl) ▸
       at 0 2 (Bx0-3214 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·3124⟩ c4) ▸
       at 1 2 (Toff412 ∷ Sw12 ∷ []) (wl0079 c4) ▸
       at 2 2 (Sb0-3-4-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·3·4·2⟩ c4) ▸
       at 3 2 (Toff412 ∷ Sw12 ∷ []) (wl0079 c4) ▸
       at 4 2 (Sb⁻0-3-4-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨0·3·4·2⟩ c4) ▸
       at 0 5 (Sb0-3-21-4 ∷ []) (refl) ▸ done


-- nat 2 SBOX(0;2;4;1): 3 steps
lem-nat-2-SBOX⟨0·2·4·1⟩ : WsL → ⟪ (Sw23 ∷ Sb0-2-4-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-3-4-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨0·2·4·1⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb0-2-4-1 ∷ []) (Sb0-3-4-1 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS24 ∷ []) (refl) ▸
       at 0 2 (CS34 ∷ Sw23 ∷ []) (sym (wl0011 c4)) ▸
       at 0 1 (Sb0-3-4-1 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(0;2;4;1): 3 steps
lem-nat-2-SBOXd⟨0·2·4·1⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻0-2-4-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-3-4-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨0·2·4·1⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻0-2-4-1 ∷ []) (Sb⁻0-3-4-1 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS24⁻ ∷ []) (refl) ▸
       at 0 2 (CS34⁻ ∷ Sw23 ∷ []) (sym (wl0012 c4)) ▸
       at 0 1 (Sb⁻0-3-4-1 ∷ []) (refl) ▸ done


-- nat 2 SBOX(0;2;31;4): 7 steps
lem-nat-2-SBOX⟨0·2·31·4⟩ : WsL → ⟪ (Sw23 ∷ Sb0-2-31-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-3-21-4 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨0·2·31·4⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb0-2-31-4 ∷ []) (Sb0-3-21-4 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx0-2314 ∷ Toff413 ∷ Sb0-2-4-1 ∷ Toff413 ∷ Sb⁻0-2-4-1 ∷ []) (refl) ▸
       at 0 2 (Bx0-3214 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·2314⟩ c4) ▸
       at 1 2 (Toff412 ∷ Sw23 ∷ []) (lem-nat-2-TOFF413 c4) ▸
       at 2 2 (Sb0-3-4-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·2·4·1⟩ c4) ▸
       at 3 2 (Toff412 ∷ Sw23 ∷ []) (lem-nat-2-TOFF413 c4) ▸
       at 4 2 (Sb⁻0-3-4-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·2·4·1⟩ c4) ▸
       at 0 5 (Sb0-3-21-4 ∷ []) (refl) ▸ done


-- nat 2 BOX(3;014): 8 steps
lem-nat-2-BOX⟨3·014⟩ : WsL → ⟪ (Sw23 ∷ Bx3-014 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-014 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·014⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx3-014 ∷ []) (Bx2-014 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff301 ∷ Bx0-34 ∷ Toff301 ∷ CCZ013 ∷ Bx0-34 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 1 2 (Toff201 ∷ Sw23 ∷ []) (lem-nat-2-TOFF301 c4) ▸
       at 2 2 (Bx0-24 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·34⟩ c4) ▸
       at 3 2 (Toff201 ∷ Sw23 ∷ []) (lem-nat-2-TOFF301 c4) ▸
       at 4 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 5 2 (Bx0-24 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·34⟩ c4) ▸
       at 0 6 (Bx2-014 ∷ []) (refl) ▸ done


-- nat 2 BOX(0;3214): 8 steps
lem-nat-2-BOX⟨0·3214⟩ : WsL → ⟪ (Sw23 ∷ Bx0-3214 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2314 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·3214⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-3214 ∷ []) (Bx0-2314 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff023 ∷ Bx3-014 ∷ Toff023 ∷ CCZ023 ∷ Bx3-014 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw23 ∷ []) (sym (wl0065 c4)) ▸
       at 1 2 (Toff023 ∷ Sw23 ∷ []) (wl0093 c4) ▸
       at 2 2 (Bx2-014 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·014⟩ c4) ▸
       at 3 2 (Toff023 ∷ Sw23 ∷ []) (wl0093 c4) ▸
       at 4 2 (CCZ023 ∷ Sw23 ∷ []) (sym (wl0065 c4)) ▸
       at 5 2 (Bx2-014 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·014⟩ c4) ▸
       at 0 6 (Bx0-2314 ∷ []) (refl) ▸ done


-- nat 2 SBOX(0;3;4;1): 3 steps
lem-nat-2-SBOX⟨0·3·4·1⟩ : WsL → ⟪ (Sw23 ∷ Sb0-3-4-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-4-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨0·3·4·1⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb0-3-4-1 ∷ []) (Sb0-2-4-1 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS34 ∷ []) (refl) ▸
       at 0 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0015 c4)) ▸
       at 0 1 (Sb0-2-4-1 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(0;3;4;1): 3 steps
lem-nat-2-SBOXd⟨0·3·4·1⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻0-3-4-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-2-4-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨0·3·4·1⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻0-3-4-1 ∷ []) (Sb⁻0-2-4-1 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS34⁻ ∷ []) (refl) ▸
       at 0 2 (CS24⁻ ∷ Sw23 ∷ []) (sym (wl0016 c4)) ▸
       at 0 1 (Sb⁻0-2-4-1 ∷ []) (refl) ▸ done


-- nat 2 SBOX(0;3;21;4): 7 steps
lem-nat-2-SBOX⟨0·3·21·4⟩ : WsL → ⟪ (Sw23 ∷ Sb0-3-21-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-31-4 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨0·3·21·4⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb0-3-21-4 ∷ []) (Sb0-2-31-4 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx0-3214 ∷ Toff412 ∷ Sb0-3-4-1 ∷ Toff412 ∷ Sb⁻0-3-4-1 ∷ []) (refl) ▸
       at 0 2 (Bx0-2314 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3214⟩ c4) ▸
       at 1 2 (Toff413 ∷ Sw23 ∷ []) (lem-nat-2-TOFF412 c4) ▸
       at 2 2 (Sb0-2-4-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·3·4·1⟩ c4) ▸
       at 3 2 (Toff413 ∷ Sw23 ∷ []) (lem-nat-2-TOFF412 c4) ▸
       at 4 2 (Sb⁻0-2-4-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·3·4·1⟩ c4) ▸
       at 0 5 (Sb0-2-31-4 ∷ []) (refl) ▸ done


-- nat 3 BOX(0;23): 3 steps
lem-nat-3-BOX⟨0·23⟩ : WsL → ⟪ (Sw34 ∷ Bx0-23 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-24 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·23⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx0-23 ∷ []) (Bx0-24 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CZ23 ∷ []) (refl) ▸
       at 0 2 (CZ24 ∷ Sw34 ∷ []) (lem-nat-3-CZ23 c4) ▸
       at 0 1 (Bx0-24 ∷ []) (refl) ▸ done


-- nat 3 BOX(2;013): 8 steps
lem-nat-3-BOX⟨2·013⟩ : WsL → ⟪ (Sw34 ∷ Bx2-013 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-014 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨2·013⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx2-013 ∷ []) (Bx2-014 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff201 ∷ Bx0-23 ∷ Toff201 ∷ CCZ012 ∷ Bx0-23 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 1 2 (Toff201 ∷ Sw34 ∷ []) (sym (c₃ (Toffᵗ) (Swap))) ▸
       at 2 2 (Bx0-24 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·23⟩ c4) ▸
       at 3 2 (Toff201 ∷ Sw34 ∷ []) (sym (c₃ (Toffᵗ) (Swap))) ▸
       at 4 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 5 2 (Bx0-24 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·23⟩ c4) ▸
       at 0 6 (Bx2-014 ∷ []) (refl) ▸ done


-- nat 3 BOX(0;2413): 8 steps
lem-nat-3-BOX⟨0·2413⟩ : WsL → ⟪ (Sw34 ∷ Bx0-2413 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2314 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·2413⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx0-2413 ∷ []) (Bx0-2314 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff024 ∷ Bx2-013 ∷ Toff024 ∷ CCZ024 ∷ Bx2-013 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 c4) ▸
       at 1 2 (Toff023 ∷ Sw34 ∷ []) (lem-nat-3-TOFF024 c4) ▸
       at 2 2 (Bx2-014 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·013⟩ c4) ▸
       at 3 2 (Toff023 ∷ Sw34 ∷ []) (lem-nat-3-TOFF024 c4) ▸
       at 4 2 (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 c4) ▸
       at 5 2 (Bx2-014 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·013⟩ c4) ▸
       at 0 6 (Bx0-2314 ∷ []) (refl) ▸ done


-- nat 3 SBOX(0;2;3;1): 3 steps
lem-nat-3-SBOX⟨0·2·3·1⟩ : WsL → ⟪ (Sw34 ∷ Sb0-2-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-4-1 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨0·2·3·1⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb0-2-3-1 ∷ []) (Sb0-2-4-1 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS23 ∷ []) (refl) ▸
       at 0 2 (CS24 ∷ Sw34 ∷ []) (lem-nat-3-CS23 c4) ▸
       at 0 1 (Sb0-2-4-1 ∷ []) (refl) ▸ done


-- nat 3 SBOXd(0;2;3;1): 3 steps
lem-nat-3-SBOXd⟨0·2·3·1⟩ : WsL → ⟪ (Sw34 ∷ Sb⁻0-2-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-2-4-1 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨0·2·3·1⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb⁻0-2-3-1 ∷ []) (Sb⁻0-2-4-1 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS23⁻ ∷ []) (refl) ▸
       at 0 2 (CS24⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd23 c4) ▸
       at 0 1 (Sb⁻0-2-4-1 ∷ []) (refl) ▸ done


-- nat 3 SBOX(0;2;41;3): 7 steps
lem-nat-3-SBOX⟨0·2·41·3⟩ : WsL → ⟪ (Sw34 ∷ Sb0-2-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-31-4 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨0·2·41·3⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb0-2-41-3 ∷ []) (Sb0-2-31-4 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx0-2413 ∷ Toff314 ∷ Sb0-2-3-1 ∷ Toff314 ∷ Sb⁻0-2-3-1 ∷ []) (refl) ▸
       at 0 2 (Bx0-2314 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·2413⟩ c4) ▸
       at 1 2 (Toff413 ∷ Sw34 ∷ []) (wl0142 c4) ▸
       at 2 2 (Sb0-2-4-1 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·2·3·1⟩ c4) ▸
       at 3 2 (Toff413 ∷ Sw34 ∷ []) (wl0142 c4) ▸
       at 4 2 (Sb⁻0-2-4-1 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·2·3·1⟩ c4) ▸
       at 0 5 (Sb0-2-31-4 ∷ []) (refl) ▸ done


-- nat 3 BOX(2;014): 8 steps
lem-nat-3-BOX⟨2·014⟩ : WsL → ⟪ (Sw34 ∷ Bx2-014 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-013 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨2·014⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx2-014 ∷ []) (Bx2-013 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff201 ∷ Bx0-24 ∷ Toff201 ∷ CCZ012 ∷ Bx0-24 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 1 2 (Toff201 ∷ Sw34 ∷ []) (sym (c₃ (Toffᵗ) (Swap))) ▸
       at 2 2 (Bx0-23 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·24⟩ c4) ▸
       at 3 2 (Toff201 ∷ Sw34 ∷ []) (sym (c₃ (Toffᵗ) (Swap))) ▸
       at 4 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 5 2 (Bx0-23 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·24⟩ c4) ▸
       at 0 6 (Bx2-013 ∷ []) (refl) ▸ done


-- nat 3 BOX(0;2314): 8 steps
lem-nat-3-BOX⟨0·2314⟩ : WsL → ⟪ (Sw34 ∷ Bx0-2314 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2413 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·2314⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx0-2314 ∷ []) (Bx0-2413 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff023 ∷ Bx2-014 ∷ Toff023 ∷ CCZ023 ∷ Bx2-014 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw34 ∷ []) (lem-nat-3-CCZ023 c4) ▸
       at 1 2 (Toff024 ∷ Sw34 ∷ []) (lem-nat-3-TOFF023 c4) ▸
       at 2 2 (Bx2-013 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·014⟩ c4) ▸
       at 3 2 (Toff024 ∷ Sw34 ∷ []) (lem-nat-3-TOFF023 c4) ▸
       at 4 2 (CCZ024 ∷ Sw34 ∷ []) (lem-nat-3-CCZ023 c4) ▸
       at 5 2 (Bx2-013 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·014⟩ c4) ▸
       at 0 6 (Bx0-2413 ∷ []) (refl) ▸ done


-- nat 3 SBOX(0;2;4;1): 3 steps
lem-nat-3-SBOX⟨0·2·4·1⟩ : WsL → ⟪ (Sw34 ∷ Sb0-2-4-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-3-1 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨0·2·4·1⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb0-2-4-1 ∷ []) (Sb0-2-3-1 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS24 ∷ []) (refl) ▸
       at 0 2 (CS23 ∷ Sw34 ∷ []) (lem-nat-3-CS24 c4) ▸
       at 0 1 (Sb0-2-3-1 ∷ []) (refl) ▸ done


-- nat 3 SBOXd(0;2;4;1): 3 steps
lem-nat-3-SBOXd⟨0·2·4·1⟩ : WsL → ⟪ (Sw34 ∷ Sb⁻0-2-4-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-2-3-1 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨0·2·4·1⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb⁻0-2-4-1 ∷ []) (Sb⁻0-2-3-1 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS24⁻ ∷ []) (refl) ▸
       at 0 2 (CS23⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd24 c4) ▸
       at 0 1 (Sb⁻0-2-3-1 ∷ []) (refl) ▸ done


-- nat 3 SBOX(0;2;31;4): 7 steps
lem-nat-3-SBOX⟨0·2·31·4⟩ : WsL → ⟪ (Sw34 ∷ Sb0-2-31-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-41-3 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨0·2·31·4⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb0-2-31-4 ∷ []) (Sb0-2-41-3 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx0-2314 ∷ Toff413 ∷ Sb0-2-4-1 ∷ Toff413 ∷ Sb⁻0-2-4-1 ∷ []) (refl) ▸
       at 0 2 (Bx0-2413 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·2314⟩ c4) ▸
       at 1 2 (Toff314 ∷ Sw34 ∷ []) (wl0141 c4) ▸
       at 2 2 (Sb0-2-3-1 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·2·4·1⟩ c4) ▸
       at 3 2 (Toff314 ∷ Sw34 ∷ []) (wl0141 c4) ▸
       at 4 2 (Sb⁻0-2-3-1 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·2·4·1⟩ c4) ▸
       at 0 5 (Sb0-2-41-3 ∷ []) (refl) ▸ done


-- nat 0 BOX(2;103): 8 steps
lem-nat-0-BOX⟨2·103⟩ : WsL → ⟪ (Sw01 ∷ Bx2-103 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-013 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·103⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx2-103 ∷ []) (Bx2-013 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff201 ∷ Bx1-23 ∷ Toff201 ∷ CCZ012 ∷ Bx1-23 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw01 ∷ []) (sym (wl0096 c4)) ▸
       at 1 2 (Toff201 ∷ Sw01 ∷ []) (wl0107 c4) ▸
       at 2 2 (Bx0-23 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·23⟩ c4) ▸
       at 3 2 (Toff201 ∷ Sw01 ∷ []) (wl0107 c4) ▸
       at 4 2 (CCZ012 ∷ Sw01 ∷ []) (sym (wl0096 c4)) ▸
       at 5 2 (Bx0-23 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·23⟩ c4) ▸
       at 0 6 (Bx2-013 ∷ []) (refl) ▸ done


-- nat 0 BOX(1;2403): 8 steps
lem-nat-0-BOX⟨1·2403⟩ : WsL → ⟪ (Sw01 ∷ Bx1-2403 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2413 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·2403⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-2403 ∷ []) (Bx0-2413 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff124 ∷ Bx2-103 ∷ Toff124 ∷ CCZ124 ∷ Bx2-103 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 1 2 (Toff024 ∷ Sw01 ∷ []) (lem-nat-0-TOFF124 c4) ▸
       at 2 2 (Bx2-013 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·103⟩ c4) ▸
       at 3 2 (Toff024 ∷ Sw01 ∷ []) (lem-nat-0-TOFF124 c4) ▸
       at 4 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 5 2 (Bx2-013 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·103⟩ c4) ▸
       at 0 6 (Bx0-2413 ∷ []) (refl) ▸ done


-- nat 0 SBOX(1;2;3;0): 2 steps
lem-nat-0-SBOX⟨1·2·3·0⟩ : WsL → ⟪ (Sw01 ∷ Sb1-2-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-3-1 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨1·2·3·0⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb1-2-3-0 ∷ []) (Sb0-2-3-1 ∷ Sw01 ∷ [])
  b0 = at 0 2 (Sb1-2-3-0 ∷ Sw01 ∷ []) (c₂ (Swap) (CS)) ▸
       at 0 1 (Sb0-2-3-1 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 SBOXd(1;2;3;0): 2 steps
lem-nat-0-SBOXd⟨1·2·3·0⟩ : WsL → ⟪ (Sw01 ∷ Sb⁻1-2-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-2-3-1 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨1·2·3·0⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻1-2-3-0 ∷ []) (Sb⁻0-2-3-1 ∷ Sw01 ∷ [])
  b0 = at 0 2 (Sb⁻1-2-3-0 ∷ Sw01 ∷ []) (c₂ (Swap) (CS • CS • CS)) ▸
       at 0 1 (Sb⁻0-2-3-1 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 SBOX(1;2;40;3): 7 steps
lem-nat-0-SBOX⟨1·2·40·3⟩ : WsL → ⟪ (Sw01 ∷ Sb1-2-40-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-41-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨1·2·40·3⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb1-2-40-3 ∷ []) (Sb0-2-41-3 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx1-2403 ∷ Toff304 ∷ Sb1-2-3-0 ∷ Toff304 ∷ Sb⁻1-2-3-0 ∷ []) (refl) ▸
       at 0 2 (Bx0-2413 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·2403⟩ c4) ▸
       at 1 2 (Toff314 ∷ Sw01 ∷ []) (lem-nat-0-TOFF304 c4) ▸
       at 2 2 (Sb0-2-3-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·2·3·0⟩ c4) ▸
       at 3 2 (Toff314 ∷ Sw01 ∷ []) (lem-nat-0-TOFF304 c4) ▸
       at 4 2 (Sb⁻0-2-3-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·2·3·0⟩ c4) ▸
       at 0 5 (Sb0-2-41-3 ∷ []) (refl) ▸ done


-- nat 0 BOX(2;013): 8 steps
lem-nat-0-BOX⟨2·013⟩ : WsL → ⟪ (Sw01 ∷ Bx2-013 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-103 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·013⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx2-013 ∷ []) (Bx2-103 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff201 ∷ Bx0-23 ∷ Toff201 ∷ CCZ012 ∷ Bx0-23 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw01 ∷ []) (sym (wl0096 c4)) ▸
       at 1 2 (Toff201 ∷ Sw01 ∷ []) (wl0107 c4) ▸
       at 2 2 (Bx1-23 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·23⟩ c4) ▸
       at 3 2 (Toff201 ∷ Sw01 ∷ []) (wl0107 c4) ▸
       at 4 2 (CCZ012 ∷ Sw01 ∷ []) (sym (wl0096 c4)) ▸
       at 5 2 (Bx1-23 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·23⟩ c4) ▸
       at 0 6 (Bx2-103 ∷ []) (refl) ▸ done


-- nat 0 BOX(0;2413): 8 steps
lem-nat-0-BOX⟨0·2413⟩ : WsL → ⟪ (Sw01 ∷ Bx0-2413 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2403 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·2413⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-2413 ∷ []) (Bx1-2403 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff024 ∷ Bx2-013 ∷ Toff024 ∷ CCZ024 ∷ Bx2-013 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 1 2 (Toff124 ∷ Sw01 ∷ []) (lem-nat-0-TOFF024 c4) ▸
       at 2 2 (Bx2-103 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·013⟩ c4) ▸
       at 3 2 (Toff124 ∷ Sw01 ∷ []) (lem-nat-0-TOFF024 c4) ▸
       at 4 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 5 2 (Bx2-103 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·013⟩ c4) ▸
       at 0 6 (Bx1-2403 ∷ []) (refl) ▸ done


-- nat 0 SBOX(0;2;3;1): 2 steps
lem-nat-0-SBOX⟨0·2·3·1⟩ : WsL → ⟪ (Sw01 ∷ Sb0-2-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-3-0 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨0·2·3·1⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb0-2-3-1 ∷ []) (Sb1-2-3-0 ∷ Sw01 ∷ [])
  b0 = at 0 2 (Sb0-2-3-1 ∷ Sw01 ∷ []) (c₂ (Swap) (CS)) ▸
       at 0 1 (Sb1-2-3-0 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 SBOXd(0;2;3;1): 2 steps
lem-nat-0-SBOXd⟨0·2·3·1⟩ : WsL → ⟪ (Sw01 ∷ Sb⁻0-2-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-2-3-0 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨0·2·3·1⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻0-2-3-1 ∷ []) (Sb⁻1-2-3-0 ∷ Sw01 ∷ [])
  b0 = at 0 2 (Sb⁻0-2-3-1 ∷ Sw01 ∷ []) (c₂ (Swap) (CS • CS • CS)) ▸
       at 0 1 (Sb⁻1-2-3-0 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 SBOX(0;2;41;3): 7 steps
lem-nat-0-SBOX⟨0·2·41·3⟩ : WsL → ⟪ (Sw01 ∷ Sb0-2-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-40-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨0·2·41·3⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb0-2-41-3 ∷ []) (Sb1-2-40-3 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx0-2413 ∷ Toff314 ∷ Sb0-2-3-1 ∷ Toff314 ∷ Sb⁻0-2-3-1 ∷ []) (refl) ▸
       at 0 2 (Bx1-2403 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·2413⟩ c4) ▸
       at 1 2 (Toff304 ∷ Sw01 ∷ []) (lem-nat-0-TOFF314 c4) ▸
       at 2 2 (Sb1-2-3-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·2·3·1⟩ c4) ▸
       at 3 2 (Toff304 ∷ Sw01 ∷ []) (lem-nat-0-TOFF314 c4) ▸
       at 4 2 (Sb⁻1-2-3-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨0·2·3·1⟩ c4) ▸
       at 0 5 (Sb1-2-40-3 ∷ []) (refl) ▸ done


-- comm CX20 CCZ134: 23 steps
lem-comm-CX20-CCZ134 : WsL → ⟪ (CX20 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ CX20 ∷ []) ⟫ʷ
lem-comm-CX20-CCZ134 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX20 ∷ CCZ134 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ CCZ124 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Sw34 ∷ CCZ123 ∷ Sw34 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 1 3 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 2 3 (CX40 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 10 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 8 3 (CCZ124 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ CCZ124 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ CCZ123 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b1 = at 9 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 7 3 (CCZ134 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CCZ234 ∷ Sw12 ∷ []) (sym (wl0084 c4)) ▸
       at 5 2 (CCZ234 ∷ CX10 ∷ []) (c₂ (CX₁₀) (CCZ)) ▸
       at 4 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0034 c4)) ▸
       at 4 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0006 c4) ▸
       at 3 1 (Sw34 ∷ CCZ123 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ CCZ123 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (CCZ134 ∷ CX20 ∷ [])
  b2 = at 2 2 [] (wl0007 c4) ▸
       at 3 7 (CX40 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw34 ∷ CX30 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0007 c4) ▸
       at 4 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0006 c4) ▸
       at 0 5 (CCZ134 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 SBOX(0;1;4;2): 3 steps
lem-nat-0-SBOX⟨0·1·4·2⟩ : WsL → ⟪ (Sw01 ∷ Sb0-1-4-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-4-2 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨0·1·4·2⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb0-1-4-2 ∷ []) (Sb1-0-4-2 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS14 ∷ []) (refl) ▸
       at 0 2 (CS04 ∷ Sw01 ∷ []) (lem-nat-0-CS14 c4) ▸
       at 0 1 (Sb1-0-4-2 ∷ []) (refl) ▸ done


-- nat 0 SBOXd(0;1;4;2): 3 steps
lem-nat-0-SBOXd⟨0·1·4·2⟩ : WsL → ⟪ (Sw01 ∷ Sb⁻0-1-4-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-4-2 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨0·1·4·2⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻0-1-4-2 ∷ []) (Sb⁻1-0-4-2 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS14⁻ ∷ []) (refl) ▸
       at 0 2 (CS04⁻ ∷ Sw01 ∷ []) (lem-nat-0-CSd14 c4) ▸
       at 0 1 (Sb⁻1-0-4-2 ∷ []) (refl) ▸ done


-- nat 0 SBOX(0;1;32;4): 7 steps
lem-nat-0-SBOX⟨0·1·32·4⟩ : WsL → ⟪ (Sw01 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-32-4 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨0·1·32·4⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb0-1-32-4 ∷ []) (Sb1-0-32-4 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ []) (refl) ▸
       at 0 2 (Bx1-0324 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1324⟩ c4) ▸
       at 1 2 (Toff423 ∷ Sw01 ∷ []) (c₂ (Swap) (Toffᵗ)) ▸
       at 2 2 (Sb1-0-4-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·4·2⟩ c4) ▸
       at 3 2 (Toff423 ∷ Sw01 ∷ []) (c₂ (Swap) (Toffᵗ)) ▸
       at 4 2 (Sb⁻1-0-4-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨0·1·4·2⟩ c4) ▸
       at 0 5 (Sb1-0-32-4 ∷ []) (refl) ▸ done


-- nat 0 BOX(0;421): 8 steps
lem-nat-0-BOX⟨0·421⟩ : WsL → ⟪ (Sw01 ∷ Bx0-421 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-420 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·421⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-421 ∷ []) (Bx1-420 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff024 ∷ Bx4-01 ∷ Toff024 ∷ CCZ024 ∷ Bx4-01 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 1 2 (Toff124 ∷ Sw01 ∷ []) (lem-nat-0-TOFF024 c4) ▸
       at 2 2 (Bx4-10 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·01⟩ c4) ▸
       at 3 2 (Toff124 ∷ Sw01 ∷ []) (lem-nat-0-TOFF024 c4) ▸
       at 4 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 5 2 (Bx4-10 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·01⟩ c4) ▸
       at 0 6 (Bx1-420 ∷ []) (refl) ▸ done


-- nat 0 BOX(4;0321): 8 steps
lem-nat-0-BOX⟨4·0321⟩ : WsL → ⟪ (Sw01 ∷ Bx4-0321 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1320 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·0321⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx4-0321 ∷ []) (Bx4-1320 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff403 ∷ Bx0-421 ∷ Toff403 ∷ CCZ034 ∷ Bx0-421 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4) ▸
       at 1 2 (Toff413 ∷ Sw01 ∷ []) (lem-nat-0-TOFF403 c4) ▸
       at 2 2 (Bx1-420 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·421⟩ c4) ▸
       at 3 2 (Toff413 ∷ Sw01 ∷ []) (lem-nat-0-TOFF403 c4) ▸
       at 4 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4) ▸
       at 5 2 (Bx1-420 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·421⟩ c4) ▸
       at 0 6 (Bx4-1320 ∷ []) (refl) ▸ done


-- nat 0 SBOX(4;0;1;2): 3 steps
lem-nat-0-SBOX⟨4·0·1·2⟩ : WsL → ⟪ (Sw01 ∷ Sb4-0-1-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-1-0-2 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨4·0·1·2⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb4-0-1-2 ∷ []) (Sb4-1-0-2 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS01 ∷ []) (refl) ▸
       at 0 2 (CS01 ∷ Sw01 ∷ []) (sym (wl0132 c4)) ▸
       at 0 1 (Sb4-1-0-2 ∷ []) (refl) ▸ done


-- nat 0 SBOXd(4;0;1;2): 3 steps
lem-nat-0-SBOXd⟨4·0·1·2⟩ : WsL → ⟪ (Sw01 ∷ Sb⁻4-0-1-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻4-1-0-2 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨4·0·1·2⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻4-0-1-2 ∷ []) (Sb⁻4-1-0-2 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS01⁻ ∷ []) (refl) ▸
       at 0 2 (CS01⁻ ∷ Sw01 ∷ []) (sym (wl0133 c4)) ▸
       at 0 1 (Sb⁻4-1-0-2 ∷ []) (refl) ▸ done


-- nat 0 SBOX(4;0;32;1): 7 steps
lem-nat-0-SBOX⟨4·0·32·1⟩ : WsL → ⟪ (Sw01 ∷ Sb4-0-32-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-1-32-0 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨4·0·32·1⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb4-0-32-1 ∷ []) (Sb4-1-32-0 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx4-0321 ∷ Toff123 ∷ Sb4-0-1-2 ∷ Toff123 ∷ Sb⁻4-0-1-2 ∷ []) (refl) ▸
       at 0 2 (Bx4-1320 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·0321⟩ c4) ▸
       at 1 2 (Toff023 ∷ Sw01 ∷ []) (wl0053 c4) ▸
       at 2 2 (Sb4-1-0-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨4·0·1·2⟩ c4) ▸
       at 3 2 (Toff023 ∷ Sw01 ∷ []) (wl0053 c4) ▸
       at 4 2 (Sb⁻4-1-0-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨4·0·1·2⟩ c4) ▸
       at 0 5 (Sb4-1-32-0 ∷ []) (refl) ▸ done


-- nat 3 BOX(0;314): 8 steps
lem-nat-3-BOX⟨0·314⟩ : WsL → ⟪ (Sw34 ∷ Bx0-314 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-413 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·314⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx0-314 ∷ []) (Bx0-413 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff013 ∷ Bx3-04 ∷ Toff013 ∷ CCZ013 ∷ Bx3-04 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4) ▸
       at 1 2 (Toff014 ∷ Sw34 ∷ []) (lem-nat-3-TOFF013 c4) ▸
       at 2 2 (Bx4-03 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·04⟩ c4) ▸
       at 3 2 (Toff014 ∷ Sw34 ∷ []) (lem-nat-3-TOFF013 c4) ▸
       at 4 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4) ▸
       at 5 2 (Bx4-03 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·04⟩ c4) ▸
       at 0 6 (Bx0-413 ∷ []) (refl) ▸ done


-- nat 3 BOX(3;0214): 8 steps
lem-nat-3-BOX⟨3·0214⟩ : WsL → ⟪ (Sw34 ∷ Bx3-0214 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0213 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨3·0214⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx3-0214 ∷ []) (Bx4-0213 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff302 ∷ Bx0-314 ∷ Toff302 ∷ CCZ023 ∷ Bx0-314 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw34 ∷ []) (lem-nat-3-CCZ023 c4) ▸
       at 1 2 (Toff402 ∷ Sw34 ∷ []) (lem-nat-3-TOFF302 c4) ▸
       at 2 2 (Bx0-413 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·314⟩ c4) ▸
       at 3 2 (Toff402 ∷ Sw34 ∷ []) (lem-nat-3-TOFF302 c4) ▸
       at 4 2 (CCZ024 ∷ Sw34 ∷ []) (lem-nat-3-CCZ023 c4) ▸
       at 5 2 (Bx0-413 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·314⟩ c4) ▸
       at 0 6 (Bx4-0213 ∷ []) (refl) ▸ done


-- nat 1 BOX(4;03): 3 steps
lem-nat-1-BOX⟨4·03⟩ : WsL → ⟪ (Sw12 ∷ Bx4-03 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-03 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·03⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx4-03 ∷ []) (Bx4-03 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ03 ∷ []) (refl) ▸
       at 0 2 (CZ03 ∷ Sw12 ∷ []) (sym (wl0098 c4)) ▸
       at 0 1 (Bx4-03 ∷ []) (refl) ▸ done


-- nat 1 BOX(0;413): 8 steps
lem-nat-1-BOX⟨0·413⟩ : WsL → ⟪ (Sw12 ∷ Bx0-413 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-423 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·413⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-413 ∷ []) (Bx0-423 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff014 ∷ Bx4-03 ∷ Toff014 ∷ CCZ014 ∷ Bx4-03 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 1 2 (Toff024 ∷ Sw12 ∷ []) (lem-nat-1-TOFF014 c4) ▸
       at 2 2 (Bx4-03 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·03⟩ c4) ▸
       at 3 2 (Toff024 ∷ Sw12 ∷ []) (lem-nat-1-TOFF014 c4) ▸
       at 4 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 5 2 (Bx4-03 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·03⟩ c4) ▸
       at 0 6 (Bx0-423 ∷ []) (refl) ▸ done


-- nat 1 BOX(4;0213): 8 steps
lem-nat-1-BOX⟨4·0213⟩ : WsL → ⟪ (Sw12 ∷ Bx4-0213 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0123 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·0213⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx4-0213 ∷ []) (Bx4-0123 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff402 ∷ Bx0-413 ∷ Toff402 ∷ CCZ024 ∷ Bx0-413 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 1 2 (Toff401 ∷ Sw12 ∷ []) (lem-nat-1-TOFF402 c4) ▸
       at 2 2 (Bx0-423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·413⟩ c4) ▸
       at 3 2 (Toff401 ∷ Sw12 ∷ []) (lem-nat-1-TOFF402 c4) ▸
       at 4 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 5 2 (Bx0-423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·413⟩ c4) ▸
       at 0 6 (Bx4-0123 ∷ []) (refl) ▸ done


-- nat 2 BOX(0;412): 8 steps
lem-nat-2-BOX⟨0·412⟩ : WsL → ⟪ (Sw23 ∷ Bx0-412 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-413 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·412⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-412 ∷ []) (Bx0-413 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff014 ∷ Bx4-02 ∷ Toff014 ∷ CCZ014 ∷ Bx4-02 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 1 2 (Toff014 ∷ Sw23 ∷ []) (lem-nat-2-TOFF014 c4) ▸
       at 2 2 (Bx4-03 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·02⟩ c4) ▸
       at 3 2 (Toff014 ∷ Sw23 ∷ []) (lem-nat-2-TOFF014 c4) ▸
       at 4 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 5 2 (Bx4-03 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·02⟩ c4) ▸
       at 0 6 (Bx0-413 ∷ []) (refl) ▸ done


-- nat 2 BOX(4;0312): 8 steps
lem-nat-2-BOX⟨4·0312⟩ : WsL → ⟪ (Sw23 ∷ Bx4-0312 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0213 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·0312⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx4-0312 ∷ []) (Bx4-0213 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff403 ∷ Bx0-412 ∷ Toff403 ∷ CCZ034 ∷ Bx0-412 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 1 2 (Toff402 ∷ Sw23 ∷ []) (lem-nat-2-TOFF403 c4) ▸
       at 2 2 (Bx0-413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·412⟩ c4) ▸
       at 3 2 (Toff402 ∷ Sw23 ∷ []) (lem-nat-2-TOFF403 c4) ▸
       at 4 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 5 2 (Bx0-413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·412⟩ c4) ▸
       at 0 6 (Bx4-0213 ∷ []) (refl) ▸ done


-- nat 1 BOX(0;421): 8 steps
lem-nat-1-BOX⟨0·421⟩ : WsL → ⟪ (Sw12 ∷ Bx0-421 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-412 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·421⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-421 ∷ []) (Bx0-412 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff024 ∷ Bx4-01 ∷ Toff024 ∷ CCZ024 ∷ Bx4-01 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 1 2 (Toff014 ∷ Sw12 ∷ []) (lem-nat-1-TOFF024 c4) ▸
       at 2 2 (Bx4-02 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·01⟩ c4) ▸
       at 3 2 (Toff014 ∷ Sw12 ∷ []) (lem-nat-1-TOFF024 c4) ▸
       at 4 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 5 2 (Bx4-02 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·01⟩ c4) ▸
       at 0 6 (Bx0-412 ∷ []) (refl) ▸ done


-- nat 1 BOX(4;0321): 8 steps
lem-nat-1-BOX⟨4·0321⟩ : WsL → ⟪ (Sw12 ∷ Bx4-0321 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0312 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·0321⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx4-0321 ∷ []) (Bx4-0312 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff403 ∷ Bx0-421 ∷ Toff403 ∷ CCZ034 ∷ Bx0-421 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 1 2 (Toff403 ∷ Sw12 ∷ []) (lem-nat-1-TOFF403 c4) ▸
       at 2 2 (Bx0-412 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·421⟩ c4) ▸
       at 3 2 (Toff403 ∷ Sw12 ∷ []) (lem-nat-1-TOFF403 c4) ▸
       at 4 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 5 2 (Bx0-412 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·421⟩ c4) ▸
       at 0 6 (Bx4-0312 ∷ []) (refl) ▸ done


-- nat 0 BOX(1;420): 8 steps
lem-nat-0-BOX⟨1·420⟩ : WsL → ⟪ (Sw01 ∷ Bx1-420 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-421 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·420⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-420 ∷ []) (Bx0-421 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff124 ∷ Bx4-10 ∷ Toff124 ∷ CCZ124 ∷ Bx4-10 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 1 2 (Toff024 ∷ Sw01 ∷ []) (lem-nat-0-TOFF124 c4) ▸
       at 2 2 (Bx4-01 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·10⟩ c4) ▸
       at 3 2 (Toff024 ∷ Sw01 ∷ []) (lem-nat-0-TOFF124 c4) ▸
       at 4 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 5 2 (Bx4-01 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·10⟩ c4) ▸
       at 0 6 (Bx0-421 ∷ []) (refl) ▸ done


-- nat 0 BOX(4;1320): 8 steps
lem-nat-0-BOX⟨4·1320⟩ : WsL → ⟪ (Sw01 ∷ Bx4-1320 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0321 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·1320⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx4-1320 ∷ []) (Bx4-0321 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff413 ∷ Bx1-420 ∷ Toff413 ∷ CCZ134 ∷ Bx1-420 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 1 2 (Toff403 ∷ Sw01 ∷ []) (lem-nat-0-TOFF413 c4) ▸
       at 2 2 (Bx0-421 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·420⟩ c4) ▸
       at 3 2 (Toff403 ∷ Sw01 ∷ []) (lem-nat-0-TOFF413 c4) ▸
       at 4 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 5 2 (Bx0-421 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·420⟩ c4) ▸
       at 0 6 (Bx4-0321 ∷ []) (refl) ▸ done


-- nat 1 BOX(0;423): 8 steps
lem-nat-1-BOX⟨0·423⟩ : WsL → ⟪ (Sw12 ∷ Bx0-423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-413 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·423⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-423 ∷ []) (Bx0-413 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff024 ∷ Bx4-03 ∷ Toff024 ∷ CCZ024 ∷ Bx4-03 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 1 2 (Toff014 ∷ Sw12 ∷ []) (lem-nat-1-TOFF024 c4) ▸
       at 2 2 (Bx4-03 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·03⟩ c4) ▸
       at 3 2 (Toff014 ∷ Sw12 ∷ []) (lem-nat-1-TOFF024 c4) ▸
       at 4 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 5 2 (Bx4-03 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·03⟩ c4) ▸
       at 0 6 (Bx0-413 ∷ []) (refl) ▸ done


-- nat 1 BOX(4;0123): 8 steps
lem-nat-1-BOX⟨4·0123⟩ : WsL → ⟪ (Sw12 ∷ Bx4-0123 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0213 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·0123⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx4-0123 ∷ []) (Bx4-0213 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff401 ∷ Bx0-423 ∷ Toff401 ∷ CCZ014 ∷ Bx0-423 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 1 2 (Toff402 ∷ Sw12 ∷ []) (lem-nat-1-TOFF401 c4) ▸
       at 2 2 (Bx0-413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·423⟩ c4) ▸
       at 3 2 (Toff402 ∷ Sw12 ∷ []) (lem-nat-1-TOFF401 c4) ▸
       at 4 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 5 2 (Bx0-413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·423⟩ c4) ▸
       at 0 6 (Bx4-0213 ∷ []) (refl) ▸ done


-- nat 0 BOX(4;03): 3 steps
lem-nat-0-BOX⟨4·03⟩ : WsL → ⟪ (Sw01 ∷ Bx4-03 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-13 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·03⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx4-03 ∷ []) (Bx4-13 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CZ03 ∷ []) (refl) ▸
       at 0 2 (CZ13 ∷ Sw01 ∷ []) (sym (wl0092 c4)) ▸
       at 0 1 (Bx4-13 ∷ []) (refl) ▸ done


-- nat 0 BOX(0;413): 8 steps
lem-nat-0-BOX⟨0·413⟩ : WsL → ⟪ (Sw01 ∷ Bx0-413 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-403 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·413⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-413 ∷ []) (Bx1-403 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff014 ∷ Bx4-03 ∷ Toff014 ∷ CCZ014 ∷ Bx4-03 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 1 2 (Toff104 ∷ Sw01 ∷ []) (lem-nat-0-TOFF014 c4) ▸
       at 2 2 (Bx4-13 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·03⟩ c4) ▸
       at 3 2 (Toff104 ∷ Sw01 ∷ []) (lem-nat-0-TOFF014 c4) ▸
       at 4 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 5 2 (Bx4-13 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·03⟩ c4) ▸
       at 0 6 (Bx1-403 ∷ []) (refl) ▸ done


-- nat 0 BOX(4;0213): 8 steps
lem-nat-0-BOX⟨4·0213⟩ : WsL → ⟪ (Sw01 ∷ Bx4-0213 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1203 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·0213⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx4-0213 ∷ []) (Bx4-1203 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff402 ∷ Bx0-413 ∷ Toff402 ∷ CCZ024 ∷ Bx0-413 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 1 2 (Toff412 ∷ Sw01 ∷ []) (lem-nat-0-TOFF402 c4) ▸
       at 2 2 (Bx1-403 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·413⟩ c4) ▸
       at 3 2 (Toff412 ∷ Sw01 ∷ []) (lem-nat-0-TOFF402 c4) ▸
       at 4 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 5 2 (Bx1-403 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·413⟩ c4) ▸
       at 0 6 (Bx4-1203 ∷ []) (refl) ▸ done


-- nat 0 BOX(4;13): 3 steps
lem-nat-0-BOX⟨4·13⟩ : WsL → ⟪ (Sw01 ∷ Bx4-13 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-03 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·13⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx4-13 ∷ []) (Bx4-03 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CZ13 ∷ []) (refl) ▸
       at 0 2 (CZ03 ∷ Sw01 ∷ []) (sym (wl0088 c4)) ▸
       at 0 1 (Bx4-03 ∷ []) (refl) ▸ done


-- nat 0 BOX(0;423): 8 steps
lem-nat-0-BOX⟨0·423⟩ : WsL → ⟪ (Sw01 ∷ Bx0-423 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-423 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·423⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-423 ∷ []) (Bx1-423 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff024 ∷ Bx4-03 ∷ Toff024 ∷ CCZ024 ∷ Bx4-03 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 1 2 (Toff124 ∷ Sw01 ∷ []) (lem-nat-0-TOFF024 c4) ▸
       at 2 2 (Bx4-13 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·03⟩ c4) ▸
       at 3 2 (Toff124 ∷ Sw01 ∷ []) (lem-nat-0-TOFF024 c4) ▸
       at 4 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 5 2 (Bx4-13 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·03⟩ c4) ▸
       at 0 6 (Bx1-423 ∷ []) (refl) ▸ done


-- nat 0 BOX(4;0123): 8 steps
lem-nat-0-BOX⟨4·0123⟩ : WsL → ⟪ (Sw01 ∷ Bx4-0123 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1023 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·0123⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx4-0123 ∷ []) (Bx4-1023 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff401 ∷ Bx0-423 ∷ Toff401 ∷ CCZ014 ∷ Bx0-423 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 1 2 (Toff401 ∷ Sw01 ∷ []) (lem-nat-0-TOFF401 c4) ▸
       at 2 2 (Bx1-423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·423⟩ c4) ▸
       at 3 2 (Toff401 ∷ Sw01 ∷ []) (lem-nat-0-TOFF401 c4) ▸
       at 4 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 5 2 (Bx1-423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·423⟩ c4) ▸
       at 0 6 (Bx4-1023 ∷ []) (refl) ▸ done


-- nat 0 BOX(1;423): 8 steps
lem-nat-0-BOX⟨1·423⟩ : WsL → ⟪ (Sw01 ∷ Bx1-423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-423 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·423⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-423 ∷ []) (Bx0-423 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff124 ∷ Bx4-13 ∷ Toff124 ∷ CCZ124 ∷ Bx4-13 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 1 2 (Toff024 ∷ Sw01 ∷ []) (lem-nat-0-TOFF124 c4) ▸
       at 2 2 (Bx4-03 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·13⟩ c4) ▸
       at 3 2 (Toff024 ∷ Sw01 ∷ []) (lem-nat-0-TOFF124 c4) ▸
       at 4 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 5 2 (Bx4-03 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·13⟩ c4) ▸
       at 0 6 (Bx0-423 ∷ []) (refl) ▸ done


-- nat 0 BOX(4;1023): 8 steps
lem-nat-0-BOX⟨4·1023⟩ : WsL → ⟪ (Sw01 ∷ Bx4-1023 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0123 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·1023⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx4-1023 ∷ []) (Bx4-0123 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff401 ∷ Bx1-423 ∷ Toff401 ∷ CCZ014 ∷ Bx1-423 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 1 2 (Toff401 ∷ Sw01 ∷ []) (lem-nat-0-TOFF401 c4) ▸
       at 2 2 (Bx0-423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·423⟩ c4) ▸
       at 3 2 (Toff401 ∷ Sw01 ∷ []) (lem-nat-0-TOFF401 c4) ▸
       at 4 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 5 2 (Bx0-423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·423⟩ c4) ▸
       at 0 6 (Bx4-0123 ∷ []) (refl) ▸ done


-- nat 2 BOX(0;413): 8 steps
lem-nat-2-BOX⟨0·413⟩ : WsL → ⟪ (Sw23 ∷ Bx0-413 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-412 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·413⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-413 ∷ []) (Bx0-412 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff014 ∷ Bx4-03 ∷ Toff014 ∷ CCZ014 ∷ Bx4-03 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 1 2 (Toff014 ∷ Sw23 ∷ []) (lem-nat-2-TOFF014 c4) ▸
       at 2 2 (Bx4-02 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·03⟩ c4) ▸
       at 3 2 (Toff014 ∷ Sw23 ∷ []) (lem-nat-2-TOFF014 c4) ▸
       at 4 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 5 2 (Bx4-02 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·03⟩ c4) ▸
       at 0 6 (Bx0-412 ∷ []) (refl) ▸ done


-- nat 2 BOX(4;0213): 8 steps
lem-nat-2-BOX⟨4·0213⟩ : WsL → ⟪ (Sw23 ∷ Bx4-0213 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0312 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·0213⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx4-0213 ∷ []) (Bx4-0312 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff402 ∷ Bx0-413 ∷ Toff402 ∷ CCZ024 ∷ Bx0-413 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 1 2 (Toff403 ∷ Sw23 ∷ []) (lem-nat-2-TOFF402 c4) ▸
       at 2 2 (Bx0-412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·413⟩ c4) ▸
       at 3 2 (Toff403 ∷ Sw23 ∷ []) (lem-nat-2-TOFF402 c4) ▸
       at 4 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 5 2 (Bx0-412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·413⟩ c4) ▸
       at 0 6 (Bx4-0312 ∷ []) (refl) ▸ done


-- nat 3 BOX(3;14): 3 steps
lem-nat-3-BOX⟨3·14⟩ : WsL → ⟪ (Sw34 ∷ Bx3-14 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-13 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨3·14⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx3-14 ∷ []) (Bx4-13 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CZ14 ∷ []) (refl) ▸
       at 0 2 (CZ13 ∷ Sw34 ∷ []) (lem-nat-3-CZ14 c4) ▸
       at 0 1 (Bx4-13 ∷ []) (refl) ▸ done


-- nat 3 BOX(1;324): 8 steps
lem-nat-3-BOX⟨1·324⟩ : WsL → ⟪ (Sw34 ∷ Bx1-324 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-423 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨1·324⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx1-324 ∷ []) (Bx1-423 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff123 ∷ Bx3-14 ∷ Toff123 ∷ CCZ123 ∷ Bx3-14 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw34 ∷ []) (lem-nat-3-CCZ123 c4) ▸
       at 1 2 (Toff124 ∷ Sw34 ∷ []) (lem-nat-3-TOFF123 c4) ▸
       at 2 2 (Bx4-13 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·14⟩ c4) ▸
       at 3 2 (Toff124 ∷ Sw34 ∷ []) (lem-nat-3-TOFF123 c4) ▸
       at 4 2 (CCZ124 ∷ Sw34 ∷ []) (lem-nat-3-CCZ123 c4) ▸
       at 5 2 (Bx4-13 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·14⟩ c4) ▸
       at 0 6 (Bx1-423 ∷ []) (refl) ▸ done


-- nat 3 BOX(3;1024): 8 steps
lem-nat-3-BOX⟨3·1024⟩ : WsL → ⟪ (Sw34 ∷ Bx3-1024 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1023 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨3·1024⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx3-1024 ∷ []) (Bx4-1023 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff301 ∷ Bx1-324 ∷ Toff301 ∷ CCZ013 ∷ Bx1-324 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4) ▸
       at 1 2 (Toff401 ∷ Sw34 ∷ []) (lem-nat-3-TOFF301 c4) ▸
       at 2 2 (Bx1-423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·324⟩ c4) ▸
       at 3 2 (Toff401 ∷ Sw34 ∷ []) (lem-nat-3-TOFF301 c4) ▸
       at 4 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4) ▸
       at 5 2 (Bx1-423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·324⟩ c4) ▸
       at 0 6 (Bx4-1023 ∷ []) (refl) ▸ done


-- nat 1 BOX(4;13): 3 steps
lem-nat-1-BOX⟨4·13⟩ : WsL → ⟪ (Sw12 ∷ Bx4-13 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-23 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·13⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx4-13 ∷ []) (Bx4-23 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ13 ∷ []) (refl) ▸
       at 0 2 (CZ23 ∷ Sw12 ∷ []) (sym (wl0029 c4)) ▸
       at 0 1 (Bx4-23 ∷ []) (refl) ▸ done


-- nat 1 BOX(1;423): 8 steps
lem-nat-1-BOX⟨1·423⟩ : WsL → ⟪ (Sw12 ∷ Bx1-423 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-413 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·423⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx1-423 ∷ []) (Bx2-413 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff124 ∷ Bx4-13 ∷ Toff124 ∷ CCZ124 ∷ Bx4-13 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw12 ∷ []) (sym (wl0078 c4)) ▸
       at 1 2 (Toff214 ∷ Sw12 ∷ []) (wl0095 c4) ▸
       at 2 2 (Bx4-23 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·13⟩ c4) ▸
       at 3 2 (Toff214 ∷ Sw12 ∷ []) (wl0095 c4) ▸
       at 4 2 (CCZ124 ∷ Sw12 ∷ []) (sym (wl0078 c4)) ▸
       at 5 2 (Bx4-23 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·13⟩ c4) ▸
       at 0 6 (Bx2-413 ∷ []) (refl) ▸ done


-- nat 1 BOX(4;1023): 8 steps
lem-nat-1-BOX⟨4·1023⟩ : WsL → ⟪ (Sw12 ∷ Bx4-1023 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2013 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·1023⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx4-1023 ∷ []) (Bx4-2013 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff401 ∷ Bx1-423 ∷ Toff401 ∷ CCZ014 ∷ Bx1-423 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 1 2 (Toff402 ∷ Sw12 ∷ []) (lem-nat-1-TOFF401 c4) ▸
       at 2 2 (Bx2-413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·423⟩ c4) ▸
       at 3 2 (Toff402 ∷ Sw12 ∷ []) (lem-nat-1-TOFF401 c4) ▸
       at 4 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 5 2 (Bx2-413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·423⟩ c4) ▸
       at 0 6 (Bx4-2013 ∷ []) (refl) ▸ done


-- nat 2 BOX(4;23): 3 steps
lem-nat-2-BOX⟨4·23⟩ : WsL → ⟪ (Sw23 ∷ Bx4-23 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-32 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·23⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx4-23 ∷ []) (Bx4-32 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ23 ∷ []) (refl) ▸
       at 0 2 (CZ23 ∷ Sw23 ∷ []) (sym (wl0045 c4)) ▸
       at 0 1 (Bx4-32 ∷ []) (refl) ▸ done


-- nat 2 BOX(2;413): 8 steps
lem-nat-2-BOX⟨2·413⟩ : WsL → ⟪ (Sw23 ∷ Bx2-413 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-412 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·413⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx2-413 ∷ []) (Bx3-412 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff214 ∷ Bx4-23 ∷ Toff214 ∷ CCZ124 ∷ Bx4-23 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 1 2 (Toff314 ∷ Sw23 ∷ []) (lem-nat-2-TOFF214 c4) ▸
       at 2 2 (Bx4-32 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·23⟩ c4) ▸
       at 3 2 (Toff314 ∷ Sw23 ∷ []) (lem-nat-2-TOFF214 c4) ▸
       at 4 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 5 2 (Bx4-32 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·23⟩ c4) ▸
       at 0 6 (Bx3-412 ∷ []) (refl) ▸ done


-- nat 2 BOX(4;2013): 8 steps
lem-nat-2-BOX⟨4·2013⟩ : WsL → ⟪ (Sw23 ∷ Bx4-2013 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3012 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·2013⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx4-2013 ∷ []) (Bx4-3012 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff402 ∷ Bx2-413 ∷ Toff402 ∷ CCZ024 ∷ Bx2-413 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 1 2 (Toff403 ∷ Sw23 ∷ []) (lem-nat-2-TOFF402 c4) ▸
       at 2 2 (Bx3-412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·413⟩ c4) ▸
       at 3 2 (Toff403 ∷ Sw23 ∷ []) (lem-nat-2-TOFF402 c4) ▸
       at 4 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 5 2 (Bx3-412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·413⟩ c4) ▸
       at 0 6 (Bx4-3012 ∷ []) (refl) ▸ done


-- nat 1 BOX(4;23): 3 steps
lem-nat-1-BOX⟨4·23⟩ : WsL → ⟪ (Sw12 ∷ Bx4-23 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-13 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·23⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx4-23 ∷ []) (Bx4-13 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ23 ∷ []) (refl) ▸
       at 0 2 (CZ13 ∷ Sw12 ∷ []) (sym (wl0026 c4)) ▸
       at 0 1 (Bx4-13 ∷ []) (refl) ▸ done


-- nat 1 BOX(2;413): 8 steps
lem-nat-1-BOX⟨2·413⟩ : WsL → ⟪ (Sw12 ∷ Bx2-413 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-423 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·413⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx2-413 ∷ []) (Bx1-423 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff214 ∷ Bx4-23 ∷ Toff214 ∷ CCZ124 ∷ Bx4-23 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw12 ∷ []) (sym (wl0078 c4)) ▸
       at 1 2 (Toff124 ∷ Sw12 ∷ []) (wl0126 c4) ▸
       at 2 2 (Bx4-13 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·23⟩ c4) ▸
       at 3 2 (Toff124 ∷ Sw12 ∷ []) (wl0126 c4) ▸
       at 4 2 (CCZ124 ∷ Sw12 ∷ []) (sym (wl0078 c4)) ▸
       at 5 2 (Bx4-13 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·23⟩ c4) ▸
       at 0 6 (Bx1-423 ∷ []) (refl) ▸ done


-- nat 1 BOX(4;2013): 8 steps
lem-nat-1-BOX⟨4·2013⟩ : WsL → ⟪ (Sw12 ∷ Bx4-2013 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1023 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·2013⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx4-2013 ∷ []) (Bx4-1023 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff402 ∷ Bx2-413 ∷ Toff402 ∷ CCZ024 ∷ Bx2-413 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 1 2 (Toff401 ∷ Sw12 ∷ []) (lem-nat-1-TOFF402 c4) ▸
       at 2 2 (Bx1-423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·413⟩ c4) ▸
       at 3 2 (Toff401 ∷ Sw12 ∷ []) (lem-nat-1-TOFF402 c4) ▸
       at 4 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 5 2 (Bx1-423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·413⟩ c4) ▸
       at 0 6 (Bx4-1023 ∷ []) (refl) ▸ done


-- nat 1 BOX(4;12): 3 steps
lem-nat-1-BOX⟨4·12⟩ : WsL → ⟪ (Sw12 ∷ Bx4-12 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-21 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·12⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx4-12 ∷ []) (Bx4-21 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ12 ∷ []) (refl) ▸
       at 0 2 (CZ12 ∷ Sw12 ∷ []) (sym (wl0109 c4)) ▸
       at 0 1 (Bx4-21 ∷ []) (refl) ▸ done


-- nat 1 BOX(1;432): 8 steps
lem-nat-1-BOX⟨1·432⟩ : WsL → ⟪ (Sw12 ∷ Bx1-432 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-431 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·432⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx1-432 ∷ []) (Bx2-431 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff134 ∷ Bx4-12 ∷ Toff134 ∷ CCZ134 ∷ Bx4-12 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw12 ∷ []) (sym (wl0084 c4)) ▸
       at 1 2 (Toff234 ∷ Sw12 ∷ []) (wl0136 c4) ▸
       at 2 2 (Bx4-21 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·12⟩ c4) ▸
       at 3 2 (Toff234 ∷ Sw12 ∷ []) (wl0136 c4) ▸
       at 4 2 (CCZ234 ∷ Sw12 ∷ []) (sym (wl0084 c4)) ▸
       at 5 2 (Bx4-21 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·12⟩ c4) ▸
       at 0 6 (Bx2-431 ∷ []) (refl) ▸ done


-- nat 1 BOX(4;1032): 8 steps
lem-nat-1-BOX⟨4·1032⟩ : WsL → ⟪ (Sw12 ∷ Bx4-1032 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2031 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·1032⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx4-1032 ∷ []) (Bx4-2031 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff401 ∷ Bx1-432 ∷ Toff401 ∷ CCZ014 ∷ Bx1-432 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 1 2 (Toff402 ∷ Sw12 ∷ []) (lem-nat-1-TOFF401 c4) ▸
       at 2 2 (Bx2-431 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·432⟩ c4) ▸
       at 3 2 (Toff402 ∷ Sw12 ∷ []) (lem-nat-1-TOFF401 c4) ▸
       at 4 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 5 2 (Bx2-431 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·432⟩ c4) ▸
       at 0 6 (Bx4-2031 ∷ []) (refl) ▸ done


-- nat 2 BOX(4;32): 3 steps
lem-nat-2-BOX⟨4·32⟩ : WsL → ⟪ (Sw23 ∷ Bx4-32 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-23 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·32⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx4-32 ∷ []) (Bx4-23 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ23 ∷ []) (refl) ▸
       at 0 2 (CZ23 ∷ Sw23 ∷ []) (sym (wl0045 c4)) ▸
       at 0 1 (Bx4-23 ∷ []) (refl) ▸ done


-- nat 2 BOX(3;412): 8 steps
lem-nat-2-BOX⟨3·412⟩ : WsL → ⟪ (Sw23 ∷ Bx3-412 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-413 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·412⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx3-412 ∷ []) (Bx2-413 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff314 ∷ Bx4-32 ∷ Toff314 ∷ CCZ134 ∷ Bx4-32 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 1 2 (Toff214 ∷ Sw23 ∷ []) (lem-nat-2-TOFF314 c4) ▸
       at 2 2 (Bx4-23 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·32⟩ c4) ▸
       at 3 2 (Toff214 ∷ Sw23 ∷ []) (lem-nat-2-TOFF314 c4) ▸
       at 4 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 5 2 (Bx4-23 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·32⟩ c4) ▸
       at 0 6 (Bx2-413 ∷ []) (refl) ▸ done


-- nat 2 BOX(4;3012): 8 steps
lem-nat-2-BOX⟨4·3012⟩ : WsL → ⟪ (Sw23 ∷ Bx4-3012 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2013 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·3012⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx4-3012 ∷ []) (Bx4-2013 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff403 ∷ Bx3-412 ∷ Toff403 ∷ CCZ034 ∷ Bx3-412 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 1 2 (Toff402 ∷ Sw23 ∷ []) (lem-nat-2-TOFF403 c4) ▸
       at 2 2 (Bx2-413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·412⟩ c4) ▸
       at 3 2 (Toff402 ∷ Sw23 ∷ []) (lem-nat-2-TOFF403 c4) ▸
       at 4 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 5 2 (Bx2-413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·412⟩ c4) ▸
       at 0 6 (Bx4-2013 ∷ []) (refl) ▸ done


-- nat 1 BOX(1;403): 8 steps
lem-nat-1-BOX⟨1·403⟩ : WsL → ⟪ (Sw12 ∷ Bx1-403 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-403 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·403⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx1-403 ∷ []) (Bx2-403 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff104 ∷ Bx4-13 ∷ Toff104 ∷ CCZ014 ∷ Bx4-13 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 1 2 (Toff204 ∷ Sw12 ∷ []) (lem-nat-1-TOFF104 c4) ▸
       at 2 2 (Bx4-23 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·13⟩ c4) ▸
       at 3 2 (Toff204 ∷ Sw12 ∷ []) (lem-nat-1-TOFF104 c4) ▸
       at 4 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 5 2 (Bx4-23 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·13⟩ c4) ▸
       at 0 6 (Bx2-403 ∷ []) (refl) ▸ done


-- nat 1 BOX(4;1203): 8 steps
lem-nat-1-BOX⟨4·1203⟩ : WsL → ⟪ (Sw12 ∷ Bx4-1203 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2103 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·1203⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx4-1203 ∷ []) (Bx4-2103 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff412 ∷ Bx1-403 ∷ Toff412 ∷ CCZ124 ∷ Bx1-403 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw12 ∷ []) (sym (wl0078 c4)) ▸
       at 1 2 (Toff412 ∷ Sw12 ∷ []) (wl0079 c4) ▸
       at 2 2 (Bx2-403 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·403⟩ c4) ▸
       at 3 2 (Toff412 ∷ Sw12 ∷ []) (wl0079 c4) ▸
       at 4 2 (CCZ124 ∷ Sw12 ∷ []) (sym (wl0078 c4)) ▸
       at 5 2 (Bx2-403 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·403⟩ c4) ▸
       at 0 6 (Bx4-2103 ∷ []) (refl) ▸ done


-- nat 2 BOX(2;403): 8 steps
lem-nat-2-BOX⟨2·403⟩ : WsL → ⟪ (Sw23 ∷ Bx2-403 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-402 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·403⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx2-403 ∷ []) (Bx3-402 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff204 ∷ Bx4-23 ∷ Toff204 ∷ CCZ024 ∷ Bx4-23 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 1 2 (Toff304 ∷ Sw23 ∷ []) (lem-nat-2-TOFF204 c4) ▸
       at 2 2 (Bx4-32 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·23⟩ c4) ▸
       at 3 2 (Toff304 ∷ Sw23 ∷ []) (lem-nat-2-TOFF204 c4) ▸
       at 4 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 5 2 (Bx4-32 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·23⟩ c4) ▸
       at 0 6 (Bx3-402 ∷ []) (refl) ▸ done


-- nat 2 BOX(4;2103): 8 steps
lem-nat-2-BOX⟨4·2103⟩ : WsL → ⟪ (Sw23 ∷ Bx4-2103 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3102 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·2103⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx4-2103 ∷ []) (Bx4-3102 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff412 ∷ Bx2-403 ∷ Toff412 ∷ CCZ124 ∷ Bx2-403 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 1 2 (Toff413 ∷ Sw23 ∷ []) (lem-nat-2-TOFF412 c4) ▸
       at 2 2 (Bx3-402 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·403⟩ c4) ▸
       at 3 2 (Toff413 ∷ Sw23 ∷ []) (lem-nat-2-TOFF412 c4) ▸
       at 4 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 5 2 (Bx3-402 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·403⟩ c4) ▸
       at 0 6 (Bx4-3102 ∷ []) (refl) ▸ done


-- nat 0 BOX(3;402): 8 steps
lem-nat-0-BOX⟨3·402⟩ : WsL → ⟪ (Sw01 ∷ Bx3-402 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-412 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·402⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx3-402 ∷ []) (Bx3-412 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff304 ∷ Bx4-32 ∷ Toff304 ∷ CCZ034 ∷ Bx4-32 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4) ▸
       at 1 2 (Toff314 ∷ Sw01 ∷ []) (lem-nat-0-TOFF304 c4) ▸
       at 2 2 (Bx4-32 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ)) ▸
       at 3 2 (Toff314 ∷ Sw01 ∷ []) (lem-nat-0-TOFF304 c4) ▸
       at 4 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4) ▸
       at 5 2 (Bx4-32 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ)) ▸
       at 0 6 (Bx3-412 ∷ []) (refl) ▸ done


-- nat 0 BOX(4;3102): 8 steps
lem-nat-0-BOX⟨4·3102⟩ : WsL → ⟪ (Sw01 ∷ Bx4-3102 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3012 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·3102⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx4-3102 ∷ []) (Bx4-3012 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff413 ∷ Bx3-402 ∷ Toff413 ∷ CCZ134 ∷ Bx3-402 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 1 2 (Toff403 ∷ Sw01 ∷ []) (lem-nat-0-TOFF413 c4) ▸
       at 2 2 (Bx3-412 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·402⟩ c4) ▸
       at 3 2 (Toff403 ∷ Sw01 ∷ []) (lem-nat-0-TOFF413 c4) ▸
       at 4 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 5 2 (Bx3-412 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·402⟩ c4) ▸
       at 0 6 (Bx4-3012 ∷ []) (refl) ▸ done


-- nat 1 BOX(4;21): 3 steps
lem-nat-1-BOX⟨4·21⟩ : WsL → ⟪ (Sw12 ∷ Bx4-21 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-12 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·21⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx4-21 ∷ []) (Bx4-12 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ12 ∷ []) (refl) ▸
       at 0 2 (CZ12 ∷ Sw12 ∷ []) (sym (wl0109 c4)) ▸
       at 0 1 (Bx4-12 ∷ []) (refl) ▸ done


-- nat 1 BOX(2;14): 3 steps
lem-nat-1-BOX⟨2·14⟩ : WsL → ⟪ (Sw12 ∷ Bx2-14 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-24 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·14⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx2-14 ∷ []) (Bx1-24 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ14 ∷ []) (refl) ▸
       at 0 2 (CZ24 ∷ Sw12 ∷ []) (sym (wl0089 c4)) ▸
       at 0 1 (Bx1-24 ∷ []) (refl) ▸ done


-- nat 1 BOX(1;204): 8 steps
lem-nat-1-BOX⟨1·204⟩ : WsL → ⟪ (Sw12 ∷ Bx1-204 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-104 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·204⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx1-204 ∷ []) (Bx2-104 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff102 ∷ Bx2-14 ∷ Toff102 ∷ CCZ012 ∷ Bx2-14 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw12 ∷ []) (sym (wl0037 c4)) ▸
       at 1 2 (Toff201 ∷ Sw12 ∷ []) (wl0047 c4) ▸
       at 2 2 (Bx1-24 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·14⟩ c4) ▸
       at 3 2 (Toff201 ∷ Sw12 ∷ []) (wl0047 c4) ▸
       at 4 2 (CCZ012 ∷ Sw12 ∷ []) (sym (wl0037 c4)) ▸
       at 5 2 (Bx1-24 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·14⟩ c4) ▸
       at 0 6 (Bx2-104 ∷ []) (refl) ▸ done


-- nat 1 BOX(2;1304): 8 steps
lem-nat-1-BOX⟨2·1304⟩ : WsL → ⟪ (Sw12 ∷ Bx2-1304 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2304 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·1304⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx2-1304 ∷ []) (Bx1-2304 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff213 ∷ Bx1-204 ∷ Toff213 ∷ CCZ123 ∷ Bx1-204 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw12 ∷ []) (sym (wl0111 c4)) ▸
       at 1 2 (Toff123 ∷ Sw12 ∷ []) (wl0112 c4) ▸
       at 2 2 (Bx2-104 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·204⟩ c4) ▸
       at 3 2 (Toff123 ∷ Sw12 ∷ []) (wl0112 c4) ▸
       at 4 2 (CCZ123 ∷ Sw12 ∷ []) (sym (wl0111 c4)) ▸
       at 5 2 (Bx2-104 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·204⟩ c4) ▸
       at 0 6 (Bx1-2304 ∷ []) (refl) ▸ done


-- nat 1 BOX(2;104): 8 steps
lem-nat-1-BOX⟨2·104⟩ : WsL → ⟪ (Sw12 ∷ Bx2-104 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-204 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·104⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx2-104 ∷ []) (Bx1-204 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff201 ∷ Bx1-24 ∷ Toff201 ∷ CCZ012 ∷ Bx1-24 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw12 ∷ []) (sym (wl0037 c4)) ▸
       at 1 2 (Toff102 ∷ Sw12 ∷ []) (wl0044 c4) ▸
       at 2 2 (Bx2-14 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·24⟩ c4) ▸
       at 3 2 (Toff102 ∷ Sw12 ∷ []) (wl0044 c4) ▸
       at 4 2 (CCZ012 ∷ Sw12 ∷ []) (sym (wl0037 c4)) ▸
       at 5 2 (Bx2-14 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·24⟩ c4) ▸
       at 0 6 (Bx1-204 ∷ []) (refl) ▸ done


-- nat 1 BOX(1;2304): 8 steps
lem-nat-1-BOX⟨1·2304⟩ : WsL → ⟪ (Sw12 ∷ Bx1-2304 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1304 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·2304⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx1-2304 ∷ []) (Bx2-1304 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff123 ∷ Bx2-104 ∷ Toff123 ∷ CCZ123 ∷ Bx2-104 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw12 ∷ []) (sym (wl0111 c4)) ▸
       at 1 2 (Toff213 ∷ Sw12 ∷ []) (wl0146 c4) ▸
       at 2 2 (Bx1-204 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·104⟩ c4) ▸
       at 3 2 (Toff213 ∷ Sw12 ∷ []) (wl0146 c4) ▸
       at 4 2 (CCZ123 ∷ Sw12 ∷ []) (sym (wl0111 c4)) ▸
       at 5 2 (Bx1-204 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·104⟩ c4) ▸
       at 0 6 (Bx2-1304 ∷ []) (refl) ▸ done


-- nat 1 BOX(0;31): 3 steps
lem-nat-1-BOX⟨0·31⟩ : WsL → ⟪ (Sw12 ∷ Bx0-31 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-32 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·31⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-31 ∷ []) (Bx0-32 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ13 ∷ []) (refl) ▸
       at 0 2 (CZ23 ∷ Sw12 ∷ []) (sym (wl0029 c4)) ▸
       at 0 1 (Bx0-32 ∷ []) (refl) ▸ done


-- nat 1 BOX(3;041): 8 steps
lem-nat-1-BOX⟨3·041⟩ : WsL → ⟪ (Sw12 ∷ Bx3-041 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-042 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·041⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-041 ∷ []) (Bx3-042 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff304 ∷ Bx0-31 ∷ Toff304 ∷ CCZ034 ∷ Bx0-31 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 1 2 (Toff304 ∷ Sw12 ∷ []) (lem-nat-1-TOFF304 c4) ▸
       at 2 2 (Bx0-32 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·31⟩ c4) ▸
       at 3 2 (Toff304 ∷ Sw12 ∷ []) (lem-nat-1-TOFF304 c4) ▸
       at 4 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 5 2 (Bx0-32 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·31⟩ c4) ▸
       at 0 6 (Bx3-042 ∷ []) (refl) ▸ done


-- nat 1 BOX(0;3241): 8 steps
lem-nat-1-BOX⟨0·3241⟩ : WsL → ⟪ (Sw12 ∷ Bx0-3241 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3142 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·3241⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-3241 ∷ []) (Bx0-3142 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff023 ∷ Bx3-041 ∷ Toff023 ∷ CCZ023 ∷ Bx3-041 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 1 2 (Toff013 ∷ Sw12 ∷ []) (lem-nat-1-TOFF023 c4) ▸
       at 2 2 (Bx3-042 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·041⟩ c4) ▸
       at 3 2 (Toff013 ∷ Sw12 ∷ []) (lem-nat-1-TOFF023 c4) ▸
       at 4 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 5 2 (Bx3-042 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·041⟩ c4) ▸
       at 0 6 (Bx0-3142 ∷ []) (refl) ▸ done


-- nat 1 BOX(0;32): 3 steps
lem-nat-1-BOX⟨0·32⟩ : WsL → ⟪ (Sw12 ∷ Bx0-32 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-31 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·32⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-32 ∷ []) (Bx0-31 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ23 ∷ []) (refl) ▸
       at 0 2 (CZ13 ∷ Sw12 ∷ []) (sym (wl0026 c4)) ▸
       at 0 1 (Bx0-31 ∷ []) (refl) ▸ done

