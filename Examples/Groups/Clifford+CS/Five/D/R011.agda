{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.R011 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (WsL ; wl0001 ; wl0002 ; wl0006 ; wl0007 ; wl0008 ; wl0009 ; wl0010 ; wl0014 ; wl0017 ; wl0018 ; wl0020 ; wl0023 ; wl0024 ; wl0025 ; wl0026 ; wl0037 ; wl0038 ; wl0043 ; wl0044 ; wl0046 ; wl0047 ; wl0056 ; wl0062 ; wl0063 ; wl0064 ; wl0065 ; wl0066 ; wl0078 ; wl0088 ; wl0090 ; wl0095 ; wl0096 ; wl0097 ; wl0098 ; wl0100 ; wl0101 ; wl0102 ; wl0107 ; wl0111 ; wl0112 ; wl0113 ; wl0114 ; wl0119 ; wl0120 ; wl0125 ; wl0126 ; wl0127 ; wl0128 ; wl0129 ; wl0136 ; wl0140 ; wl0144 ; wl0146 ; wl0147 ; wl0148 ; wl0149 ; wl0150 ; wl0151)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-nat-1-CCZ023 ; lem-nat-1-CCZ024 ; lem-nat-1-CCZ034 ; lem-nat-1-TOFF014 ; lem-nat-1-TOFF024 ; lem-nat-2-CCZ012 ; lem-nat-2-CCZ013 ; lem-nat-2-CCZ024 ; lem-nat-2-CCZ034 ; lem-nat-2-TOFF012 ; lem-nat-2-TOFF013 ; lem-nat-2-TOFF024 ; lem-nat-2-TOFF034 ; lem-nat-2-TOFF102 ; lem-nat-2-TOFF103 ; lem-nat-3-CCZ014 ; lem-nat-3-CCZ024 ; lem-nat-3-TOFF013 ; lem-nat-3-TOFF014 ; lem-nat-3-TOFF104)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-0-CCZ024 ; lem-nat-0-CCZ124 ; lem-nat-1-CCZ013 ; lem-nat-1-CCZ014 ; lem-nat-1-TOFF301 ; lem-nat-1-TOFF302 ; lem-nat-2-CCZ124 ; lem-nat-2-CCZ134 ; lem-nat-3-CCZ013 ; lem-nat-3-CCZ023 ; lem-nat-3-CZ14 ; lem-nat-3-TOFF203)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-0-CCZ014 ; lem-nat-0-TOFF014 ; lem-nat-0-TOFF104 ; lem-nat-1-TOFF104 ; lem-nat-1-TOFF204)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-1-TOFF013 ; lem-nat-2-TOFF104)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-0-TOFF024 ; lem-nat-1-TOFF023 ; lem-nat-2-CCZ014 ; lem-nat-2-CZ02 ; lem-nat-2-CZ03 ; lem-nat-2-TOFF214 ; lem-nat-3-TOFF103)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-0-BOXd⟨1·0423⟩ ; lem-nat-1-BOXd⟨2·03⟩ ; lem-nat-1-BOXd⟨2·0413⟩ ; lem-nat-1-CS01 ; lem-nat-1-CS02 ; lem-nat-1-CZ01 ; lem-nat-2-TOFF314 ; lem-nat-3-BOXd⟨0·1423⟩)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-0-BOX⟨0·12⟩ ; lem-nat-0-BOX⟨2·03⟩ ; lem-nat-0-BOX⟨2·13⟩ ; lem-nat-0-SBOX⟨0·1·3·2⟩ ; lem-nat-0-SBOX⟨1·0·3·2⟩ ; lem-nat-0-SBOXd⟨0·1·3·2⟩ ; lem-nat-0-SBOXd⟨1·0·3·2⟩ ; lem-nat-1-BOX⟨3·02⟩ ; lem-nat-1-CSd02 ; lem-nat-1-SBOX⟨1·0·3·2⟩ ; lem-nat-1-SBOX⟨2·0·3·1⟩ ; lem-nat-1-SBOXd⟨1·0·3·2⟩ ; lem-nat-1-SBOXd⟨2·0·3·1⟩ ; lem-nat-2-BOX⟨3·01⟩ ; lem-nat-2-CS02 ; lem-nat-2-CSd02 ; lem-nat-2-SBOX⟨1·0·2·3⟩ ; lem-nat-2-SBOXd⟨1·0·2·3⟩ ; lem-nat-2-TOFF014 ; lem-nat-2-TOFF124 ; lem-nat-3-SBOX⟨0·1·3·2⟩ ; lem-nat-3-SBOX⟨0·1·4·2⟩ ; lem-nat-3-SBOX⟨1·0·2·4⟩ ; lem-nat-3-SBOXd⟨0·1·3·2⟩ ; lem-nat-3-SBOXd⟨0·1·4·2⟩ ; lem-nat-3-SBOXd⟨1·0·2·4⟩)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-nat-0-BOX⟨1·02⟩ ; lem-nat-1-BOX⟨1·02⟩ ; lem-nat-1-BOX⟨2·01⟩ ; lem-nat-1-CSd01 ; lem-nat-1-TOFF034 ; lem-nat-3-TOFF024)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-1-BOX⟨1·34⟩ ; lem-nat-1-BOX⟨2·34⟩ ; lem-nat-2-CS03 ; lem-nat-2-CSd03)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-nat-0-TOFF124 ; lem-nat-1-BOX⟨2·3140⟩ ; lem-nat-1-SBOX⟨2·0·3·4⟩ ; lem-nat-1-SBOX⟨2·3·0·4⟩ ; lem-nat-1-SBOXd⟨2·0·3·4⟩ ; lem-nat-2-BOX⟨1·03⟩ ; lem-nat-2-SBOX⟨1·0·3·4⟩ ; lem-nat-2-SBOXd⟨1·0·3·4⟩)
-- nat 1 SBOXd(2;3;0;4): 3 steps
lem-nat-1-SBOXd⟨2·3·0·4⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻2-3-0-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-3-0-4 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨2·3·0·4⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻2-3-0-4 ∷ []) (Sb⁻1-3-0-4 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS03⁻ ∷ []) (refl) ▸
       at 0 2 (CS03⁻ ∷ Sw12 ∷ []) (sym (wl0023 c4)) ▸
       at 0 1 (Sb⁻1-3-0-4 ∷ []) (refl) ▸ done


-- nat 1 SBOX(2;3;14;0): 7 steps
lem-nat-1-SBOX⟨2·3·14·0⟩ : WsL → ⟪ (Sw12 ∷ Sb2-3-14-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-3-24-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨2·3·14·0⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb2-3-14-0 ∷ []) (Sb1-3-24-0 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx2-3140 ∷ Toff014 ∷ Sb2-3-0-4 ∷ Toff014 ∷ Sb⁻2-3-0-4 ∷ []) (refl) ▸
       at 0 2 (Bx1-3240 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·3140⟩ c4) ▸
       at 1 2 (Toff024 ∷ Sw12 ∷ []) (lem-nat-1-TOFF014 c4) ▸
       at 2 2 (Sb1-3-0-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·3·0·4⟩ c4) ▸
       at 3 2 (Toff024 ∷ Sw12 ∷ []) (lem-nat-1-TOFF014 c4) ▸
       at 4 2 (Sb⁻1-3-0-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·3·0·4⟩ c4) ▸
       at 0 5 (Sb1-3-24-0 ∷ []) (refl) ▸ done


-- nat 2 BOX(1;20): 3 steps
lem-nat-2-BOX⟨1·20⟩ : WsL → ⟪ (Sw23 ∷ Bx1-20 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-30 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·20⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx1-20 ∷ []) (Bx1-30 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ02 ∷ []) (refl) ▸
       at 0 2 (CZ03 ∷ Sw23 ∷ []) (lem-nat-2-CZ02 c4) ▸
       at 0 1 (Bx1-30 ∷ []) (refl) ▸ done


-- nat 2 BOX(2;140): 8 steps
lem-nat-2-BOX⟨2·140⟩ : WsL → ⟪ (Sw23 ∷ Bx2-140 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-140 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·140⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx2-140 ∷ []) (Bx3-140 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff214 ∷ Bx1-20 ∷ Toff214 ∷ CCZ124 ∷ Bx1-20 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 1 2 (Toff314 ∷ Sw23 ∷ []) (lem-nat-2-TOFF214 c4) ▸
       at 2 2 (Bx1-30 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·20⟩ c4) ▸
       at 3 2 (Toff314 ∷ Sw23 ∷ []) (lem-nat-2-TOFF214 c4) ▸
       at 4 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 5 2 (Bx1-30 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·20⟩ c4) ▸
       at 0 6 (Bx3-140 ∷ []) (refl) ▸ done


-- nat 2 BOX(1;2340): 8 steps
lem-nat-2-BOX⟨1·2340⟩ : WsL → ⟪ (Sw23 ∷ Bx1-2340 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3240 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·2340⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx1-2340 ∷ []) (Bx1-3240 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff123 ∷ Bx2-140 ∷ Toff123 ∷ CCZ123 ∷ Bx2-140 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw23 ∷ []) (sym (wl0113 c4)) ▸
       at 1 2 (Toff123 ∷ Sw23 ∷ []) (wl0114 c4) ▸
       at 2 2 (Bx3-140 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·140⟩ c4) ▸
       at 3 2 (Toff123 ∷ Sw23 ∷ []) (wl0114 c4) ▸
       at 4 2 (CCZ123 ∷ Sw23 ∷ []) (sym (wl0113 c4)) ▸
       at 5 2 (Bx3-140 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·140⟩ c4) ▸
       at 0 6 (Bx1-3240 ∷ []) (refl) ▸ done


-- nat 2 SBOX(1;2;0;4): 3 steps
lem-nat-2-SBOX⟨1·2·0·4⟩ : WsL → ⟪ (Sw23 ∷ Sb1-2-0-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-3-0-4 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨1·2·0·4⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb1-2-0-4 ∷ []) (Sb1-3-0-4 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS02 ∷ []) (refl) ▸
       at 0 2 (CS03 ∷ Sw23 ∷ []) (lem-nat-2-CS02 c4) ▸
       at 0 1 (Sb1-3-0-4 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(1;2;0;4): 3 steps
lem-nat-2-SBOXd⟨1·2·0·4⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻1-2-0-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-3-0-4 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨1·2·0·4⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻1-2-0-4 ∷ []) (Sb⁻1-3-0-4 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS02⁻ ∷ []) (refl) ▸
       at 0 2 (CS03⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd02 c4) ▸
       at 0 1 (Sb⁻1-3-0-4 ∷ []) (refl) ▸ done


-- nat 2 SBOX(1;2;34;0): 7 steps
lem-nat-2-SBOX⟨1·2·34·0⟩ : WsL → ⟪ (Sw23 ∷ Sb1-2-34-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-3-24-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨1·2·34·0⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb1-2-34-0 ∷ []) (Sb1-3-24-0 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx1-2340 ∷ Toff034 ∷ Sb1-2-0-4 ∷ Toff034 ∷ Sb⁻1-2-0-4 ∷ []) (refl) ▸
       at 0 2 (Bx1-3240 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·2340⟩ c4) ▸
       at 1 2 (Toff024 ∷ Sw23 ∷ []) (lem-nat-2-TOFF034 c4) ▸
       at 2 2 (Sb1-3-0-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·2·0·4⟩ c4) ▸
       at 3 2 (Toff024 ∷ Sw23 ∷ []) (lem-nat-2-TOFF034 c4) ▸
       at 4 2 (Sb⁻1-3-0-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·2·0·4⟩ c4) ▸
       at 0 5 (Sb1-3-24-0 ∷ []) (refl) ▸ done


-- nat 2 BOX(1;30): 3 steps
lem-nat-2-BOX⟨1·30⟩ : WsL → ⟪ (Sw23 ∷ Bx1-30 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-20 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·30⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx1-30 ∷ []) (Bx1-20 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ03 ∷ []) (refl) ▸
       at 0 2 (CZ02 ∷ Sw23 ∷ []) (lem-nat-2-CZ03 c4) ▸
       at 0 1 (Bx1-20 ∷ []) (refl) ▸ done


-- nat 2 BOX(3;140): 8 steps
lem-nat-2-BOX⟨3·140⟩ : WsL → ⟪ (Sw23 ∷ Bx3-140 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-140 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·140⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx3-140 ∷ []) (Bx2-140 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff314 ∷ Bx1-30 ∷ Toff314 ∷ CCZ134 ∷ Bx1-30 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 1 2 (Toff214 ∷ Sw23 ∷ []) (lem-nat-2-TOFF314 c4) ▸
       at 2 2 (Bx1-20 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·30⟩ c4) ▸
       at 3 2 (Toff214 ∷ Sw23 ∷ []) (lem-nat-2-TOFF314 c4) ▸
       at 4 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 5 2 (Bx1-20 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·30⟩ c4) ▸
       at 0 6 (Bx2-140 ∷ []) (refl) ▸ done


-- nat 2 BOX(1;3240): 8 steps
lem-nat-2-BOX⟨1·3240⟩ : WsL → ⟪ (Sw23 ∷ Bx1-3240 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2340 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·3240⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx1-3240 ∷ []) (Bx1-2340 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff123 ∷ Bx3-140 ∷ Toff123 ∷ CCZ123 ∷ Bx3-140 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw23 ∷ []) (sym (wl0113 c4)) ▸
       at 1 2 (Toff123 ∷ Sw23 ∷ []) (wl0114 c4) ▸
       at 2 2 (Bx2-140 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·140⟩ c4) ▸
       at 3 2 (Toff123 ∷ Sw23 ∷ []) (wl0114 c4) ▸
       at 4 2 (CCZ123 ∷ Sw23 ∷ []) (sym (wl0113 c4)) ▸
       at 5 2 (Bx2-140 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·140⟩ c4) ▸
       at 0 6 (Bx1-2340 ∷ []) (refl) ▸ done


-- nat 2 SBOX(1;3;0;4): 3 steps
lem-nat-2-SBOX⟨1·3·0·4⟩ : WsL → ⟪ (Sw23 ∷ Sb1-3-0-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-0-4 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨1·3·0·4⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb1-3-0-4 ∷ []) (Sb1-2-0-4 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS03 ∷ []) (refl) ▸
       at 0 2 (CS02 ∷ Sw23 ∷ []) (lem-nat-2-CS03 c4) ▸
       at 0 1 (Sb1-2-0-4 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(1;3;0;4): 3 steps
lem-nat-2-SBOXd⟨1·3·0·4⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻1-3-0-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-2-0-4 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨1·3·0·4⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻1-3-0-4 ∷ []) (Sb⁻1-2-0-4 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS03⁻ ∷ []) (refl) ▸
       at 0 2 (CS02⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd03 c4) ▸
       at 0 1 (Sb⁻1-2-0-4 ∷ []) (refl) ▸ done


-- nat 2 SBOX(1;3;24;0): 7 steps
lem-nat-2-SBOX⟨1·3·24·0⟩ : WsL → ⟪ (Sw23 ∷ Sb1-3-24-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-34-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨1·3·24·0⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb1-3-24-0 ∷ []) (Sb1-2-34-0 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx1-3240 ∷ Toff024 ∷ Sb1-3-0-4 ∷ Toff024 ∷ Sb⁻1-3-0-4 ∷ []) (refl) ▸
       at 0 2 (Bx1-2340 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·3240⟩ c4) ▸
       at 1 2 (Toff034 ∷ Sw23 ∷ []) (lem-nat-2-TOFF024 c4) ▸
       at 2 2 (Sb1-2-0-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·3·0·4⟩ c4) ▸
       at 3 2 (Toff034 ∷ Sw23 ∷ []) (lem-nat-2-TOFF024 c4) ▸
       at 4 2 (Sb⁻1-2-0-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·3·0·4⟩ c4) ▸
       at 0 5 (Sb1-2-34-0 ∷ []) (refl) ▸ done


-- nat 3 BOX(1;042): 8 steps
lem-nat-3-BOX⟨1·042⟩ : WsL → ⟪ (Sw34 ∷ Bx1-042 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-032 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨1·042⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx1-042 ∷ []) (Bx1-032 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff104 ∷ Bx0-12 ∷ Toff104 ∷ CCZ014 ∷ Bx0-12 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4) ▸
       at 1 2 (Toff103 ∷ Sw34 ∷ []) (lem-nat-3-TOFF104 c4) ▸
       at 2 2 (Bx0-12 ∷ Sw34 ∷ []) (sym (c₃ (CZ ↑) (Swap))) ▸
       at 3 2 (Toff103 ∷ Sw34 ∷ []) (lem-nat-3-TOFF104 c4) ▸
       at 4 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4) ▸
       at 5 2 (Bx0-12 ∷ Sw34 ∷ []) (sym (c₃ (CZ ↑) (Swap))) ▸
       at 0 6 (Bx1-032 ∷ []) (refl) ▸ done


-- nat 3 BOX(0;1342): 8 steps
lem-nat-3-BOX⟨0·1342⟩ : WsL → ⟪ (Sw34 ∷ Bx0-1342 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1432 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·1342⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx0-1342 ∷ []) (Bx0-1432 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff013 ∷ Bx1-042 ∷ Toff013 ∷ CCZ013 ∷ Bx1-042 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4) ▸
       at 1 2 (Toff014 ∷ Sw34 ∷ []) (lem-nat-3-TOFF013 c4) ▸
       at 2 2 (Bx1-032 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·042⟩ c4) ▸
       at 3 2 (Toff014 ∷ Sw34 ∷ []) (lem-nat-3-TOFF013 c4) ▸
       at 4 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4) ▸
       at 5 2 (Bx1-032 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·042⟩ c4) ▸
       at 0 6 (Bx0-1432 ∷ []) (refl) ▸ done


-- nat 0 BOX(1;032): 8 steps
lem-nat-0-BOX⟨1·032⟩ : WsL → ⟪ (Sw01 ∷ Bx1-032 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-132 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·032⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-032 ∷ []) (Bx0-132 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff103 ∷ Bx0-12 ∷ Toff103 ∷ CCZ013 ∷ Bx0-12 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw01 ∷ []) (sym (wl0100 c4)) ▸
       at 1 2 (Toff013 ∷ Sw01 ∷ []) (wl0102 c4) ▸
       at 2 2 (Bx1-02 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·12⟩ c4) ▸
       at 3 2 (Toff013 ∷ Sw01 ∷ []) (wl0102 c4) ▸
       at 4 2 (CCZ013 ∷ Sw01 ∷ []) (sym (wl0100 c4)) ▸
       at 5 2 (Bx1-02 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·12⟩ c4) ▸
       at 0 6 (Bx0-132 ∷ []) (refl) ▸ done


-- nat 0 BOX(0;1432): 8 steps
lem-nat-0-BOX⟨0·1432⟩ : WsL → ⟪ (Sw01 ∷ Bx0-1432 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0432 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·1432⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-1432 ∷ []) (Bx1-0432 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff014 ∷ Bx1-032 ∷ Toff014 ∷ CCZ014 ∷ Bx1-032 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 1 2 (Toff104 ∷ Sw01 ∷ []) (lem-nat-0-TOFF014 c4) ▸
       at 2 2 (Bx0-132 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·032⟩ c4) ▸
       at 3 2 (Toff104 ∷ Sw01 ∷ []) (lem-nat-0-TOFF014 c4) ▸
       at 4 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 5 2 (Bx0-132 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·032⟩ c4) ▸
       at 0 6 (Bx1-0432 ∷ []) (refl) ▸ done


-- nat 1 BOX(0;132): 8 steps
lem-nat-1-BOX⟨0·132⟩ : WsL → ⟪ (Sw12 ∷ Bx0-132 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-231 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·132⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-132 ∷ []) (Bx0-231 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff013 ∷ Bx1-02 ∷ Toff013 ∷ CCZ013 ∷ Bx1-02 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 1 2 (Toff023 ∷ Sw12 ∷ []) (lem-nat-1-TOFF013 c4) ▸
       at 2 2 (Bx2-01 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·02⟩ c4) ▸
       at 3 2 (Toff023 ∷ Sw12 ∷ []) (lem-nat-1-TOFF013 c4) ▸
       at 4 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 5 2 (Bx2-01 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·02⟩ c4) ▸
       at 0 6 (Bx0-231 ∷ []) (refl) ▸ done


-- nat 1 BOX(1;0432): 8 steps
lem-nat-1-BOX⟨1·0432⟩ : WsL → ⟪ (Sw12 ∷ Bx1-0432 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0431 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·0432⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx1-0432 ∷ []) (Bx2-0431 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff104 ∷ Bx0-132 ∷ Toff104 ∷ CCZ014 ∷ Bx0-132 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 1 2 (Toff204 ∷ Sw12 ∷ []) (lem-nat-1-TOFF104 c4) ▸
       at 2 2 (Bx0-231 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·132⟩ c4) ▸
       at 3 2 (Toff204 ∷ Sw12 ∷ []) (lem-nat-1-TOFF104 c4) ▸
       at 4 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 5 2 (Bx0-231 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·132⟩ c4) ▸
       at 0 6 (Bx2-0431 ∷ []) (refl) ▸ done


-- nat 0 BOX(0;132): 8 steps
lem-nat-0-BOX⟨0·132⟩ : WsL → ⟪ (Sw01 ∷ Bx0-132 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-032 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·132⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-132 ∷ []) (Bx1-032 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff013 ∷ Bx1-02 ∷ Toff013 ∷ CCZ013 ∷ Bx1-02 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw01 ∷ []) (sym (wl0100 c4)) ▸
       at 1 2 (Toff103 ∷ Sw01 ∷ []) (wl0101 c4) ▸
       at 2 2 (Bx0-12 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·02⟩ c4) ▸
       at 3 2 (Toff103 ∷ Sw01 ∷ []) (wl0101 c4) ▸
       at 4 2 (CCZ013 ∷ Sw01 ∷ []) (sym (wl0100 c4)) ▸
       at 5 2 (Bx0-12 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·02⟩ c4) ▸
       at 0 6 (Bx1-032 ∷ []) (refl) ▸ done


-- nat 0 BOX(1;0432): 8 steps
lem-nat-0-BOX⟨1·0432⟩ : WsL → ⟪ (Sw01 ∷ Bx1-0432 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1432 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·0432⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-0432 ∷ []) (Bx0-1432 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff104 ∷ Bx0-132 ∷ Toff104 ∷ CCZ014 ∷ Bx0-132 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 1 2 (Toff014 ∷ Sw01 ∷ []) (lem-nat-0-TOFF104 c4) ▸
       at 2 2 (Bx1-032 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·132⟩ c4) ▸
       at 3 2 (Toff014 ∷ Sw01 ∷ []) (lem-nat-0-TOFF104 c4) ▸
       at 4 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 5 2 (Bx1-032 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·132⟩ c4) ▸
       at 0 6 (Bx0-1432 ∷ []) (refl) ▸ done


-- nat 1 BOX(0;231): 8 steps
lem-nat-1-BOX⟨0·231⟩ : WsL → ⟪ (Sw12 ∷ Bx0-231 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-132 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·231⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-231 ∷ []) (Bx0-132 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff023 ∷ Bx2-01 ∷ Toff023 ∷ CCZ023 ∷ Bx2-01 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 1 2 (Toff013 ∷ Sw12 ∷ []) (lem-nat-1-TOFF023 c4) ▸
       at 2 2 (Bx1-02 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·01⟩ c4) ▸
       at 3 2 (Toff013 ∷ Sw12 ∷ []) (lem-nat-1-TOFF023 c4) ▸
       at 4 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 5 2 (Bx1-02 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·01⟩ c4) ▸
       at 0 6 (Bx0-132 ∷ []) (refl) ▸ done


-- nat 1 BOX(2;0431): 8 steps
lem-nat-1-BOX⟨2·0431⟩ : WsL → ⟪ (Sw12 ∷ Bx2-0431 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0432 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·0431⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx2-0431 ∷ []) (Bx1-0432 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff204 ∷ Bx0-231 ∷ Toff204 ∷ CCZ024 ∷ Bx0-231 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 1 2 (Toff104 ∷ Sw12 ∷ []) (lem-nat-1-TOFF204 c4) ▸
       at 2 2 (Bx0-132 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·231⟩ c4) ▸
       at 3 2 (Toff104 ∷ Sw12 ∷ []) (lem-nat-1-TOFF204 c4) ▸
       at 4 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 5 2 (Bx0-132 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·231⟩ c4) ▸
       at 0 6 (Bx1-0432 ∷ []) (refl) ▸ done


-- comm CX41 TOFF203: 7 steps
lem-comm-CX41-TOFF203 : WsL → ⟪ (CX41 ∷ Toff203 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ CX41 ∷ []) ⟫ʷ
lem-comm-CX41-TOFF203 c4 = run b0
  where
  b0 : Chain (CX41 ∷ Toff203 ∷ []) (Toff203 ∷ CX41 ∷ [])
  b0 = at 1 1 (Sw12 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw12 ∷ CX42 ∷ []) (wl0125 c4) ▸
       at 1 2 (Sw23 ∷ CX43 ∷ []) (wl0147 c4) ▸
       at 2 2 (Toff102 ∷ CX43 ∷ []) (sym (c₃ (K ↑ • CCZ • K ↑ • iI) (CX₁₀))) ▸
       at 3 2 (Sw23 ∷ CX42 ∷ []) (wl0148 c4) ▸
       at 4 2 (Sw12 ∷ CX41 ∷ []) (wl0149 c4) ▸
       at 0 5 (Toff203 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp CSd13 at 2: 4 steps
lem-resp-CSd13-at-2 : WsL → ⟪ (CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CS23⁻ ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CSd13-at-2 c4 = run b0
  where
  b0 : Chain (CS13⁻ ∷ []) (Sw12 ∷ Sw01 ∷ CS23⁻ ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 0 2 (Sw12 ∷ CS23⁻ ∷ []) (wl0043 c4) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 c4)) ▸
       at 1 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (c₂ (Swap) (CS • CS • CS))) ▸ done


-- resp CX04 at 2: 12 steps
lem-resp-CX04-at-2 : WsL → ⟪ (CX04 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CX14 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CX04-at-2 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CX04 ∷ []) (Sw12 ∷ Sw34 ∷ CX03 ∷ Sw34 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 0 1 (Sw34 ∷ CX03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 1 2 (Sw12 ∷ CX03 ∷ []) (wl0014 c4) ▸
       at 0 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 1 3 (CX04 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 c4)) ▸
       at 1 1 (Sw34 ∷ CX03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw12 ∷ Sw34 ∷ CX03 ∷ Sw34 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw01 ∷ CX14 ∷ Sw01 ∷ Sw12 ∷ [])
  b1 = at 3 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 2 2 (Sw01 ∷ CX13 ∷ []) (wl0020 c4) ▸
       at 1 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 2 3 (CX14 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 1 BOX(1;23): 3 steps
lem-nat-1-BOX⟨1·23⟩ : WsL → ⟪ (Sw12 ∷ Bx1-23 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-13 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·23⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx1-23 ∷ []) (Bx2-13 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ23 ∷ []) (refl) ▸
       at 0 2 (CZ13 ∷ Sw12 ∷ []) (sym (wl0026 c4)) ▸
       at 0 1 (Bx2-13 ∷ []) (refl) ▸ done


-- nat 1 BOX(2;143): 8 steps
lem-nat-1-BOX⟨2·143⟩ : WsL → ⟪ (Sw12 ∷ Bx2-143 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-243 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·143⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx2-143 ∷ []) (Bx1-243 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff214 ∷ Bx1-23 ∷ Toff214 ∷ CCZ124 ∷ Bx1-23 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw12 ∷ []) (sym (wl0078 c4)) ▸
       at 1 2 (Toff124 ∷ Sw12 ∷ []) (wl0126 c4) ▸
       at 2 2 (Bx2-13 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·23⟩ c4) ▸
       at 3 2 (Toff124 ∷ Sw12 ∷ []) (wl0126 c4) ▸
       at 4 2 (CCZ124 ∷ Sw12 ∷ []) (sym (wl0078 c4)) ▸
       at 5 2 (Bx2-13 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·23⟩ c4) ▸
       at 0 6 (Bx1-243 ∷ []) (refl) ▸ done


-- nat 1 BOX(1;2043): 8 steps
lem-nat-1-BOX⟨1·2043⟩ : WsL → ⟪ (Sw12 ∷ Bx1-2043 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1043 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·2043⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx1-2043 ∷ []) (Bx2-1043 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff102 ∷ Bx2-143 ∷ Toff102 ∷ CCZ012 ∷ Bx2-143 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw12 ∷ []) (sym (wl0037 c4)) ▸
       at 1 2 (Toff201 ∷ Sw12 ∷ []) (wl0047 c4) ▸
       at 2 2 (Bx1-243 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·143⟩ c4) ▸
       at 3 2 (Toff201 ∷ Sw12 ∷ []) (wl0047 c4) ▸
       at 4 2 (CCZ012 ∷ Sw12 ∷ []) (sym (wl0037 c4)) ▸
       at 5 2 (Bx1-243 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·143⟩ c4) ▸
       at 0 6 (Bx2-1043 ∷ []) (refl) ▸ done


-- nat 0 BOX(1;243): 8 steps
lem-nat-0-BOX⟨1·243⟩ : WsL → ⟪ (Sw01 ∷ Bx1-243 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-243 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·243⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-243 ∷ []) (Bx0-243 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff124 ∷ Bx2-13 ∷ Toff124 ∷ CCZ124 ∷ Bx2-13 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 1 2 (Toff024 ∷ Sw01 ∷ []) (lem-nat-0-TOFF124 c4) ▸
       at 2 2 (Bx2-03 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·13⟩ c4) ▸
       at 3 2 (Toff024 ∷ Sw01 ∷ []) (lem-nat-0-TOFF124 c4) ▸
       at 4 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 5 2 (Bx2-03 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·13⟩ c4) ▸
       at 0 6 (Bx0-243 ∷ []) (refl) ▸ done


-- nat 0 BOX(2;1043): 8 steps
lem-nat-0-BOX⟨2·1043⟩ : WsL → ⟪ (Sw01 ∷ Bx2-1043 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0143 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·1043⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx2-1043 ∷ []) (Bx2-0143 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff201 ∷ Bx1-243 ∷ Toff201 ∷ CCZ012 ∷ Bx1-243 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw01 ∷ []) (sym (wl0096 c4)) ▸
       at 1 2 (Toff201 ∷ Sw01 ∷ []) (wl0107 c4) ▸
       at 2 2 (Bx0-243 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·243⟩ c4) ▸
       at 3 2 (Toff201 ∷ Sw01 ∷ []) (wl0107 c4) ▸
       at 4 2 (CCZ012 ∷ Sw01 ∷ []) (sym (wl0096 c4)) ▸
       at 5 2 (Bx0-243 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·243⟩ c4) ▸
       at 0 6 (Bx2-0143 ∷ []) (refl) ▸ done


-- nat 0 BOX(0;243): 8 steps
lem-nat-0-BOX⟨0·243⟩ : WsL → ⟪ (Sw01 ∷ Bx0-243 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-243 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·243⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-243 ∷ []) (Bx1-243 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff024 ∷ Bx2-03 ∷ Toff024 ∷ CCZ024 ∷ Bx2-03 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 1 2 (Toff124 ∷ Sw01 ∷ []) (lem-nat-0-TOFF024 c4) ▸
       at 2 2 (Bx2-13 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·03⟩ c4) ▸
       at 3 2 (Toff124 ∷ Sw01 ∷ []) (lem-nat-0-TOFF024 c4) ▸
       at 4 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 5 2 (Bx2-13 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·03⟩ c4) ▸
       at 0 6 (Bx1-243 ∷ []) (refl) ▸ done


-- nat 0 BOX(2;0143): 8 steps
lem-nat-0-BOX⟨2·0143⟩ : WsL → ⟪ (Sw01 ∷ Bx2-0143 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1043 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·0143⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx2-0143 ∷ []) (Bx2-1043 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff201 ∷ Bx0-243 ∷ Toff201 ∷ CCZ012 ∷ Bx0-243 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw01 ∷ []) (sym (wl0096 c4)) ▸
       at 1 2 (Toff201 ∷ Sw01 ∷ []) (wl0107 c4) ▸
       at 2 2 (Bx1-243 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·243⟩ c4) ▸
       at 3 2 (Toff201 ∷ Sw01 ∷ []) (wl0107 c4) ▸
       at 4 2 (CCZ012 ∷ Sw01 ∷ []) (sym (wl0096 c4)) ▸
       at 5 2 (Bx1-243 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·243⟩ c4) ▸
       at 0 6 (Bx2-1043 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(2;0;41;3): 7 steps
lem-nat-1-SBOXd⟨2·0·41·3⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-42-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨2·0·41·3⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻2-0-41-3 ∷ []) (Sb⁻1-0-42-3 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) (refl) ▸
       at 0 2 (Sb1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·3·1⟩ c4) ▸
       at 1 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 c4) ▸
       at 2 2 (Sb⁻1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·3·1⟩ c4) ▸
       at 3 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 c4) ▸
       at 4 2 (Bx⁻1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨2·0413⟩ c4) ▸
       at 0 5 (Sb⁻1-0-42-3 ∷ []) (refl) ▸ done


-- nat 2 SBOX(1;0;3;2): 3 steps
lem-nat-2-SBOX⟨1·0·3·2⟩ : WsL → ⟪ (Sw23 ∷ Sb1-0-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-2-3 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨1·0·3·2⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb1-0-3-2 ∷ []) (Sb1-0-2-3 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS03 ∷ []) (refl) ▸
       at 0 2 (CS02 ∷ Sw23 ∷ []) (lem-nat-2-CS03 c4) ▸
       at 0 1 (Sb1-0-2-3 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(1;0;3;2): 3 steps
lem-nat-2-SBOXd⟨1·0·3·2⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻1-0-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-2-3 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨1·0·3·2⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻1-0-3-2 ∷ []) (Sb⁻1-0-2-3 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS03⁻ ∷ []) (refl) ▸
       at 0 2 (CS02⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd03 c4) ▸
       at 0 1 (Sb⁻1-0-2-3 ∷ []) (refl) ▸ done


-- nat 2 BOXd(1;03): 3 steps
lem-nat-2-BOXd⟨1·03⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻1-03 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-02 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨1·03⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻1-03 ∷ []) (Bx⁻1-02 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ03 ∷ []) (refl) ▸
       at 0 2 (CZ02 ∷ Sw23 ∷ []) (lem-nat-2-CZ03 c4) ▸
       at 0 1 (Bx⁻1-02 ∷ []) (refl) ▸ done


-- nat 2 BOXd(0;123): 8 steps
lem-nat-2-BOXd⟨0·123⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻0-123 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-132 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨0·123⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻0-123 ∷ []) (Bx⁻0-132 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx⁻1-03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻1-03 ∷ Toff012 ∷ CCZ012 ∷ []) (refl) ▸
       at 0 2 (Bx⁻1-02 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·03⟩ c4) ▸
       at 1 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 2 2 (Toff013 ∷ Sw23 ∷ []) (lem-nat-2-TOFF012 c4) ▸
       at 3 2 (Bx⁻1-02 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·03⟩ c4) ▸
       at 4 2 (Toff013 ∷ Sw23 ∷ []) (lem-nat-2-TOFF012 c4) ▸
       at 5 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 0 6 (Bx⁻0-132 ∷ []) (refl) ▸ done


-- nat 2 BOXd(1;0423): 8 steps
lem-nat-2-BOXd⟨1·0423⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻1-0423 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-0432 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨1·0423⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻1-0423 ∷ []) (Bx⁻1-0432 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx⁻0-123 ∷ CCZ014 ∷ Toff104 ∷ Bx⁻0-123 ∷ Toff104 ∷ CCZ014 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-132 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·123⟩ c4) ▸
       at 1 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 2 2 (Toff104 ∷ Sw23 ∷ []) (lem-nat-2-TOFF104 c4) ▸
       at 3 2 (Bx⁻0-132 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·123⟩ c4) ▸
       at 4 2 (Toff104 ∷ Sw23 ∷ []) (lem-nat-2-TOFF104 c4) ▸
       at 5 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 0 6 (Bx⁻1-0432 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(1;0;42;3): 7 steps
lem-nat-2-SBOXd⟨1·0·42·3⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-43-2 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨1·0·42·3⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻1-0-42-3 ∷ []) (Sb⁻1-0-43-2 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ Toff324 ∷ Bx⁻1-0423 ∷ []) (refl) ▸
       at 0 2 (Sb1-0-2-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·3·2⟩ c4) ▸
       at 1 2 (Toff234 ∷ Sw23 ∷ []) (wl0144 c4) ▸
       at 2 2 (Sb⁻1-0-2-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·0·3·2⟩ c4) ▸
       at 3 2 (Toff234 ∷ Sw23 ∷ []) (wl0144 c4) ▸
       at 4 2 (Bx⁻1-0432 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·0423⟩ c4) ▸
       at 0 5 (Sb⁻1-0-43-2 ∷ []) (refl) ▸ done


-- nat 3 SBOX(1;0;2;3): 2 steps
lem-nat-3-SBOX⟨1·0·2·3⟩ : WsL → ⟪ (Sw34 ∷ Sb1-0-2-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-2-4 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨1·0·2·3⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb1-0-2-3 ∷ []) (Sb1-0-2-4 ∷ Sw34 ∷ [])
  b0 = at 0 2 (Sb1-0-2-3 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑ • CS • Swap ↑) (Swap))) ▸
       at 0 1 (Sb1-0-2-4 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 3 SBOXd(1;0;2;3): 2 steps
lem-nat-3-SBOXd⟨1·0·2·3⟩ : WsL → ⟪ (Sw34 ∷ Sb⁻1-0-2-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-2-4 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨1·0·2·3⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb⁻1-0-2-3 ∷ []) (Sb⁻1-0-2-4 ∷ Sw34 ∷ [])
  b0 = at 0 2 (Sb⁻1-0-2-3 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑ • (CS • CS • CS) • Swap ↑) (Swap))) ▸
       at 0 1 (Sb⁻1-0-2-4 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 3 BOXd(0;132): 8 steps
lem-nat-3-BOXd⟨0·132⟩ : WsL → ⟪ (Sw34 ∷ Bx⁻0-132 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-142 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨0·132⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx⁻0-132 ∷ []) (Bx⁻0-142 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx⁻1-02 ∷ CCZ013 ∷ Toff013 ∷ Bx⁻1-02 ∷ Toff013 ∷ CCZ013 ∷ []) (refl) ▸
       at 0 2 (Bx⁻1-02 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑ • CZ • Swap ↑) (Swap))) ▸
       at 1 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4) ▸
       at 2 2 (Toff014 ∷ Sw34 ∷ []) (lem-nat-3-TOFF013 c4) ▸
       at 3 2 (Bx⁻1-02 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑ • CZ • Swap ↑) (Swap))) ▸
       at 4 2 (Toff014 ∷ Sw34 ∷ []) (lem-nat-3-TOFF013 c4) ▸
       at 5 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4) ▸
       at 0 6 (Bx⁻0-142 ∷ []) (refl) ▸ done


-- nat 3 BOXd(1;0432): 8 steps
lem-nat-3-BOXd⟨1·0432⟩ : WsL → ⟪ (Sw34 ∷ Bx⁻1-0432 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-0342 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨1·0432⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx⁻1-0432 ∷ []) (Bx⁻1-0342 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx⁻0-132 ∷ CCZ014 ∷ Toff104 ∷ Bx⁻0-132 ∷ Toff104 ∷ CCZ014 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-142 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨0·132⟩ c4) ▸
       at 1 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4) ▸
       at 2 2 (Toff103 ∷ Sw34 ∷ []) (lem-nat-3-TOFF104 c4) ▸
       at 3 2 (Bx⁻0-142 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨0·132⟩ c4) ▸
       at 4 2 (Toff103 ∷ Sw34 ∷ []) (lem-nat-3-TOFF104 c4) ▸
       at 5 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4) ▸
       at 0 6 (Bx⁻1-0342 ∷ []) (refl) ▸ done


-- nat 3 SBOXd(1;0;43;2): 7 steps
lem-nat-3-SBOXd⟨1·0·43·2⟩ : WsL → ⟪ (Sw34 ∷ Sb⁻1-0-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-34-2 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨1·0·43·2⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb⁻1-0-43-2 ∷ []) (Sb⁻1-0-34-2 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ Toff234 ∷ Bx⁻1-0432 ∷ []) (refl) ▸
       at 0 2 (Sb1-0-2-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨1·0·2·3⟩ c4) ▸
       at 1 2 (Toff234 ∷ Sw34 ∷ []) (wl0128 c4) ▸
       at 2 2 (Sb⁻1-0-2-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨1·0·2·3⟩ c4) ▸
       at 3 2 (Toff234 ∷ Sw34 ∷ []) (wl0128 c4) ▸
       at 4 2 (Bx⁻1-0342 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨1·0432⟩ c4) ▸
       at 0 5 (Sb⁻1-0-34-2 ∷ []) (refl) ▸ done


-- nat 2 SBOX(1;0;2;4): 3 steps
lem-nat-2-SBOX⟨1·0·2·4⟩ : WsL → ⟪ (Sw23 ∷ Sb1-0-2-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-3-4 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨1·0·2·4⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb1-0-2-4 ∷ []) (Sb1-0-3-4 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS02 ∷ []) (refl) ▸
       at 0 2 (CS03 ∷ Sw23 ∷ []) (lem-nat-2-CS02 c4) ▸
       at 0 1 (Sb1-0-3-4 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(1;0;2;4): 3 steps
lem-nat-2-SBOXd⟨1·0·2·4⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻1-0-2-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-3-4 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨1·0·2·4⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻1-0-2-4 ∷ []) (Sb⁻1-0-3-4 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS02⁻ ∷ []) (refl) ▸
       at 0 2 (CS03⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd02 c4) ▸
       at 0 1 (Sb⁻1-0-3-4 ∷ []) (refl) ▸ done


-- nat 2 BOXd(1;02): 3 steps
lem-nat-2-BOXd⟨1·02⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻1-02 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-03 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨1·02⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻1-02 ∷ []) (Bx⁻1-03 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ02 ∷ []) (refl) ▸
       at 0 2 (CZ03 ∷ Sw23 ∷ []) (lem-nat-2-CZ02 c4) ▸
       at 0 1 (Bx⁻1-03 ∷ []) (refl) ▸ done


-- nat 2 BOXd(0;142): 8 steps
lem-nat-2-BOXd⟨0·142⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻0-142 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-143 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨0·142⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻0-142 ∷ []) (Bx⁻0-143 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx⁻1-02 ∷ CCZ014 ∷ Toff014 ∷ Bx⁻1-02 ∷ Toff014 ∷ CCZ014 ∷ []) (refl) ▸
       at 0 2 (Bx⁻1-03 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·02⟩ c4) ▸
       at 1 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 2 2 (Toff014 ∷ Sw23 ∷ []) (lem-nat-2-TOFF014 c4) ▸
       at 3 2 (Bx⁻1-03 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·02⟩ c4) ▸
       at 4 2 (Toff014 ∷ Sw23 ∷ []) (lem-nat-2-TOFF014 c4) ▸
       at 5 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 0 6 (Bx⁻0-143 ∷ []) (refl) ▸ done


-- nat 2 BOXd(1;0342): 8 steps
lem-nat-2-BOXd⟨1·0342⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻1-0342 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-0243 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨1·0342⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻1-0342 ∷ []) (Bx⁻1-0243 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx⁻0-142 ∷ CCZ013 ∷ Toff103 ∷ Bx⁻0-142 ∷ Toff103 ∷ CCZ013 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-143 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·142⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 2 2 (Toff102 ∷ Sw23 ∷ []) (lem-nat-2-TOFF103 c4) ▸
       at 3 2 (Bx⁻0-143 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·142⟩ c4) ▸
       at 4 2 (Toff102 ∷ Sw23 ∷ []) (lem-nat-2-TOFF103 c4) ▸
       at 5 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 0 6 (Bx⁻1-0243 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(1;0;34;2): 7 steps
lem-nat-2-SBOXd⟨1·0·34·2⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻1-0-34-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-24-3 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨1·0·34·2⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻1-0-34-2 ∷ []) (Sb⁻1-0-24-3 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sb1-0-2-4 ∷ Toff234 ∷ Sb⁻1-0-2-4 ∷ Toff234 ∷ Bx⁻1-0342 ∷ []) (refl) ▸
       at 0 2 (Sb1-0-3-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·2·4⟩ c4) ▸
       at 1 2 (Toff324 ∷ Sw23 ∷ []) (wl0127 c4) ▸
       at 2 2 (Sb⁻1-0-3-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·0·2·4⟩ c4) ▸
       at 3 2 (Toff324 ∷ Sw23 ∷ []) (wl0127 c4) ▸
       at 4 2 (Bx⁻1-0243 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·0342⟩ c4) ▸
       at 0 5 (Sb⁻1-0-24-3 ∷ []) (refl) ▸ done


-- nat 1 SBOX(1;0;3;4): 3 steps
lem-nat-1-SBOX⟨1·0·3·4⟩ : WsL → ⟪ (Sw12 ∷ Sb1-0-3-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-3-4 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨1·0·3·4⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb1-0-3-4 ∷ []) (Sb2-0-3-4 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS03 ∷ []) (refl) ▸
       at 0 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 c4)) ▸
       at 0 1 (Sb2-0-3-4 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(1;0;3;4): 3 steps
lem-nat-1-SBOXd⟨1·0·3·4⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻1-0-3-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-0-3-4 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨1·0·3·4⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻1-0-3-4 ∷ []) (Sb⁻2-0-3-4 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS03⁻ ∷ []) (refl) ▸
       at 0 2 (CS03⁻ ∷ Sw12 ∷ []) (sym (wl0023 c4)) ▸
       at 0 1 (Sb⁻2-0-3-4 ∷ []) (refl) ▸ done


-- nat 1 BOXd(1;03): 3 steps
lem-nat-1-BOXd⟨1·03⟩ : WsL → ⟪ (Sw12 ∷ Bx⁻1-03 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-03 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨1·03⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻1-03 ∷ []) (Bx⁻2-03 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ03 ∷ []) (refl) ▸
       at 0 2 (CZ03 ∷ Sw12 ∷ []) (sym (wl0098 c4)) ▸
       at 0 1 (Bx⁻2-03 ∷ []) (refl) ▸ done


-- nat 1 BOXd(0;143): 8 steps
lem-nat-1-BOXd⟨0·143⟩ : WsL → ⟪ (Sw12 ∷ Bx⁻0-143 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-243 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨0·143⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻0-143 ∷ []) (Bx⁻0-243 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx⁻1-03 ∷ CCZ014 ∷ Toff014 ∷ Bx⁻1-03 ∷ Toff014 ∷ CCZ014 ∷ []) (refl) ▸
       at 0 2 (Bx⁻2-03 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨1·03⟩ c4) ▸
       at 1 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 2 2 (Toff024 ∷ Sw12 ∷ []) (lem-nat-1-TOFF014 c4) ▸
       at 3 2 (Bx⁻2-03 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨1·03⟩ c4) ▸
       at 4 2 (Toff024 ∷ Sw12 ∷ []) (lem-nat-1-TOFF014 c4) ▸
       at 5 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 0 6 (Bx⁻0-243 ∷ []) (refl) ▸ done


-- nat 1 BOXd(1;0243): 8 steps
lem-nat-1-BOXd⟨1·0243⟩ : WsL → ⟪ (Sw12 ∷ Bx⁻1-0243 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-0143 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨1·0243⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻1-0243 ∷ []) (Bx⁻2-0143 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx⁻0-143 ∷ CCZ012 ∷ Toff102 ∷ Bx⁻0-143 ∷ Toff102 ∷ CCZ012 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-243 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨0·143⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw12 ∷ []) (sym (wl0037 c4)) ▸
       at 2 2 (Toff201 ∷ Sw12 ∷ []) (wl0047 c4) ▸
       at 3 2 (Bx⁻0-243 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨0·143⟩ c4) ▸
       at 4 2 (Toff201 ∷ Sw12 ∷ []) (wl0047 c4) ▸
       at 5 2 (CCZ012 ∷ Sw12 ∷ []) (sym (wl0037 c4)) ▸
       at 0 6 (Bx⁻2-0143 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(1;0;24;3): 7 steps
lem-nat-1-SBOXd⟨1·0·24·3⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻1-0-24-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-0-14-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨1·0·24·3⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻1-0-24-3 ∷ []) (Sb⁻2-0-14-3 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sb1-0-3-4 ∷ Toff324 ∷ Sb⁻1-0-3-4 ∷ Toff324 ∷ Bx⁻1-0243 ∷ []) (refl) ▸
       at 0 2 (Sb2-0-3-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·3·4⟩ c4) ▸
       at 1 2 (Toff314 ∷ Sw12 ∷ []) (wl0063 c4) ▸
       at 2 2 (Sb⁻2-0-3-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·0·3·4⟩ c4) ▸
       at 3 2 (Toff314 ∷ Sw12 ∷ []) (wl0063 c4) ▸
       at 4 2 (Bx⁻2-0143 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨1·0243⟩ c4) ▸
       at 0 5 (Sb⁻2-0-14-3 ∷ []) (refl) ▸ done


-- nat 1 BOXd(0;123): 8 steps
lem-nat-1-BOXd⟨0·123⟩ : WsL → ⟪ (Sw12 ∷ Bx⁻0-123 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-213 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨0·123⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻0-123 ∷ []) (Bx⁻0-213 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx⁻1-03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻1-03 ∷ Toff012 ∷ CCZ012 ∷ []) (refl) ▸
       at 0 2 (Bx⁻2-03 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨1·03⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw12 ∷ []) (sym (wl0037 c4)) ▸
       at 2 2 (Toff012 ∷ Sw12 ∷ []) (wl0038 c4) ▸
       at 3 2 (Bx⁻2-03 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨1·03⟩ c4) ▸
       at 4 2 (Toff012 ∷ Sw12 ∷ []) (wl0038 c4) ▸
       at 5 2 (CCZ012 ∷ Sw12 ∷ []) (sym (wl0037 c4)) ▸
       at 0 6 (Bx⁻0-213 ∷ []) (refl) ▸ done


-- nat 1 BOXd(1;0423): 8 steps
lem-nat-1-BOXd⟨1·0423⟩ : WsL → ⟪ (Sw12 ∷ Bx⁻1-0423 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-0413 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨1·0423⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻1-0423 ∷ []) (Bx⁻2-0413 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx⁻0-123 ∷ CCZ014 ∷ Toff104 ∷ Bx⁻0-123 ∷ Toff104 ∷ CCZ014 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-213 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨0·123⟩ c4) ▸
       at 1 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 2 2 (Toff204 ∷ Sw12 ∷ []) (lem-nat-1-TOFF104 c4) ▸
       at 3 2 (Bx⁻0-213 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨0·123⟩ c4) ▸
       at 4 2 (Toff204 ∷ Sw12 ∷ []) (lem-nat-1-TOFF104 c4) ▸
       at 5 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 0 6 (Bx⁻2-0413 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(1;0;42;3): 7 steps
lem-nat-1-SBOXd⟨1·0·42·3⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-0-41-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨1·0·42·3⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻1-0-42-3 ∷ []) (Sb⁻2-0-41-3 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ Toff324 ∷ Bx⁻1-0423 ∷ []) (refl) ▸
       at 0 2 (Sb2-0-3-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·3·2⟩ c4) ▸
       at 1 2 (Toff314 ∷ Sw12 ∷ []) (wl0063 c4) ▸
       at 2 2 (Sb⁻2-0-3-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·0·3·2⟩ c4) ▸
       at 3 2 (Toff314 ∷ Sw12 ∷ []) (wl0063 c4) ▸
       at 4 2 (Bx⁻2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨1·0423⟩ c4) ▸
       at 0 5 (Sb⁻2-0-41-3 ∷ []) (refl) ▸ done


-- nat 1 BOXd(0;243): 8 steps
lem-nat-1-BOXd⟨0·243⟩ : WsL → ⟪ (Sw12 ∷ Bx⁻0-243 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-143 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨0·243⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻0-243 ∷ []) (Bx⁻0-143 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx⁻2-03 ∷ CCZ024 ∷ Toff024 ∷ Bx⁻2-03 ∷ Toff024 ∷ CCZ024 ∷ []) (refl) ▸
       at 0 2 (Bx⁻1-03 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨2·03⟩ c4) ▸
       at 1 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 2 2 (Toff014 ∷ Sw12 ∷ []) (lem-nat-1-TOFF024 c4) ▸
       at 3 2 (Bx⁻1-03 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨2·03⟩ c4) ▸
       at 4 2 (Toff014 ∷ Sw12 ∷ []) (lem-nat-1-TOFF024 c4) ▸
       at 5 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 0 6 (Bx⁻0-143 ∷ []) (refl) ▸ done


-- nat 1 BOXd(2;0143): 8 steps
lem-nat-1-BOXd⟨2·0143⟩ : WsL → ⟪ (Sw12 ∷ Bx⁻2-0143 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-0243 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨2·0143⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻2-0143 ∷ []) (Bx⁻1-0243 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx⁻0-243 ∷ CCZ012 ∷ Toff201 ∷ Bx⁻0-243 ∷ Toff201 ∷ CCZ012 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-143 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨0·243⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw12 ∷ []) (sym (wl0037 c4)) ▸
       at 2 2 (Toff102 ∷ Sw12 ∷ []) (wl0044 c4) ▸
       at 3 2 (Bx⁻0-143 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨0·243⟩ c4) ▸
       at 4 2 (Toff102 ∷ Sw12 ∷ []) (wl0044 c4) ▸
       at 5 2 (CCZ012 ∷ Sw12 ∷ []) (sym (wl0037 c4)) ▸
       at 0 6 (Bx⁻1-0243 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(2;0;14;3): 7 steps
lem-nat-1-SBOXd⟨2·0·14·3⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻2-0-14-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-24-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨2·0·14·3⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻2-0-14-3 ∷ []) (Sb⁻1-0-24-3 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sb2-0-3-4 ∷ Toff314 ∷ Sb⁻2-0-3-4 ∷ Toff314 ∷ Bx⁻2-0143 ∷ []) (refl) ▸
       at 0 2 (Sb1-0-3-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·3·4⟩ c4) ▸
       at 1 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 c4) ▸
       at 2 2 (Sb⁻1-0-3-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·3·4⟩ c4) ▸
       at 3 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 c4) ▸
       at 4 2 (Bx⁻1-0243 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨2·0143⟩ c4) ▸
       at 0 5 (Sb⁻1-0-24-3 ∷ []) (refl) ▸ done


-- nat 2 BOXd(0;132): 8 steps
lem-nat-2-BOXd⟨0·132⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻0-132 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-123 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨0·132⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻0-132 ∷ []) (Bx⁻0-123 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx⁻1-02 ∷ CCZ013 ∷ Toff013 ∷ Bx⁻1-02 ∷ Toff013 ∷ CCZ013 ∷ []) (refl) ▸
       at 0 2 (Bx⁻1-03 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·02⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 2 2 (Toff012 ∷ Sw23 ∷ []) (lem-nat-2-TOFF013 c4) ▸
       at 3 2 (Bx⁻1-03 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·02⟩ c4) ▸
       at 4 2 (Toff012 ∷ Sw23 ∷ []) (lem-nat-2-TOFF013 c4) ▸
       at 5 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 0 6 (Bx⁻0-123 ∷ []) (refl) ▸ done


-- nat 2 BOXd(1;0432): 8 steps
lem-nat-2-BOXd⟨1·0432⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻1-0432 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-0423 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨1·0432⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻1-0432 ∷ []) (Bx⁻1-0423 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx⁻0-132 ∷ CCZ014 ∷ Toff104 ∷ Bx⁻0-132 ∷ Toff104 ∷ CCZ014 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-123 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·132⟩ c4) ▸
       at 1 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 2 2 (Toff104 ∷ Sw23 ∷ []) (lem-nat-2-TOFF104 c4) ▸
       at 3 2 (Bx⁻0-123 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·132⟩ c4) ▸
       at 4 2 (Toff104 ∷ Sw23 ∷ []) (lem-nat-2-TOFF104 c4) ▸
       at 5 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 0 6 (Bx⁻1-0423 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(1;0;43;2): 7 steps
lem-nat-2-SBOXd⟨1·0·43·2⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻1-0-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-42-3 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨1·0·43·2⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻1-0-43-2 ∷ []) (Sb⁻1-0-42-3 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ Toff234 ∷ Bx⁻1-0432 ∷ []) (refl) ▸
       at 0 2 (Sb1-0-3-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·2·3⟩ c4) ▸
       at 1 2 (Toff324 ∷ Sw23 ∷ []) (wl0127 c4) ▸
       at 2 2 (Sb⁻1-0-3-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·0·2·3⟩ c4) ▸
       at 3 2 (Toff324 ∷ Sw23 ∷ []) (wl0127 c4) ▸
       at 4 2 (Bx⁻1-0423 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·0432⟩ c4) ▸
       at 0 5 (Sb⁻1-0-42-3 ∷ []) (refl) ▸ done


-- nat 2 BOXd(0;143): 8 steps
lem-nat-2-BOXd⟨0·143⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻0-143 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-142 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨0·143⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻0-143 ∷ []) (Bx⁻0-142 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx⁻1-03 ∷ CCZ014 ∷ Toff014 ∷ Bx⁻1-03 ∷ Toff014 ∷ CCZ014 ∷ []) (refl) ▸
       at 0 2 (Bx⁻1-02 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·03⟩ c4) ▸
       at 1 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 2 2 (Toff014 ∷ Sw23 ∷ []) (lem-nat-2-TOFF014 c4) ▸
       at 3 2 (Bx⁻1-02 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·03⟩ c4) ▸
       at 4 2 (Toff014 ∷ Sw23 ∷ []) (lem-nat-2-TOFF014 c4) ▸
       at 5 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 0 6 (Bx⁻0-142 ∷ []) (refl) ▸ done


-- nat 2 BOXd(1;0243): 8 steps
lem-nat-2-BOXd⟨1·0243⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻1-0243 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-0342 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨1·0243⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻1-0243 ∷ []) (Bx⁻1-0342 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx⁻0-143 ∷ CCZ012 ∷ Toff102 ∷ Bx⁻0-143 ∷ Toff102 ∷ CCZ012 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-142 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·143⟩ c4) ▸
       at 1 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 2 2 (Toff103 ∷ Sw23 ∷ []) (lem-nat-2-TOFF102 c4) ▸
       at 3 2 (Bx⁻0-142 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·143⟩ c4) ▸
       at 4 2 (Toff103 ∷ Sw23 ∷ []) (lem-nat-2-TOFF102 c4) ▸
       at 5 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 0 6 (Bx⁻1-0342 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(1;0;24;3): 7 steps
lem-nat-2-SBOXd⟨1·0·24·3⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻1-0-24-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-34-2 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨1·0·24·3⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻1-0-24-3 ∷ []) (Sb⁻1-0-34-2 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sb1-0-3-4 ∷ Toff324 ∷ Sb⁻1-0-3-4 ∷ Toff324 ∷ Bx⁻1-0243 ∷ []) (refl) ▸
       at 0 2 (Sb1-0-2-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·3·4⟩ c4) ▸
       at 1 2 (Toff234 ∷ Sw23 ∷ []) (wl0144 c4) ▸
       at 2 2 (Sb⁻1-0-2-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·0·3·4⟩ c4) ▸
       at 3 2 (Toff234 ∷ Sw23 ∷ []) (wl0144 c4) ▸
       at 4 2 (Bx⁻1-0342 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·0243⟩ c4) ▸
       at 0 5 (Sb⁻1-0-34-2 ∷ []) (refl) ▸ done


-- nat 3 BOXd(0;142): 8 steps
lem-nat-3-BOXd⟨0·142⟩ : WsL → ⟪ (Sw34 ∷ Bx⁻0-142 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-132 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨0·142⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx⁻0-142 ∷ []) (Bx⁻0-132 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx⁻1-02 ∷ CCZ014 ∷ Toff014 ∷ Bx⁻1-02 ∷ Toff014 ∷ CCZ014 ∷ []) (refl) ▸
       at 0 2 (Bx⁻1-02 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑ • CZ • Swap ↑) (Swap))) ▸
       at 1 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4) ▸
       at 2 2 (Toff013 ∷ Sw34 ∷ []) (lem-nat-3-TOFF014 c4) ▸
       at 3 2 (Bx⁻1-02 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑ • CZ • Swap ↑) (Swap))) ▸
       at 4 2 (Toff013 ∷ Sw34 ∷ []) (lem-nat-3-TOFF014 c4) ▸
       at 5 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4) ▸
       at 0 6 (Bx⁻0-132 ∷ []) (refl) ▸ done


-- nat 3 BOXd(1;0342): 8 steps
lem-nat-3-BOXd⟨1·0342⟩ : WsL → ⟪ (Sw34 ∷ Bx⁻1-0342 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-0432 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨1·0342⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx⁻1-0342 ∷ []) (Bx⁻1-0432 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx⁻0-142 ∷ CCZ013 ∷ Toff103 ∷ Bx⁻0-142 ∷ Toff103 ∷ CCZ013 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-132 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨0·142⟩ c4) ▸
       at 1 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4) ▸
       at 2 2 (Toff104 ∷ Sw34 ∷ []) (lem-nat-3-TOFF103 c4) ▸
       at 3 2 (Bx⁻0-132 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨0·142⟩ c4) ▸
       at 4 2 (Toff104 ∷ Sw34 ∷ []) (lem-nat-3-TOFF103 c4) ▸
       at 5 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4) ▸
       at 0 6 (Bx⁻1-0432 ∷ []) (refl) ▸ done


-- nat 3 SBOXd(1;0;34;2): 7 steps
lem-nat-3-SBOXd⟨1·0·34·2⟩ : WsL → ⟪ (Sw34 ∷ Sb⁻1-0-34-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-43-2 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨1·0·34·2⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb⁻1-0-34-2 ∷ []) (Sb⁻1-0-43-2 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sb1-0-2-4 ∷ Toff234 ∷ Sb⁻1-0-2-4 ∷ Toff234 ∷ Bx⁻1-0342 ∷ []) (refl) ▸
       at 0 2 (Sb1-0-2-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨1·0·2·4⟩ c4) ▸
       at 1 2 (Toff234 ∷ Sw34 ∷ []) (wl0128 c4) ▸
       at 2 2 (Sb⁻1-0-2-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨1·0·2·4⟩ c4) ▸
       at 3 2 (Toff234 ∷ Sw34 ∷ []) (wl0128 c4) ▸
       at 4 2 (Bx⁻1-0432 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨1·0342⟩ c4) ▸
       at 0 5 (Sb⁻1-0-43-2 ∷ []) (refl) ▸ done


-- nat 3 SBOXd(0;1;42;3): 7 steps
lem-nat-3-SBOXd⟨0·1·42·3⟩ : WsL → ⟪ (Sw34 ∷ Sb⁻0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-32-4 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨0·1·42·3⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb⁻0-1-42-3 ∷ []) (Sb⁻0-1-32-4 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ Toff324 ∷ Bx⁻0-1423 ∷ []) (refl) ▸
       at 0 2 (Sb0-1-4-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·3·2⟩ c4) ▸
       at 1 2 (Toff423 ∷ Sw34 ∷ []) (wl0119 c4) ▸
       at 2 2 (Sb⁻0-1-4-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·3·2⟩ c4) ▸
       at 3 2 (Toff423 ∷ Sw34 ∷ []) (wl0119 c4) ▸
       at 4 2 (Bx⁻0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨0·1423⟩ c4) ▸
       at 0 5 (Sb⁻0-1-32-4 ∷ []) (refl) ▸ done


-- nat 3 BOXd(0;14): 3 steps
lem-nat-3-BOXd⟨0·14⟩ : WsL → ⟪ (Sw34 ∷ Bx⁻0-14 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-13 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨0·14⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx⁻0-14 ∷ []) (Bx⁻0-13 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CZ14 ∷ []) (refl) ▸
       at 0 2 (CZ13 ∷ Sw34 ∷ []) (lem-nat-3-CZ14 c4) ▸
       at 0 1 (Bx⁻0-13 ∷ []) (refl) ▸ done


-- nat 3 BOXd(1;024): 8 steps
lem-nat-3-BOXd⟨1·024⟩ : WsL → ⟪ (Sw34 ∷ Bx⁻1-024 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-023 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨1·024⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx⁻1-024 ∷ []) (Bx⁻1-023 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx⁻0-14 ∷ CCZ012 ∷ Toff102 ∷ Bx⁻0-14 ∷ Toff102 ∷ CCZ012 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-13 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨0·14⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 2 2 (Toff102 ∷ Sw34 ∷ []) (sym (c₃ (K ↑ • CCZ • K ↑ • iI) (Swap))) ▸
       at 3 2 (Bx⁻0-13 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨0·14⟩ c4) ▸
       at 4 2 (Toff102 ∷ Sw34 ∷ []) (sym (c₃ (K ↑ • CCZ • K ↑ • iI) (Swap))) ▸
       at 5 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 0 6 (Bx⁻1-023 ∷ []) (refl) ▸ done


-- nat 3 BOXd(0;1324): 8 steps
lem-nat-3-BOXd⟨0·1324⟩ : WsL → ⟪ (Sw34 ∷ Bx⁻0-1324 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-1423 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨0·1324⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx⁻0-1324 ∷ []) (Bx⁻0-1423 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx⁻1-024 ∷ CCZ013 ∷ Toff013 ∷ Bx⁻1-024 ∷ Toff013 ∷ CCZ013 ∷ []) (refl) ▸
       at 0 2 (Bx⁻1-023 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨1·024⟩ c4) ▸
       at 1 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4) ▸
       at 2 2 (Toff014 ∷ Sw34 ∷ []) (lem-nat-3-TOFF013 c4) ▸
       at 3 2 (Bx⁻1-023 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨1·024⟩ c4) ▸
       at 4 2 (Toff014 ∷ Sw34 ∷ []) (lem-nat-3-TOFF013 c4) ▸
       at 5 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4) ▸
       at 0 6 (Bx⁻0-1423 ∷ []) (refl) ▸ done


-- nat 3 SBOXd(0;1;32;4): 7 steps
lem-nat-3-SBOXd⟨0·1·32·4⟩ : WsL → ⟪ (Sw34 ∷ Sb⁻0-1-32-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-42-3 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨0·1·32·4⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb⁻0-1-32-4 ∷ []) (Sb⁻0-1-42-3 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ Toff423 ∷ Bx⁻0-1324 ∷ []) (refl) ▸
       at 0 2 (Sb0-1-3-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·4·2⟩ c4) ▸
       at 1 2 (Toff324 ∷ Sw34 ∷ []) (wl0120 c4) ▸
       at 2 2 (Sb⁻0-1-3-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·4·2⟩ c4) ▸
       at 3 2 (Toff324 ∷ Sw34 ∷ []) (wl0120 c4) ▸
       at 4 2 (Bx⁻0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨0·1324⟩ c4) ▸
       at 0 5 (Sb⁻0-1-42-3 ∷ []) (refl) ▸ done


-- nat 0 SBOXd(1;0;42;3): 7 steps
lem-nat-0-SBOXd⟨1·0·42·3⟩ : WsL → ⟪ (Sw01 ∷ Sb⁻1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-42-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨1·0·42·3⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻1-0-42-3 ∷ []) (Sb⁻0-1-42-3 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ Toff324 ∷ Bx⁻1-0423 ∷ []) (refl) ▸
       at 0 2 (Sb0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·3·2⟩ c4) ▸
       at 1 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 2 2 (Sb⁻0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·3·2⟩ c4) ▸
       at 3 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 4 2 (Bx⁻0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨1·0423⟩ c4) ▸
       at 0 5 (Sb⁻0-1-42-3 ∷ []) (refl) ▸ done


-- nat 0 BOXd(0;13): 3 steps
lem-nat-0-BOXd⟨0·13⟩ : WsL → ⟪ (Sw01 ∷ Bx⁻0-13 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-03 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨0·13⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻0-13 ∷ []) (Bx⁻1-03 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CZ13 ∷ []) (refl) ▸
       at 0 2 (CZ03 ∷ Sw01 ∷ []) (sym (wl0088 c4)) ▸
       at 0 1 (Bx⁻1-03 ∷ []) (refl) ▸ done


-- nat 0 BOXd(1;023): 8 steps
lem-nat-0-BOXd⟨1·023⟩ : WsL → ⟪ (Sw01 ∷ Bx⁻1-023 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-123 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨1·023⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻1-023 ∷ []) (Bx⁻0-123 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx⁻0-13 ∷ CCZ012 ∷ Toff102 ∷ Bx⁻0-13 ∷ Toff102 ∷ CCZ012 ∷ []) (refl) ▸
       at 0 2 (Bx⁻1-03 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨0·13⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw01 ∷ []) (sym (wl0096 c4)) ▸
       at 2 2 (Toff012 ∷ Sw01 ∷ []) (wl0097 c4) ▸
       at 3 2 (Bx⁻1-03 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨0·13⟩ c4) ▸
       at 4 2 (Toff012 ∷ Sw01 ∷ []) (wl0097 c4) ▸
       at 5 2 (CCZ012 ∷ Sw01 ∷ []) (sym (wl0096 c4)) ▸
       at 0 6 (Bx⁻0-123 ∷ []) (refl) ▸ done


-- nat 0 BOXd(0;1423): 8 steps
lem-nat-0-BOXd⟨0·1423⟩ : WsL → ⟪ (Sw01 ∷ Bx⁻0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-0423 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨0·1423⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻0-1423 ∷ []) (Bx⁻1-0423 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx⁻1-023 ∷ CCZ014 ∷ Toff014 ∷ Bx⁻1-023 ∷ Toff014 ∷ CCZ014 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-123 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨1·023⟩ c4) ▸
       at 1 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 2 2 (Toff104 ∷ Sw01 ∷ []) (lem-nat-0-TOFF014 c4) ▸
       at 3 2 (Bx⁻0-123 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨1·023⟩ c4) ▸
       at 4 2 (Toff104 ∷ Sw01 ∷ []) (lem-nat-0-TOFF014 c4) ▸
       at 5 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 0 6 (Bx⁻1-0423 ∷ []) (refl) ▸ done


-- nat 0 SBOXd(0;1;42;3): 7 steps
lem-nat-0-SBOXd⟨0·1·42·3⟩ : WsL → ⟪ (Sw01 ∷ Sb⁻0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-42-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨0·1·42·3⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻0-1-42-3 ∷ []) (Sb⁻1-0-42-3 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ Toff324 ∷ Bx⁻0-1423 ∷ []) (refl) ▸
       at 0 2 (Sb1-0-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·3·2⟩ c4) ▸
       at 1 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 2 2 (Sb⁻1-0-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨0·1·3·2⟩ c4) ▸
       at 3 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 4 2 (Bx⁻1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨0·1423⟩ c4) ▸
       at 0 5 (Sb⁻1-0-42-3 ∷ []) (refl) ▸ done


-- comm TOFF203 CX41: 181 steps
lem-comm-TOFF203-CX41 : WsL → ⟪ (Toff203 ∷ CX41 ∷ []) ⟫ʷ ≈ ⟪ (CX41 ∷ Toff203 ∷ []) ⟫ʷ
lem-comm-TOFF203-CX41 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (run b22))))))))))))))))))))))
  where
  b0 : Chain (Toff203 ∷ CX41 ∷ []) (Sw12 ∷ K1 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 1 (Sw12 ∷ Toff103 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 2 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸ done

  b1 : Chain (Sw12 ∷ K1 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ Sw34 ∷ []) (Sw12 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ Sw34 ∷ [])
  b1 = at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 4 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 6 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 8 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 9 2 [] (wl0006 c4) ▸ done

  b2 : Chain (Sw12 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ Sw34 ∷ []) (K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw12 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ Sw34 ∷ [])
  b2 = at 0 2 (K2 ∷ Sw12 ∷ []) (sym (wl0056 c4)) ▸
       at 1 2 (CS23 ∷ Sw12 ∷ []) (sym (wl0025 c4)) ▸
       at 4 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 2 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS23⁻ ∷ Sw12 ∷ []) (sym (wl0046 c4)) ▸
       at 6 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 4 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 c4)) ▸ done

  b3 : Chain (K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw12 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ Sw34 ∷ []) (K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw34 ∷ CX02 ∷ CS04 ∷ K2 ∷ ι ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ Sw34 ∷ [])
  b3 = at 6 2 (K2 ∷ Sw12 ∷ []) (sym (wl0056 c4)) ▸
       at 7 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 8 2 [] (wl0001 c4) ▸
       at 7 2 (Sw34 ∷ ι ∷ []) (c₁ (iI) (Swap ↑ ↑)) ▸
       at 6 2 (Sw34 ∷ K2 ∷ []) (c₃ (K ↑ ↑) (Swap)) ▸
       at 5 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 6 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw34 ∷ CX02 ∷ []) (c₃ (Swap ↑ • CX₀₁ • Swap ↑) (Swap)) ▸ done

  b4 : Chain (K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw34 ∷ CX02 ∷ CS04 ∷ K2 ∷ ι ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ Sw34 ∷ []) (Sw34 ∷ Sw12 ∷ K1 ∷ Sw12 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K2 ∷ ι ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ Sw34 ∷ [])
  b4 = at 3 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 4 3 (CS24⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw34 ∷ CX02 ∷ []) (c₃ (Swap ↑ • CX₀₁ • Swap ↑) (Swap)) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 2 3 (CS24 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw34 ∷ K2 ∷ []) (c₃ (K ↑ ↑) (Swap)) ▸
       at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 2 2 (K1 ∷ Sw12 ∷ []) (sym (wl0062 c4)) ▸ done

  b5 : Chain (Sw34 ∷ Sw12 ∷ K1 ∷ Sw12 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K2 ∷ ι ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ Sw34 ∷ []) (Sw34 ∷ Sw12 ∷ K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ Sw12 ∷ CS03 ∷ Sw34 ∷ K2 ∷ ι ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ Sw34 ∷ [])
  b5 = at 3 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0017 c4)) ▸
       at 5 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0001 c4) ▸
       at 5 2 (CS14⁻ ∷ Sw12 ∷ []) (sym (wl0018 c4)) ▸
       at 7 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0001 c4) ▸
       at 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸ done

  b6 : Chain (Sw34 ∷ Sw12 ∷ K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ Sw12 ∷ CS03 ∷ Sw34 ∷ K2 ∷ ι ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ Sw34 ∷ []) (Sw34 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ Sw34 ∷ Sw34 ∷ CS13 ∷ Sw34 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ Sw34 ∷ [])
  b6 = at 8 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 c4)) ▸
       at 9 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 7 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K1 ∷ Sw12 ∷ []) (sym (wl0062 c4)) ▸
       at 9 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 3 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 5 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b7 : Chain (Sw34 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ Sw34 ∷ Sw34 ∷ CS13 ∷ Sw34 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ Sw34 ∷ []) (Sw34 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ Sw34 ∷ ι ∷ Sw12 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ Sw34 ∷ [])
  b7 = at 4 2 [] (wl0007 c4) ▸
       at 5 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 7 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0007 c4) ▸
       at 7 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 9 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0007 c4) ▸
       at 9 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸ done

  b8 : Chain (Sw34 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ Sw34 ∷ ι ∷ Sw12 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ Sw34 ∷ []) (Sw34 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ Sw34 ∷ [])
  b8 = at 10 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 4 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0006 c4) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0006 c4) ▸ done

  b9 : Chain (Sw34 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ Sw34 ∷ []) (Sw34 ∷ Sw12 ∷ Toff104 ∷ Sw12 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ Sw34 ∷ [])
  b9 = at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (wl0006 c4) ▸
       at 10 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 11 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 4 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸
       at 3 3 (Toff103 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (Toff104 ∷ []) (by-assoc Eq.refl) ▸ done

  b10 : Chain (Sw34 ∷ Sw12 ∷ Toff104 ∷ Sw12 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ Sw34 ∷ []) (Sw34 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw34 ∷ CX32 ∷ Sw34 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ [])
  b10 = at 1 3 (Toff204 ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 2 3 (Toff304 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 10 3 (CX31 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (CX32 ∷ Sw12 ∷ []) (sym (wl0150 c4)) ▸
       at 10 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸ done

  b11 : Chain (Sw34 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw34 ∷ CX32 ∷ Sw34 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ []) (Sw34 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ [])
  b11 = at 8 3 (CX42 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX43 ∷ Sw23 ∷ []) (sym (wl0148 c4)) ▸
       at 6 2 (CX43 ∷ Toff102 ∷ []) (c₃ (K ↑ • CCZ • K ↑ • iI) (CX₁₀)) ▸
       at 5 2 (CX42 ∷ Sw23 ∷ []) (sym (wl0147 c4)) ▸
       at 5 1 (Sw34 ∷ CX32 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0007 c4) ▸
       at 3 2 (CX31 ∷ Sw12 ∷ []) (sym (wl0151 c4)) ▸
       at 3 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b12 : Chain (Sw34 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ []) (Sw34 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw34 ∷ [])
  b12 = at 2 2 [] (wl0006 c4) ▸
       at 3 9 (Toff304 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw23 ∷ Toff204 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0006 c4) ▸
       at 4 1 (Sw12 ∷ Toff104 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (Sw34 ∷ Toff103 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸ done

  b13 : Chain (Sw34 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw34 ∷ []) (Sw34 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw34 ∷ [])
  b13 = at 6 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 7 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 9 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 13 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸ done

  b14 : Chain (Sw34 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw34 ∷ []) (Sw34 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ Sw12 ∷ K1 ∷ CS14 ∷ CX01 ∷ Sw34 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw34 ∷ [])
  b14 = at 11 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 13 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 14 2 [] (wl0006 c4) ▸
       at 5 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 6 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸ done

  b15 : Chain (Sw34 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ Sw12 ∷ K1 ∷ CS14 ∷ CX01 ∷ Sw34 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw34 ∷ []) (Sw34 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ Sw12 ∷ K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw34 ∷ [])
  b15 = at 10 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 8 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 12 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 10 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 12 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 13 2 [] (wl0007 c4) ▸ done

  b16 : Chain (Sw34 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ Sw12 ∷ K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw34 ∷ []) (Sw34 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ K2 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw12 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw34 ∷ [])
  b16 = at 4 2 (K2 ∷ Sw12 ∷ []) (sym (wl0056 c4)) ▸
       at 5 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0008 c4)) ▸
       at 8 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 6 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CS24⁻ ∷ Sw12 ∷ []) (sym (wl0009 c4)) ▸
       at 10 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 8 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 10 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b17 : Chain (Sw34 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ K2 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw12 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw34 ∷ []) (Sw34 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ K2 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K2 ∷ Sw34 ∷ ι ∷ [])
  b17 = at 9 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 10 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 c4)) ▸
       at 11 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 9 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (K2 ∷ Sw12 ∷ []) (sym (wl0056 c4)) ▸
       at 11 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 12 2 [] (wl0001 c4) ▸
       at 11 2 (Sw34 ∷ ι ∷ []) (c₁ (iI) (Swap ↑ ↑)) ▸ done

  b18 : Chain (Sw34 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ K2 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K2 ∷ Sw34 ∷ ι ∷ []) (Sw34 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ K2 ∷ Sw34 ∷ CS23 ∷ Sw34 ∷ Sw34 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K2 ∷ ι ∷ [])
  b18 = at 10 2 (Sw34 ∷ K2 ∷ []) (c₃ (K ↑ ↑) (Swap)) ▸
       at 9 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] (wl0007 c4) ▸
       at 8 2 (Sw34 ∷ CX02 ∷ []) (c₃ (Swap ↑ • CX₀₁ • Swap ↑) (Swap)) ▸
       at 7 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (wl0007 c4) ▸
       at 6 2 (Sw34 ∷ CX02 ∷ []) (c₃ (Swap ↑ • CX₀₁ • Swap ↑) (Swap)) ▸
       at 5 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b19 : Chain (Sw34 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ K2 ∷ Sw34 ∷ CS23 ∷ Sw34 ∷ Sw34 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K2 ∷ ι ∷ []) (Sw34 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw12 ∷ CX02 ∷ CS03 ∷ K2 ∷ ι ∷ [])
  b19 = at 7 2 [] (wl0007 c4) ▸
       at 4 2 (Sw34 ∷ K2 ∷ []) (c₃ (K ↑ ↑) (Swap)) ▸
       at 5 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 6 2 (K1 ∷ Sw12 ∷ []) (sym (wl0062 c4)) ▸
       at 7 2 (CS13 ∷ Sw12 ∷ []) (sym (wl0024 c4)) ▸
       at 9 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0001 c4) ▸
       at 9 2 (CS13⁻ ∷ Sw12 ∷ []) (sym (wl0043 c4)) ▸ done

  b20 : Chain (Sw34 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw12 ∷ CX02 ∷ CS03 ∷ K2 ∷ ι ∷ []) (Sw34 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ K1 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw12 ∷ [])
  b20 = at 11 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (wl0001 c4) ▸
       at 11 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 c4)) ▸
       at 12 2 (K1 ∷ Sw12 ∷ []) (sym (wl0062 c4)) ▸
       at 13 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 7 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b21 : Chain (Sw34 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ K1 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw12 ∷ []) (Sw34 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ Sw23 ∷ ι ∷ Sw12 ∷ [])
  b21 = at 8 2 [] (wl0006 c4) ▸
       at 9 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 11 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (wl0006 c4) ▸
       at 11 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 [] (wl0006 c4) ▸
       at 13 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸ done

  b22 : Chain (Sw34 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ Sw23 ∷ ι ∷ Sw12 ∷ []) (CX41 ∷ Toff203 ∷ [])
  b22 = at 14 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 7 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸
       at 6 3 (Toff103 ∷ []) (by-assoc Eq.refl) ▸
       at 5 3 (Toff203 ∷ []) (by-assoc Eq.refl) ▸
       at 0 5 (CX41 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp CZ13 at 2: 4 steps
lem-resp-CZ13-at-2 : WsL → ⟪ (CZ13 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CZ23 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CZ13-at-2 c4 = run b0
  where
  b0 : Chain (CZ13 ∷ []) (Sw12 ∷ Sw01 ∷ CZ23 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 0 2 (Sw12 ∷ CZ23 ∷ []) (wl0026 c4) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 c4)) ▸
       at 1 2 (Sw01 ∷ CZ23 ∷ []) (sym (c₂ (Swap) (CZ))) ▸ done


-- nat 1 BOX(3;01): 3 steps
lem-nat-1-BOX⟨3·01⟩ : WsL → ⟪ (Sw12 ∷ Bx3-01 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-02 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·01⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-01 ∷ []) (Bx3-02 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ01 ∷ []) (refl) ▸
       at 0 2 (CZ02 ∷ Sw12 ∷ []) (lem-nat-1-CZ01 c4) ▸
       at 0 1 (Bx3-02 ∷ []) (refl) ▸ done


-- nat 1 BOX(0;341): 8 steps
lem-nat-1-BOX⟨0·341⟩ : WsL → ⟪ (Sw12 ∷ Bx0-341 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-342 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·341⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-341 ∷ []) (Bx0-342 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff034 ∷ Bx3-01 ∷ Toff034 ∷ CCZ034 ∷ Bx3-01 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 1 2 (Toff034 ∷ Sw12 ∷ []) (lem-nat-1-TOFF034 c4) ▸
       at 2 2 (Bx3-02 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·01⟩ c4) ▸
       at 3 2 (Toff034 ∷ Sw12 ∷ []) (lem-nat-1-TOFF034 c4) ▸
       at 4 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 5 2 (Bx3-02 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·01⟩ c4) ▸
       at 0 6 (Bx0-342 ∷ []) (refl) ▸ done


-- nat 1 BOX(3;0241): 8 steps
lem-nat-1-BOX⟨3·0241⟩ : WsL → ⟪ (Sw12 ∷ Bx3-0241 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0142 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·0241⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-0241 ∷ []) (Bx3-0142 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff302 ∷ Bx0-341 ∷ Toff302 ∷ CCZ023 ∷ Bx0-341 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 1 2 (Toff301 ∷ Sw12 ∷ []) (lem-nat-1-TOFF302 c4) ▸
       at 2 2 (Bx0-342 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·341⟩ c4) ▸
       at 3 2 (Toff301 ∷ Sw12 ∷ []) (lem-nat-1-TOFF302 c4) ▸
       at 4 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 5 2 (Bx0-342 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·341⟩ c4) ▸
       at 0 6 (Bx3-0142 ∷ []) (refl) ▸ done


-- nat 1 BOX(0;342): 8 steps
lem-nat-1-BOX⟨0·342⟩ : WsL → ⟪ (Sw12 ∷ Bx0-342 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-341 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·342⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-342 ∷ []) (Bx0-341 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff034 ∷ Bx3-02 ∷ Toff034 ∷ CCZ034 ∷ Bx3-02 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 1 2 (Toff034 ∷ Sw12 ∷ []) (lem-nat-1-TOFF034 c4) ▸
       at 2 2 (Bx3-01 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·02⟩ c4) ▸
       at 3 2 (Toff034 ∷ Sw12 ∷ []) (lem-nat-1-TOFF034 c4) ▸
       at 4 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 5 2 (Bx3-01 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·02⟩ c4) ▸
       at 0 6 (Bx0-341 ∷ []) (refl) ▸ done


-- nat 1 BOX(3;0142): 8 steps
lem-nat-1-BOX⟨3·0142⟩ : WsL → ⟪ (Sw12 ∷ Bx3-0142 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0241 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·0142⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-0142 ∷ []) (Bx3-0241 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff301 ∷ Bx0-342 ∷ Toff301 ∷ CCZ013 ∷ Bx0-342 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 1 2 (Toff302 ∷ Sw12 ∷ []) (lem-nat-1-TOFF301 c4) ▸
       at 2 2 (Bx0-341 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·342⟩ c4) ▸
       at 3 2 (Toff302 ∷ Sw12 ∷ []) (lem-nat-1-TOFF301 c4) ▸
       at 4 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 5 2 (Bx0-341 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·342⟩ c4) ▸
       at 0 6 (Bx3-0241 ∷ []) (refl) ▸ done


-- nat 2 BOX(2;01): 2 steps
lem-nat-2-BOX⟨2·01⟩ : WsL → ⟪ (Sw23 ∷ Bx2-01 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-01 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·01⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx2-01 ∷ []) (Bx3-01 ∷ Sw23 ∷ [])
  b0 = at 0 2 (Bx2-01 ∷ Sw23 ∷ []) (sym (c₂ (CZ) (Swap))) ▸
       at 0 1 (Bx3-01 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 2 BOX(0;241): 8 steps
lem-nat-2-BOX⟨0·241⟩ : WsL → ⟪ (Sw23 ∷ Bx0-241 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-341 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·241⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-241 ∷ []) (Bx0-341 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff024 ∷ Bx2-01 ∷ Toff024 ∷ CCZ024 ∷ Bx2-01 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 1 2 (Toff034 ∷ Sw23 ∷ []) (lem-nat-2-TOFF024 c4) ▸
       at 2 2 (Bx3-01 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·01⟩ c4) ▸
       at 3 2 (Toff034 ∷ Sw23 ∷ []) (lem-nat-2-TOFF024 c4) ▸
       at 4 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 5 2 (Bx3-01 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·01⟩ c4) ▸
       at 0 6 (Bx0-341 ∷ []) (refl) ▸ done


-- nat 2 BOX(2;0341): 8 steps
lem-nat-2-BOX⟨2·0341⟩ : WsL → ⟪ (Sw23 ∷ Bx2-0341 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0241 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·0341⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx2-0341 ∷ []) (Bx3-0241 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff203 ∷ Bx0-241 ∷ Toff203 ∷ CCZ023 ∷ Bx0-241 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw23 ∷ []) (sym (wl0065 c4)) ▸
       at 1 2 (Toff302 ∷ Sw23 ∷ []) (wl0090 c4) ▸
       at 2 2 (Bx0-341 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·241⟩ c4) ▸
       at 3 2 (Toff302 ∷ Sw23 ∷ []) (wl0090 c4) ▸
       at 4 2 (CCZ023 ∷ Sw23 ∷ []) (sym (wl0065 c4)) ▸
       at 5 2 (Bx0-341 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·241⟩ c4) ▸
       at 0 6 (Bx3-0241 ∷ []) (refl) ▸ done


-- nat 2 BOX(0;341): 8 steps
lem-nat-2-BOX⟨0·341⟩ : WsL → ⟪ (Sw23 ∷ Bx0-341 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-241 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·341⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-341 ∷ []) (Bx0-241 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff034 ∷ Bx3-01 ∷ Toff034 ∷ CCZ034 ∷ Bx3-01 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 1 2 (Toff024 ∷ Sw23 ∷ []) (lem-nat-2-TOFF034 c4) ▸
       at 2 2 (Bx2-01 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·01⟩ c4) ▸
       at 3 2 (Toff024 ∷ Sw23 ∷ []) (lem-nat-2-TOFF034 c4) ▸
       at 4 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 5 2 (Bx2-01 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·01⟩ c4) ▸
       at 0 6 (Bx0-241 ∷ []) (refl) ▸ done


-- nat 2 BOX(3;0241): 8 steps
lem-nat-2-BOX⟨3·0241⟩ : WsL → ⟪ (Sw23 ∷ Bx3-0241 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0341 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·0241⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx3-0241 ∷ []) (Bx2-0341 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff302 ∷ Bx0-341 ∷ Toff302 ∷ CCZ023 ∷ Bx0-341 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw23 ∷ []) (sym (wl0065 c4)) ▸
       at 1 2 (Toff203 ∷ Sw23 ∷ []) (wl0066 c4) ▸
       at 2 2 (Bx0-241 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·341⟩ c4) ▸
       at 3 2 (Toff203 ∷ Sw23 ∷ []) (wl0066 c4) ▸
       at 4 2 (CCZ023 ∷ Sw23 ∷ []) (sym (wl0065 c4)) ▸
       at 5 2 (Bx0-241 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·341⟩ c4) ▸
       at 0 6 (Bx2-0341 ∷ []) (refl) ▸ done


-- nat 3 BOX(0;241): 8 steps
lem-nat-3-BOX⟨0·241⟩ : WsL → ⟪ (Sw34 ∷ Bx0-241 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-231 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·241⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx0-241 ∷ []) (Bx0-231 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff024 ∷ Bx2-01 ∷ Toff024 ∷ CCZ024 ∷ Bx2-01 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 c4) ▸
       at 1 2 (Toff023 ∷ Sw34 ∷ []) (lem-nat-3-TOFF024 c4) ▸
       at 2 2 (Bx2-01 ∷ Sw34 ∷ []) (sym (c₂ (CZ) (Swap ↑))) ▸
       at 3 2 (Toff023 ∷ Sw34 ∷ []) (lem-nat-3-TOFF024 c4) ▸
       at 4 2 (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 c4) ▸
       at 5 2 (Bx2-01 ∷ Sw34 ∷ []) (sym (c₂ (CZ) (Swap ↑))) ▸
       at 0 6 (Bx0-231 ∷ []) (refl) ▸ done


-- nat 3 BOX(2;0341): 8 steps
lem-nat-3-BOX⟨2·0341⟩ : WsL → ⟪ (Sw34 ∷ Bx2-0341 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0431 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨2·0341⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx2-0341 ∷ []) (Bx2-0431 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff203 ∷ Bx0-241 ∷ Toff203 ∷ CCZ023 ∷ Bx0-241 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw34 ∷ []) (lem-nat-3-CCZ023 c4) ▸
       at 1 2 (Toff204 ∷ Sw34 ∷ []) (lem-nat-3-TOFF203 c4) ▸
       at 2 2 (Bx0-231 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·241⟩ c4) ▸
       at 3 2 (Toff204 ∷ Sw34 ∷ []) (lem-nat-3-TOFF203 c4) ▸
       at 4 2 (CCZ024 ∷ Sw34 ∷ []) (lem-nat-3-CCZ023 c4) ▸
       at 5 2 (Bx0-231 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·241⟩ c4) ▸
       at 0 6 (Bx2-0431 ∷ []) (refl) ▸ done


-- nat 2 BOX(0;123): 8 steps
lem-nat-2-BOX⟨0·123⟩ : WsL → ⟪ (Sw23 ∷ Bx0-123 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-132 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·123⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-123 ∷ []) (Bx0-132 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff012 ∷ Bx1-03 ∷ Toff012 ∷ CCZ012 ∷ Bx1-03 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 1 2 (Toff013 ∷ Sw23 ∷ []) (lem-nat-2-TOFF012 c4) ▸
       at 2 2 (Bx1-02 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·03⟩ c4) ▸
       at 3 2 (Toff013 ∷ Sw23 ∷ []) (lem-nat-2-TOFF012 c4) ▸
       at 4 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 5 2 (Bx1-02 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·03⟩ c4) ▸
       at 0 6 (Bx0-132 ∷ []) (refl) ▸ done


-- nat 2 BOX(1;0423): 8 steps
lem-nat-2-BOX⟨1·0423⟩ : WsL → ⟪ (Sw23 ∷ Bx1-0423 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0432 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·0423⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx1-0423 ∷ []) (Bx1-0432 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff104 ∷ Bx0-123 ∷ Toff104 ∷ CCZ014 ∷ Bx0-123 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 1 2 (Toff104 ∷ Sw23 ∷ []) (lem-nat-2-TOFF104 c4) ▸
       at 2 2 (Bx0-132 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·123⟩ c4) ▸
       at 3 2 (Toff104 ∷ Sw23 ∷ []) (lem-nat-2-TOFF104 c4) ▸
       at 4 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 5 2 (Bx0-132 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·123⟩ c4) ▸
       at 0 6 (Bx1-0432 ∷ []) (refl) ▸ done


-- nat 1 SBOX(3;0;1;4): 3 steps
lem-nat-1-SBOX⟨3·0·1·4⟩ : WsL → ⟪ (Sw12 ∷ Sb3-0-1-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-2-4 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨3·0·1·4⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb3-0-1-4 ∷ []) (Sb3-0-2-4 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS01 ∷ []) (refl) ▸
       at 0 2 (CS02 ∷ Sw12 ∷ []) (lem-nat-1-CS01 c4) ▸
       at 0 1 (Sb3-0-2-4 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(3;0;1;4): 3 steps
lem-nat-1-SBOXd⟨3·0·1·4⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻3-0-1-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻3-0-2-4 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨3·0·1·4⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻3-0-1-4 ∷ []) (Sb⁻3-0-2-4 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS01⁻ ∷ []) (refl) ▸
       at 0 2 (CS02⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd01 c4) ▸
       at 0 1 (Sb⁻3-0-2-4 ∷ []) (refl) ▸ done


-- nat 1 SBOX(3;0;24;1): 7 steps
lem-nat-1-SBOX⟨3·0·24·1⟩ : WsL → ⟪ (Sw12 ∷ Sb3-0-24-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-14-2 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨3·0·24·1⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb3-0-24-1 ∷ []) (Sb3-0-14-2 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx3-0241 ∷ Toff124 ∷ Sb3-0-1-4 ∷ Toff124 ∷ Sb⁻3-0-1-4 ∷ []) (refl) ▸
       at 0 2 (Bx3-0142 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0241⟩ c4) ▸
       at 1 2 (Toff214 ∷ Sw12 ∷ []) (wl0095 c4) ▸
       at 2 2 (Sb3-0-2-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·1·4⟩ c4) ▸
       at 3 2 (Toff214 ∷ Sw12 ∷ []) (wl0095 c4) ▸
       at 4 2 (Sb⁻3-0-2-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨3·0·1·4⟩ c4) ▸
       at 0 5 (Sb3-0-14-2 ∷ []) (refl) ▸ done


-- nat 1 SBOX(3;0;2;4): 3 steps
lem-nat-1-SBOX⟨3·0·2·4⟩ : WsL → ⟪ (Sw12 ∷ Sb3-0-2-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-1-4 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨3·0·2·4⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb3-0-2-4 ∷ []) (Sb3-0-1-4 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS02 ∷ []) (refl) ▸
       at 0 2 (CS01 ∷ Sw12 ∷ []) (lem-nat-1-CS02 c4) ▸
       at 0 1 (Sb3-0-1-4 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(3;0;2;4): 3 steps
lem-nat-1-SBOXd⟨3·0·2·4⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻3-0-2-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻3-0-1-4 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨3·0·2·4⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻3-0-2-4 ∷ []) (Sb⁻3-0-1-4 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS02⁻ ∷ []) (refl) ▸
       at 0 2 (CS01⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd02 c4) ▸
       at 0 1 (Sb⁻3-0-1-4 ∷ []) (refl) ▸ done


-- nat 1 SBOX(3;0;14;2): 7 steps
lem-nat-1-SBOX⟨3·0·14·2⟩ : WsL → ⟪ (Sw12 ∷ Sb3-0-14-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-24-1 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨3·0·14·2⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb3-0-14-2 ∷ []) (Sb3-0-24-1 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx3-0142 ∷ Toff214 ∷ Sb3-0-2-4 ∷ Toff214 ∷ Sb⁻3-0-2-4 ∷ []) (refl) ▸
       at 0 2 (Bx3-0241 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0142⟩ c4) ▸
       at 1 2 (Toff124 ∷ Sw12 ∷ []) (wl0126 c4) ▸
       at 2 2 (Sb3-0-1-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·2·4⟩ c4) ▸
       at 3 2 (Toff124 ∷ Sw12 ∷ []) (wl0126 c4) ▸
       at 4 2 (Sb⁻3-0-1-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨3·0·2·4⟩ c4) ▸
       at 0 5 (Sb3-0-24-1 ∷ []) (refl) ▸ done


-- nat 2 TOFF134: 2 steps
lem-nat-2-TOFF134 : WsL → ⟪ (Sw23 ∷ Toff134 ∷ []) ⟫ʷ ≈ ⟪ (Toff124 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-TOFF134 c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Toff134 ∷ []) (Toff124 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Toff124 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0006 c4) ▸ done


-- nat 2 SBOX(2;0;1;4): 2 steps
lem-nat-2-SBOX⟨2·0·1·4⟩ : WsL → ⟪ (Sw23 ∷ Sb2-0-1-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-1-4 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨2·0·1·4⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb2-0-1-4 ∷ []) (Sb3-0-1-4 ∷ Sw23 ∷ [])
  b0 = at 0 2 (Sb2-0-1-4 ∷ Sw23 ∷ []) (sym (c₂ (CS) (Swap))) ▸
       at 0 1 (Sb3-0-1-4 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 2 SBOXd(2;0;1;4): 2 steps
lem-nat-2-SBOXd⟨2·0·1·4⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻2-0-1-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻3-0-1-4 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨2·0·1·4⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻2-0-1-4 ∷ []) (Sb⁻3-0-1-4 ∷ Sw23 ∷ [])
  b0 = at 0 2 (Sb⁻2-0-1-4 ∷ Sw23 ∷ []) (sym (c₂ (CS • CS • CS) (Swap))) ▸
       at 0 1 (Sb⁻3-0-1-4 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 2 SBOX(2;0;34;1): 7 steps
lem-nat-2-SBOX⟨2·0·34·1⟩ : WsL → ⟪ (Sw23 ∷ Sb2-0-34-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-24-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨2·0·34·1⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb2-0-34-1 ∷ []) (Sb3-0-24-1 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx2-0341 ∷ Toff134 ∷ Sb2-0-1-4 ∷ Toff134 ∷ Sb⁻2-0-1-4 ∷ []) (refl) ▸
       at 0 2 (Bx3-0241 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0341⟩ c4) ▸
       at 1 2 (Toff124 ∷ Sw23 ∷ []) (lem-nat-2-TOFF134 c4) ▸
       at 2 2 (Sb3-0-1-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨2·0·1·4⟩ c4) ▸
       at 3 2 (Toff124 ∷ Sw23 ∷ []) (lem-nat-2-TOFF134 c4) ▸
       at 4 2 (Sb⁻3-0-1-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨2·0·1·4⟩ c4) ▸
       at 0 5 (Sb3-0-24-1 ∷ []) (refl) ▸ done


-- nat 2 SBOX(3;0;1;4): 2 steps
lem-nat-2-SBOX⟨3·0·1·4⟩ : WsL → ⟪ (Sw23 ∷ Sb3-0-1-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-1-4 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨3·0·1·4⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb3-0-1-4 ∷ []) (Sb2-0-1-4 ∷ Sw23 ∷ [])
  b0 = at 0 2 (Sb3-0-1-4 ∷ Sw23 ∷ []) (sym (c₂ (CS) (Swap))) ▸
       at 0 1 (Sb2-0-1-4 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 2 SBOXd(3;0;1;4): 2 steps
lem-nat-2-SBOXd⟨3·0·1·4⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻3-0-1-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-0-1-4 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨3·0·1·4⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻3-0-1-4 ∷ []) (Sb⁻2-0-1-4 ∷ Sw23 ∷ [])
  b0 = at 0 2 (Sb⁻3-0-1-4 ∷ Sw23 ∷ []) (sym (c₂ (CS • CS • CS) (Swap))) ▸
       at 0 1 (Sb⁻2-0-1-4 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 2 SBOX(3;0;24;1): 7 steps
lem-nat-2-SBOX⟨3·0·24·1⟩ : WsL → ⟪ (Sw23 ∷ Sb3-0-24-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-34-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨3·0·24·1⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb3-0-24-1 ∷ []) (Sb2-0-34-1 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx3-0241 ∷ Toff124 ∷ Sb3-0-1-4 ∷ Toff124 ∷ Sb⁻3-0-1-4 ∷ []) (refl) ▸
       at 0 2 (Bx2-0341 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0241⟩ c4) ▸
       at 1 2 (Toff134 ∷ Sw23 ∷ []) (lem-nat-2-TOFF124 c4) ▸
       at 2 2 (Sb2-0-1-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·0·1·4⟩ c4) ▸
       at 3 2 (Toff134 ∷ Sw23 ∷ []) (lem-nat-2-TOFF124 c4) ▸
       at 4 2 (Sb⁻2-0-1-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨3·0·1·4⟩ c4) ▸
       at 0 5 (Sb2-0-34-1 ∷ []) (refl) ▸ done


-- nat 3 SBOX(2;0;1;4): 2 steps
lem-nat-3-SBOX⟨2·0·1·4⟩ : WsL → ⟪ (Sw34 ∷ Sb2-0-1-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-1-3 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨2·0·1·4⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb2-0-1-4 ∷ []) (Sb2-0-1-3 ∷ Sw34 ∷ [])
  b0 = at 0 2 (Sb2-0-1-4 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸
       at 0 1 (Sb2-0-1-3 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 3 SBOXd(2;0;1;4): 2 steps
lem-nat-3-SBOXd⟨2·0·1·4⟩ : WsL → ⟪ (Sw34 ∷ Sb⁻2-0-1-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-0-1-3 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨2·0·1·4⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb⁻2-0-1-4 ∷ []) (Sb⁻2-0-1-3 ∷ Sw34 ∷ [])
  b0 = at 0 2 (Sb⁻2-0-1-4 ∷ Sw34 ∷ []) (sym (c₂ (CS • CS • CS) (Swap ↑))) ▸
       at 0 1 (Sb⁻2-0-1-3 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 3 SBOX(2;0;34;1): 7 steps
lem-nat-3-SBOX⟨2·0·34·1⟩ : WsL → ⟪ (Sw34 ∷ Sb2-0-34-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-43-1 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨2·0·34·1⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb2-0-34-1 ∷ []) (Sb2-0-43-1 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx2-0341 ∷ Toff134 ∷ Sb2-0-1-4 ∷ Toff134 ∷ Sb⁻2-0-1-4 ∷ []) (refl) ▸
       at 0 2 (Bx2-0431 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·0341⟩ c4) ▸
       at 1 2 (Toff134 ∷ Sw34 ∷ []) (wl0129 c4) ▸
       at 2 2 (Sb2-0-1-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨2·0·1·4⟩ c4) ▸
       at 3 2 (Toff134 ∷ Sw34 ∷ []) (wl0129 c4) ▸
       at 4 2 (Sb⁻2-0-1-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨2·0·1·4⟩ c4) ▸
       at 0 5 (Sb2-0-43-1 ∷ []) (refl) ▸ done


-- nat 1 SBOX(1;0;2;3): 3 steps
lem-nat-1-SBOX⟨1·0·2·3⟩ : WsL → ⟪ (Sw12 ∷ Sb1-0-2-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-1-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨1·0·2·3⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb1-0-2-3 ∷ []) (Sb2-0-1-3 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS02 ∷ []) (refl) ▸
       at 0 2 (CS01 ∷ Sw12 ∷ []) (lem-nat-1-CS02 c4) ▸
       at 0 1 (Sb2-0-1-3 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(1;0;2;3): 3 steps
lem-nat-1-SBOXd⟨1·0·2·3⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻1-0-2-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-0-1-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨1·0·2·3⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻1-0-2-3 ∷ []) (Sb⁻2-0-1-3 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS02⁻ ∷ []) (refl) ▸
       at 0 2 (CS01⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd02 c4) ▸
       at 0 1 (Sb⁻2-0-1-3 ∷ []) (refl) ▸ done


-- nat 1 SBOX(1;0;43;2): 7 steps
lem-nat-1-SBOX⟨1·0·43·2⟩ : WsL → ⟪ (Sw12 ∷ Sb1-0-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-43-1 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨1·0·43·2⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb1-0-43-2 ∷ []) (Sb2-0-43-1 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (refl) ▸
       at 0 2 (Bx2-0431 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0432⟩ c4) ▸
       at 1 2 (Toff134 ∷ Sw12 ∷ []) (wl0140 c4) ▸
       at 2 2 (Sb2-0-1-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·2·3⟩ c4) ▸
       at 3 2 (Toff134 ∷ Sw12 ∷ []) (wl0140 c4) ▸
       at 4 2 (Sb⁻2-0-1-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·0·2·3⟩ c4) ▸
       at 0 5 (Sb2-0-43-1 ∷ []) (refl) ▸ done


-- nat 1 SBOX(2;0;1;3): 3 steps
lem-nat-1-SBOX⟨2·0·1·3⟩ : WsL → ⟪ (Sw12 ∷ Sb2-0-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-2-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨2·0·1·3⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb2-0-1-3 ∷ []) (Sb1-0-2-3 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS01 ∷ []) (refl) ▸
       at 0 2 (CS02 ∷ Sw12 ∷ []) (lem-nat-1-CS01 c4) ▸
       at 0 1 (Sb1-0-2-3 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(2;0;1;3): 3 steps
lem-nat-1-SBOXd⟨2·0·1·3⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻2-0-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-2-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨2·0·1·3⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻2-0-1-3 ∷ []) (Sb⁻1-0-2-3 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS01⁻ ∷ []) (refl) ▸
       at 0 2 (CS02⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd01 c4) ▸
       at 0 1 (Sb⁻1-0-2-3 ∷ []) (refl) ▸ done


-- nat 1 SBOX(2;0;43;1): 7 steps
lem-nat-1-SBOX⟨2·0·43·1⟩ : WsL → ⟪ (Sw12 ∷ Sb2-0-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-43-2 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨2·0·43·1⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb2-0-43-1 ∷ []) (Sb1-0-43-2 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx2-0431 ∷ Toff134 ∷ Sb2-0-1-3 ∷ Toff134 ∷ Sb⁻2-0-1-3 ∷ []) (refl) ▸
       at 0 2 (Bx1-0432 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0431⟩ c4) ▸
       at 1 2 (Toff234 ∷ Sw12 ∷ []) (wl0136 c4) ▸
       at 2 2 (Sb1-0-2-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·1·3⟩ c4) ▸
       at 3 2 (Toff234 ∷ Sw12 ∷ []) (wl0136 c4) ▸
       at 4 2 (Sb⁻1-0-2-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·1·3⟩ c4) ▸
       at 0 5 (Sb1-0-43-2 ∷ []) (refl) ▸ done


-- nat 2 SBOX(1;0;42;3): 7 steps
lem-nat-2-SBOX⟨1·0·42·3⟩ : WsL → ⟪ (Sw23 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-43-2 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨1·0·42·3⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb1-0-42-3 ∷ []) (Sb1-0-43-2 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (refl) ▸
       at 0 2 (Bx1-0432 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·0423⟩ c4) ▸
       at 1 2 (Toff234 ∷ Sw23 ∷ []) (wl0144 c4) ▸
       at 2 2 (Sb1-0-2-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·3·2⟩ c4) ▸
       at 3 2 (Toff234 ∷ Sw23 ∷ []) (wl0144 c4) ▸
       at 4 2 (Sb⁻1-0-2-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·0·3·2⟩ c4) ▸
       at 0 5 (Sb1-0-43-2 ∷ []) (refl) ▸ done


-- nat 1 BOX(3;104): 8 steps
lem-nat-1-BOX⟨3·104⟩ : WsL → ⟪ (Sw12 ∷ Bx3-104 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-204 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·104⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-104 ∷ []) (Bx3-204 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff301 ∷ Bx1-34 ∷ Toff301 ∷ CCZ013 ∷ Bx1-34 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 1 2 (Toff302 ∷ Sw12 ∷ []) (lem-nat-1-TOFF301 c4) ▸
       at 2 2 (Bx2-34 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·34⟩ c4) ▸
       at 3 2 (Toff302 ∷ Sw12 ∷ []) (lem-nat-1-TOFF301 c4) ▸
       at 4 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 5 2 (Bx2-34 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·34⟩ c4) ▸
       at 0 6 (Bx3-204 ∷ []) (refl) ▸ done


-- nat 1 BOX(1;3204): 8 steps
lem-nat-1-BOX⟨1·3204⟩ : WsL → ⟪ (Sw12 ∷ Bx1-3204 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3104 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·3204⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx1-3204 ∷ []) (Bx2-3104 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff123 ∷ Bx3-104 ∷ Toff123 ∷ CCZ123 ∷ Bx3-104 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw12 ∷ []) (sym (wl0111 c4)) ▸
       at 1 2 (Toff213 ∷ Sw12 ∷ []) (wl0146 c4) ▸
       at 2 2 (Bx3-204 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·104⟩ c4) ▸
       at 3 2 (Toff213 ∷ Sw12 ∷ []) (wl0146 c4) ▸
       at 4 2 (CCZ123 ∷ Sw12 ∷ []) (sym (wl0111 c4)) ▸
       at 5 2 (Bx3-204 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·104⟩ c4) ▸
       at 0 6 (Bx2-3104 ∷ []) (refl) ▸ done


-- nat 1 BOX(3;204): 8 steps
lem-nat-1-BOX⟨3·204⟩ : WsL → ⟪ (Sw12 ∷ Bx3-204 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-104 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·204⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-204 ∷ []) (Bx3-104 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff302 ∷ Bx2-34 ∷ Toff302 ∷ CCZ023 ∷ Bx2-34 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 1 2 (Toff301 ∷ Sw12 ∷ []) (lem-nat-1-TOFF302 c4) ▸
       at 2 2 (Bx1-34 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·34⟩ c4) ▸
       at 3 2 (Toff301 ∷ Sw12 ∷ []) (lem-nat-1-TOFF302 c4) ▸
       at 4 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 5 2 (Bx1-34 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·34⟩ c4) ▸
       at 0 6 (Bx3-104 ∷ []) (refl) ▸ done


-- nat 1 BOX(2;3104): 8 steps
lem-nat-1-BOX⟨2·3104⟩ : WsL → ⟪ (Sw12 ∷ Bx2-3104 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3204 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·3104⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx2-3104 ∷ []) (Bx1-3204 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff213 ∷ Bx3-204 ∷ Toff213 ∷ CCZ123 ∷ Bx3-204 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw12 ∷ []) (sym (wl0111 c4)) ▸
       at 1 2 (Toff123 ∷ Sw12 ∷ []) (wl0112 c4) ▸
       at 2 2 (Bx3-104 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·204⟩ c4) ▸
       at 3 2 (Toff123 ∷ Sw12 ∷ []) (wl0112 c4) ▸
       at 4 2 (CCZ123 ∷ Sw12 ∷ []) (sym (wl0111 c4)) ▸
       at 5 2 (Bx3-104 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·204⟩ c4) ▸
       at 0 6 (Bx1-3204 ∷ []) (refl) ▸ done

