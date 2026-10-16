{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.R015 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (WsL ; wl0001 ; wl0002 ; wl0003 ; wl0005 ; wl0006 ; wl0007 ; wl0008 ; wl0009 ; wl0010 ; wl0011 ; wl0012 ; wl0013 ; wl0014 ; wl0015 ; wl0016 ; wl0017 ; wl0018 ; wl0019 ; wl0020 ; wl0021 ; wl0024 ; wl0025 ; wl0027 ; wl0030 ; wl0031 ; wl0032 ; wl0034 ; wl0035 ; wl0036 ; wl0048 ; wl0053 ; wl0061 ; wl0063 ; wl0065 ; wl0066 ; wl0078 ; wl0079 ; wl0084 ; wl0086 ; wl0088 ; wl0089 ; wl0092 ; wl0100 ; wl0102 ; wl0103 ; wl0105 ; wl0108 ; wl0109 ; wl0111 ; wl0112 ; wl0113 ; wl0115 ; wl0117 ; wl0127 ; wl0128 ; wl0130 ; wl0132 ; wl0133 ; wl0136 ; wl0140 ; wl0142 ; wl0144 ; wl0146 ; wl0152 ; wl0155 ; wl0157 ; wl0158 ; wl0159 ; wl0160)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-nat-1-CCZ023 ; lem-nat-1-CCZ034 ; lem-nat-1-TOFF014 ; lem-nat-1-TOFF203 ; lem-nat-2-CCZ012 ; lem-nat-3-CCZ014 ; lem-nat-3-CCZ024 ; lem-nat-3-TOFF014)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-1-CCZ013 ; lem-nat-1-CCZ014 ; lem-nat-1-TOFF301 ; lem-nat-1-TOFF302 ; lem-nat-2-CCZ124 ; lem-nat-2-CCZ134 ; lem-nat-2-TOFF201 ; lem-nat-3-TOFF402)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-0-CCZ034 ; lem-nat-0-CCZ134 ; lem-nat-0-TOFF304 ; lem-nat-0-TOFF314 ; lem-nat-0-TOFF403 ; lem-nat-2-TOFF413)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-0-BOX⟨3·41⟩ ; lem-nat-1-TOFF013 ; lem-nat-1-TOFF304 ; lem-nat-2-TOFF412)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-2-BOX⟨2·0314⟩ ; lem-nat-2-BOX⟨3·0214⟩ ; lem-nat-2-CZ02 ; lem-nat-2-CZ03 ; lem-nat-3-BOX⟨2·0413⟩ ; lem-nat-3-CCZ123 ; lem-nat-3-CCZ124)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-0-BOX⟨3·04⟩ ; lem-nat-1-CZ01 ; lem-nat-1-CZ02 ; lem-nat-2-CZ13 ; lem-nat-3-CS13 ; lem-nat-3-CS14)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-0-TOFF134 ; lem-nat-2-CS02 ; lem-nat-2-CSd02 ; lem-nat-2-TOFF124)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-nat-0-TOFF034 ; lem-nat-1-TOFF403 ; lem-nat-2-CS04 ; lem-nat-2-CSd04 ; lem-nat-3-BOX⟨4·03⟩ ; lem-nat-3-TOFF412)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-2-CSd03 ; lem-nat-3-CS03 ; lem-nat-3-CSd03)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-nat-0-TOFF124)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-nat-0-BOX⟨0·1432⟩ ; lem-nat-2-TOFF134)
open import Examples.Groups.Clifford+CS.Five.D.R012 using (lem-nat-0-BOX⟨3·02⟩ ; lem-nat-1-BOX⟨3·12⟩)
open import Examples.Groups.Clifford+CS.Five.D.R013 using (lem-nat-3-TOFF312)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-nat-1-BOX⟨0·32⟩ ; lem-nat-2-BOX⟨4·0312⟩)
-- nat 1 BOX(3;042): 8 steps
lem-nat-1-BOX⟨3·042⟩ : WsL → ⟪ (Sw12 ∷ Bx3-042 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-041 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·042⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-042 ∷ []) (Bx3-041 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff304 ∷ Bx0-32 ∷ Toff304 ∷ CCZ034 ∷ Bx0-32 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 1 2 (Toff304 ∷ Sw12 ∷ []) (lem-nat-1-TOFF304 c4) ▸
       at 2 2 (Bx0-31 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·32⟩ c4) ▸
       at 3 2 (Toff304 ∷ Sw12 ∷ []) (lem-nat-1-TOFF304 c4) ▸
       at 4 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 5 2 (Bx0-31 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·32⟩ c4) ▸
       at 0 6 (Bx3-041 ∷ []) (refl) ▸ done


-- nat 1 BOX(0;3142): 8 steps
lem-nat-1-BOX⟨0·3142⟩ : WsL → ⟪ (Sw12 ∷ Bx0-3142 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3241 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·3142⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-3142 ∷ []) (Bx0-3241 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff013 ∷ Bx3-042 ∷ Toff013 ∷ CCZ013 ∷ Bx3-042 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 1 2 (Toff023 ∷ Sw12 ∷ []) (lem-nat-1-TOFF013 c4) ▸
       at 2 2 (Bx3-041 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·042⟩ c4) ▸
       at 3 2 (Toff023 ∷ Sw12 ∷ []) (lem-nat-1-TOFF013 c4) ▸
       at 4 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 5 2 (Bx3-041 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·042⟩ c4) ▸
       at 0 6 (Bx0-3241 ∷ []) (refl) ▸ done


-- nat 3 BOX(0;413): 8 steps
lem-nat-3-BOX⟨0·413⟩ : WsL → ⟪ (Sw34 ∷ Bx0-413 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-314 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·413⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx0-413 ∷ []) (Bx0-314 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff014 ∷ Bx4-03 ∷ Toff014 ∷ CCZ014 ∷ Bx4-03 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4) ▸
       at 1 2 (Toff013 ∷ Sw34 ∷ []) (lem-nat-3-TOFF014 c4) ▸
       at 2 2 (Bx3-04 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·03⟩ c4) ▸
       at 3 2 (Toff013 ∷ Sw34 ∷ []) (lem-nat-3-TOFF014 c4) ▸
       at 4 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4) ▸
       at 5 2 (Bx3-04 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·03⟩ c4) ▸
       at 0 6 (Bx0-314 ∷ []) (refl) ▸ done


-- nat 3 BOX(4;0213): 8 steps
lem-nat-3-BOX⟨4·0213⟩ : WsL → ⟪ (Sw34 ∷ Bx4-0213 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0214 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨4·0213⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx4-0213 ∷ []) (Bx3-0214 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff402 ∷ Bx0-413 ∷ Toff402 ∷ CCZ024 ∷ Bx0-413 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 c4) ▸
       at 1 2 (Toff302 ∷ Sw34 ∷ []) (lem-nat-3-TOFF402 c4) ▸
       at 2 2 (Bx0-314 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·413⟩ c4) ▸
       at 3 2 (Toff302 ∷ Sw34 ∷ []) (lem-nat-3-TOFF402 c4) ▸
       at 4 2 (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 c4) ▸
       at 5 2 (Bx0-314 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·413⟩ c4) ▸
       at 0 6 (Bx3-0214 ∷ []) (refl) ▸ done


-- nat 0 BOX(1;30): 3 steps
lem-nat-0-BOX⟨1·30⟩ : WsL → ⟪ (Sw01 ∷ Bx1-30 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-31 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·30⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-30 ∷ []) (Bx0-31 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CZ03 ∷ []) (refl) ▸
       at 0 2 (CZ13 ∷ Sw01 ∷ []) (sym (wl0092 c4)) ▸
       at 0 1 (Bx0-31 ∷ []) (refl) ▸ done


-- nat 0 BOX(3;140): 8 steps
lem-nat-0-BOX⟨3·140⟩ : WsL → ⟪ (Sw01 ∷ Bx3-140 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-041 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·140⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx3-140 ∷ []) (Bx3-041 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff314 ∷ Bx1-30 ∷ Toff314 ∷ CCZ134 ∷ Bx1-30 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 1 2 (Toff304 ∷ Sw01 ∷ []) (lem-nat-0-TOFF314 c4) ▸
       at 2 2 (Bx0-31 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·30⟩ c4) ▸
       at 3 2 (Toff304 ∷ Sw01 ∷ []) (lem-nat-0-TOFF314 c4) ▸
       at 4 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 5 2 (Bx0-31 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·30⟩ c4) ▸
       at 0 6 (Bx3-041 ∷ []) (refl) ▸ done


-- nat 0 BOX(1;3240): 8 steps
lem-nat-0-BOX⟨1·3240⟩ : WsL → ⟪ (Sw01 ∷ Bx1-3240 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3241 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·3240⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-3240 ∷ []) (Bx0-3241 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff123 ∷ Bx3-140 ∷ Toff123 ∷ CCZ123 ∷ Bx3-140 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw01 ∷ []) (sym (wl0003 c4)) ▸
       at 1 2 (Toff023 ∷ Sw01 ∷ []) (wl0053 c4) ▸
       at 2 2 (Bx3-041 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·140⟩ c4) ▸
       at 3 2 (Toff023 ∷ Sw01 ∷ []) (wl0053 c4) ▸
       at 4 2 (CCZ023 ∷ Sw01 ∷ []) (sym (wl0003 c4)) ▸
       at 5 2 (Bx3-041 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·140⟩ c4) ▸
       at 0 6 (Bx0-3241 ∷ []) (refl) ▸ done


-- nat 0 BOX(0;31): 3 steps
lem-nat-0-BOX⟨0·31⟩ : WsL → ⟪ (Sw01 ∷ Bx0-31 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-30 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·31⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-31 ∷ []) (Bx1-30 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CZ13 ∷ []) (refl) ▸
       at 0 2 (CZ03 ∷ Sw01 ∷ []) (sym (wl0088 c4)) ▸
       at 0 1 (Bx1-30 ∷ []) (refl) ▸ done


-- nat 0 BOX(3;041): 8 steps
lem-nat-0-BOX⟨3·041⟩ : WsL → ⟪ (Sw01 ∷ Bx3-041 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-140 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·041⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx3-041 ∷ []) (Bx3-140 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff304 ∷ Bx0-31 ∷ Toff304 ∷ CCZ034 ∷ Bx0-31 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4) ▸
       at 1 2 (Toff314 ∷ Sw01 ∷ []) (lem-nat-0-TOFF304 c4) ▸
       at 2 2 (Bx1-30 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·31⟩ c4) ▸
       at 3 2 (Toff314 ∷ Sw01 ∷ []) (lem-nat-0-TOFF304 c4) ▸
       at 4 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4) ▸
       at 5 2 (Bx1-30 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·31⟩ c4) ▸
       at 0 6 (Bx3-140 ∷ []) (refl) ▸ done


-- nat 0 BOX(0;3241): 8 steps
lem-nat-0-BOX⟨0·3241⟩ : WsL → ⟪ (Sw01 ∷ Bx0-3241 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3240 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·3241⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-3241 ∷ []) (Bx1-3240 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff023 ∷ Bx3-041 ∷ Toff023 ∷ CCZ023 ∷ Bx3-041 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw01 ∷ []) (sym (wl0103 c4)) ▸
       at 1 2 (Toff123 ∷ Sw01 ∷ []) (wl0108 c4) ▸
       at 2 2 (Bx3-140 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·041⟩ c4) ▸
       at 3 2 (Toff123 ∷ Sw01 ∷ []) (wl0108 c4) ▸
       at 4 2 (CCZ123 ∷ Sw01 ∷ []) (sym (wl0103 c4)) ▸
       at 5 2 (Bx3-140 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·041⟩ c4) ▸
       at 0 6 (Bx1-3240 ∷ []) (refl) ▸ done


-- nat 2 BOX(3;20): 3 steps
lem-nat-2-BOX⟨3·20⟩ : WsL → ⟪ (Sw23 ∷ Bx3-20 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-30 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·20⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx3-20 ∷ []) (Bx2-30 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ02 ∷ []) (refl) ▸
       at 0 2 (CZ03 ∷ Sw23 ∷ []) (lem-nat-2-CZ02 c4) ▸
       at 0 1 (Bx2-30 ∷ []) (refl) ▸ done


-- nat 2 BOX(2;340): 8 steps
lem-nat-2-BOX⟨2·340⟩ : WsL → ⟪ (Sw23 ∷ Bx2-340 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-240 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·340⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx2-340 ∷ []) (Bx3-240 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff234 ∷ Bx3-20 ∷ Toff234 ∷ CCZ234 ∷ Bx3-20 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw23 ∷ []) (sym (wl0086 c4)) ▸
       at 1 2 (Toff324 ∷ Sw23 ∷ []) (wl0127 c4) ▸
       at 2 2 (Bx2-30 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·20⟩ c4) ▸
       at 3 2 (Toff324 ∷ Sw23 ∷ []) (wl0127 c4) ▸
       at 4 2 (CCZ234 ∷ Sw23 ∷ []) (sym (wl0086 c4)) ▸
       at 5 2 (Bx2-30 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·20⟩ c4) ▸
       at 0 6 (Bx3-240 ∷ []) (refl) ▸ done


-- nat 2 BOX(3;2140): 8 steps
lem-nat-2-BOX⟨3·2140⟩ : WsL → ⟪ (Sw23 ∷ Bx3-2140 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3140 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·2140⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx3-2140 ∷ []) (Bx2-3140 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff312 ∷ Bx2-340 ∷ Toff312 ∷ CCZ123 ∷ Bx2-340 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw23 ∷ []) (sym (wl0113 c4)) ▸
       at 1 2 (Toff213 ∷ Sw23 ∷ []) (wl0157 c4) ▸
       at 2 2 (Bx3-240 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·340⟩ c4) ▸
       at 3 2 (Toff213 ∷ Sw23 ∷ []) (wl0157 c4) ▸
       at 4 2 (CCZ123 ∷ Sw23 ∷ []) (sym (wl0113 c4)) ▸
       at 5 2 (Bx3-240 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·340⟩ c4) ▸
       at 0 6 (Bx2-3140 ∷ []) (refl) ▸ done


-- nat 2 BOX(2;30): 3 steps
lem-nat-2-BOX⟨2·30⟩ : WsL → ⟪ (Sw23 ∷ Bx2-30 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-20 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·30⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx2-30 ∷ []) (Bx3-20 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ03 ∷ []) (refl) ▸
       at 0 2 (CZ02 ∷ Sw23 ∷ []) (lem-nat-2-CZ03 c4) ▸
       at 0 1 (Bx3-20 ∷ []) (refl) ▸ done


-- nat 2 BOX(3;240): 8 steps
lem-nat-2-BOX⟨3·240⟩ : WsL → ⟪ (Sw23 ∷ Bx3-240 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-340 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·240⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx3-240 ∷ []) (Bx2-340 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff324 ∷ Bx2-30 ∷ Toff324 ∷ CCZ234 ∷ Bx2-30 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw23 ∷ []) (sym (wl0086 c4)) ▸
       at 1 2 (Toff234 ∷ Sw23 ∷ []) (wl0144 c4) ▸
       at 2 2 (Bx3-20 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·30⟩ c4) ▸
       at 3 2 (Toff234 ∷ Sw23 ∷ []) (wl0144 c4) ▸
       at 4 2 (CCZ234 ∷ Sw23 ∷ []) (sym (wl0086 c4)) ▸
       at 5 2 (Bx3-20 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·30⟩ c4) ▸
       at 0 6 (Bx2-340 ∷ []) (refl) ▸ done


-- nat 2 BOX(2;3140): 8 steps
lem-nat-2-BOX⟨2·3140⟩ : WsL → ⟪ (Sw23 ∷ Bx2-3140 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2140 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·3140⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx2-3140 ∷ []) (Bx3-2140 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff213 ∷ Bx3-240 ∷ Toff213 ∷ CCZ123 ∷ Bx3-240 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw23 ∷ []) (sym (wl0113 c4)) ▸
       at 1 2 (Toff312 ∷ Sw23 ∷ []) (wl0158 c4) ▸
       at 2 2 (Bx2-340 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·240⟩ c4) ▸
       at 3 2 (Toff312 ∷ Sw23 ∷ []) (wl0158 c4) ▸
       at 4 2 (CCZ123 ∷ Sw23 ∷ []) (sym (wl0113 c4)) ▸
       at 5 2 (Bx2-340 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·240⟩ c4) ▸
       at 0 6 (Bx3-2140 ∷ []) (refl) ▸ done


-- nat 3 BOX(4;20): 2 steps
lem-nat-3-BOX⟨4·20⟩ : WsL → ⟪ (Sw34 ∷ Bx4-20 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-20 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨4·20⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx4-20 ∷ []) (Bx3-20 ∷ Sw34 ∷ [])
  b0 = at 0 2 (Bx4-20 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑ • CZ • Swap ↑) (Swap))) ▸
       at 0 1 (Bx3-20 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 3 BOX(2;430): 8 steps
lem-nat-3-BOX⟨2·430⟩ : WsL → ⟪ (Sw34 ∷ Bx2-430 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-340 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨2·430⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx2-430 ∷ []) (Bx2-340 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff234 ∷ Bx4-20 ∷ Toff234 ∷ CCZ234 ∷ Bx4-20 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw34 ∷ []) (sym (wl0155 c4)) ▸
       at 1 2 (Toff234 ∷ Sw34 ∷ []) (wl0128 c4) ▸
       at 2 2 (Bx3-20 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·20⟩ c4) ▸
       at 3 2 (Toff234 ∷ Sw34 ∷ []) (wl0128 c4) ▸
       at 4 2 (CCZ234 ∷ Sw34 ∷ []) (sym (wl0155 c4)) ▸
       at 5 2 (Bx3-20 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·20⟩ c4) ▸
       at 0 6 (Bx2-340 ∷ []) (refl) ▸ done


-- nat 3 BOX(4;2130): 8 steps
lem-nat-3-BOX⟨4·2130⟩ : WsL → ⟪ (Sw34 ∷ Bx4-2130 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2140 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨4·2130⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx4-2130 ∷ []) (Bx3-2140 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff412 ∷ Bx2-430 ∷ Toff412 ∷ CCZ124 ∷ Bx2-430 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw34 ∷ []) (lem-nat-3-CCZ124 c4) ▸
       at 1 2 (Toff312 ∷ Sw34 ∷ []) (lem-nat-3-TOFF412 c4) ▸
       at 2 2 (Bx2-340 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·430⟩ c4) ▸
       at 3 2 (Toff312 ∷ Sw34 ∷ []) (lem-nat-3-TOFF412 c4) ▸
       at 4 2 (CCZ123 ∷ Sw34 ∷ []) (lem-nat-3-CCZ124 c4) ▸
       at 5 2 (Bx2-340 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·430⟩ c4) ▸
       at 0 6 (Bx3-2140 ∷ []) (refl) ▸ done


-- nat 3 BOX(3;20): 2 steps
lem-nat-3-BOX⟨3·20⟩ : WsL → ⟪ (Sw34 ∷ Bx3-20 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-20 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨3·20⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx3-20 ∷ []) (Bx4-20 ∷ Sw34 ∷ [])
  b0 = at 0 2 (Bx3-20 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑ • CZ • Swap ↑) (Swap))) ▸
       at 0 1 (Bx4-20 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 3 BOX(2;340): 8 steps
lem-nat-3-BOX⟨2·340⟩ : WsL → ⟪ (Sw34 ∷ Bx2-340 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-430 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨2·340⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx2-340 ∷ []) (Bx2-430 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff234 ∷ Bx3-20 ∷ Toff234 ∷ CCZ234 ∷ Bx3-20 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw34 ∷ []) (sym (wl0155 c4)) ▸
       at 1 2 (Toff234 ∷ Sw34 ∷ []) (wl0128 c4) ▸
       at 2 2 (Bx4-20 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·20⟩ c4) ▸
       at 3 2 (Toff234 ∷ Sw34 ∷ []) (wl0128 c4) ▸
       at 4 2 (CCZ234 ∷ Sw34 ∷ []) (sym (wl0155 c4)) ▸
       at 5 2 (Bx4-20 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·20⟩ c4) ▸
       at 0 6 (Bx2-430 ∷ []) (refl) ▸ done


-- nat 3 BOX(3;2140): 8 steps
lem-nat-3-BOX⟨3·2140⟩ : WsL → ⟪ (Sw34 ∷ Bx3-2140 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2130 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨3·2140⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx3-2140 ∷ []) (Bx4-2130 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff312 ∷ Bx2-340 ∷ Toff312 ∷ CCZ123 ∷ Bx2-340 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw34 ∷ []) (lem-nat-3-CCZ123 c4) ▸
       at 1 2 (Toff412 ∷ Sw34 ∷ []) (lem-nat-3-TOFF312 c4) ▸
       at 2 2 (Bx2-430 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·340⟩ c4) ▸
       at 3 2 (Toff412 ∷ Sw34 ∷ []) (lem-nat-3-TOFF312 c4) ▸
       at 4 2 (CCZ124 ∷ Sw34 ∷ []) (lem-nat-3-CCZ123 c4) ▸
       at 5 2 (Bx2-430 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·340⟩ c4) ▸
       at 0 6 (Bx4-2130 ∷ []) (refl) ▸ done


-- nat 1 BOX(4;10): 3 steps
lem-nat-1-BOX⟨4·10⟩ : WsL → ⟪ (Sw12 ∷ Bx4-10 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-20 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·10⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx4-10 ∷ []) (Bx4-20 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ01 ∷ []) (refl) ▸
       at 0 2 (CZ02 ∷ Sw12 ∷ []) (lem-nat-1-CZ01 c4) ▸
       at 0 1 (Bx4-20 ∷ []) (refl) ▸ done


-- nat 1 BOX(1;430): 8 steps
lem-nat-1-BOX⟨1·430⟩ : WsL → ⟪ (Sw12 ∷ Bx1-430 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-430 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·430⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx1-430 ∷ []) (Bx2-430 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff134 ∷ Bx4-10 ∷ Toff134 ∷ CCZ134 ∷ Bx4-10 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw12 ∷ []) (sym (wl0084 c4)) ▸
       at 1 2 (Toff234 ∷ Sw12 ∷ []) (wl0136 c4) ▸
       at 2 2 (Bx4-20 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·10⟩ c4) ▸
       at 3 2 (Toff234 ∷ Sw12 ∷ []) (wl0136 c4) ▸
       at 4 2 (CCZ234 ∷ Sw12 ∷ []) (sym (wl0084 c4)) ▸
       at 5 2 (Bx4-20 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·10⟩ c4) ▸
       at 0 6 (Bx2-430 ∷ []) (refl) ▸ done


-- nat 1 BOX(4;1230): 8 steps
lem-nat-1-BOX⟨4·1230⟩ : WsL → ⟪ (Sw12 ∷ Bx4-1230 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2130 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·1230⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx4-1230 ∷ []) (Bx4-2130 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff412 ∷ Bx1-430 ∷ Toff412 ∷ CCZ124 ∷ Bx1-430 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw12 ∷ []) (sym (wl0078 c4)) ▸
       at 1 2 (Toff412 ∷ Sw12 ∷ []) (wl0079 c4) ▸
       at 2 2 (Bx2-430 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·430⟩ c4) ▸
       at 3 2 (Toff412 ∷ Sw12 ∷ []) (wl0079 c4) ▸
       at 4 2 (CCZ124 ∷ Sw12 ∷ []) (sym (wl0078 c4)) ▸
       at 5 2 (Bx2-430 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·430⟩ c4) ▸
       at 0 6 (Bx4-2130 ∷ []) (refl) ▸ done


-- nat 1 BOX(4;20): 3 steps
lem-nat-1-BOX⟨4·20⟩ : WsL → ⟪ (Sw12 ∷ Bx4-20 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-10 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·20⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx4-20 ∷ []) (Bx4-10 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ02 ∷ []) (refl) ▸
       at 0 2 (CZ01 ∷ Sw12 ∷ []) (lem-nat-1-CZ02 c4) ▸
       at 0 1 (Bx4-10 ∷ []) (refl) ▸ done


-- nat 1 BOX(2;430): 8 steps
lem-nat-1-BOX⟨2·430⟩ : WsL → ⟪ (Sw12 ∷ Bx2-430 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-430 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·430⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx2-430 ∷ []) (Bx1-430 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff234 ∷ Bx4-20 ∷ Toff234 ∷ CCZ234 ∷ Bx4-20 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0034 c4)) ▸
       at 1 2 (Toff134 ∷ Sw12 ∷ []) (wl0140 c4) ▸
       at 2 2 (Bx4-10 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·20⟩ c4) ▸
       at 3 2 (Toff134 ∷ Sw12 ∷ []) (wl0140 c4) ▸
       at 4 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0034 c4)) ▸
       at 5 2 (Bx4-10 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·20⟩ c4) ▸
       at 0 6 (Bx1-430 ∷ []) (refl) ▸ done


-- nat 1 BOX(4;2130): 8 steps
lem-nat-1-BOX⟨4·2130⟩ : WsL → ⟪ (Sw12 ∷ Bx4-2130 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1230 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·2130⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx4-2130 ∷ []) (Bx4-1230 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff412 ∷ Bx2-430 ∷ Toff412 ∷ CCZ124 ∷ Bx2-430 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw12 ∷ []) (sym (wl0078 c4)) ▸
       at 1 2 (Toff412 ∷ Sw12 ∷ []) (wl0079 c4) ▸
       at 2 2 (Bx1-430 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·430⟩ c4) ▸
       at 3 2 (Toff412 ∷ Sw12 ∷ []) (wl0079 c4) ▸
       at 4 2 (CCZ124 ∷ Sw12 ∷ []) (sym (wl0078 c4)) ▸
       at 5 2 (Bx1-430 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·430⟩ c4) ▸
       at 0 6 (Bx4-1230 ∷ []) (refl) ▸ done


-- nat 2 BOX(1;420): 8 steps
lem-nat-2-BOX⟨1·420⟩ : WsL → ⟪ (Sw23 ∷ Bx1-420 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-430 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·420⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx1-420 ∷ []) (Bx1-430 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff124 ∷ Bx4-10 ∷ Toff124 ∷ CCZ124 ∷ Bx4-10 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 1 2 (Toff134 ∷ Sw23 ∷ []) (lem-nat-2-TOFF124 c4) ▸
       at 2 2 (Bx4-10 ∷ Sw23 ∷ []) (sym (c₂ (CZ) (Swap))) ▸
       at 3 2 (Toff134 ∷ Sw23 ∷ []) (lem-nat-2-TOFF124 c4) ▸
       at 4 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 5 2 (Bx4-10 ∷ Sw23 ∷ []) (sym (c₂ (CZ) (Swap))) ▸
       at 0 6 (Bx1-430 ∷ []) (refl) ▸ done


-- nat 2 BOX(4;1320): 8 steps
lem-nat-2-BOX⟨4·1320⟩ : WsL → ⟪ (Sw23 ∷ Bx4-1320 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1230 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·1320⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx4-1320 ∷ []) (Bx4-1230 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff413 ∷ Bx1-420 ∷ Toff413 ∷ CCZ134 ∷ Bx1-420 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 1 2 (Toff412 ∷ Sw23 ∷ []) (lem-nat-2-TOFF413 c4) ▸
       at 2 2 (Bx1-430 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·420⟩ c4) ▸
       at 3 2 (Toff412 ∷ Sw23 ∷ []) (lem-nat-2-TOFF413 c4) ▸
       at 4 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 5 2 (Bx1-430 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·420⟩ c4) ▸
       at 0 6 (Bx4-1230 ∷ []) (refl) ▸ done


-- nat 2 BOX(1;430): 8 steps
lem-nat-2-BOX⟨1·430⟩ : WsL → ⟪ (Sw23 ∷ Bx1-430 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-420 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·430⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx1-430 ∷ []) (Bx1-420 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff134 ∷ Bx4-10 ∷ Toff134 ∷ CCZ134 ∷ Bx4-10 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 1 2 (Toff124 ∷ Sw23 ∷ []) (lem-nat-2-TOFF134 c4) ▸
       at 2 2 (Bx4-10 ∷ Sw23 ∷ []) (sym (c₂ (CZ) (Swap))) ▸
       at 3 2 (Toff124 ∷ Sw23 ∷ []) (lem-nat-2-TOFF134 c4) ▸
       at 4 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 5 2 (Bx4-10 ∷ Sw23 ∷ []) (sym (c₂ (CZ) (Swap))) ▸
       at 0 6 (Bx1-420 ∷ []) (refl) ▸ done


-- nat 2 BOX(4;1230): 8 steps
lem-nat-2-BOX⟨4·1230⟩ : WsL → ⟪ (Sw23 ∷ Bx4-1230 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1320 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·1230⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx4-1230 ∷ []) (Bx4-1320 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff412 ∷ Bx1-430 ∷ Toff412 ∷ CCZ124 ∷ Bx1-430 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 1 2 (Toff413 ∷ Sw23 ∷ []) (lem-nat-2-TOFF412 c4) ▸
       at 2 2 (Bx1-420 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·430⟩ c4) ▸
       at 3 2 (Toff413 ∷ Sw23 ∷ []) (lem-nat-2-TOFF412 c4) ▸
       at 4 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 5 2 (Bx1-420 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·430⟩ c4) ▸
       at 0 6 (Bx4-1320 ∷ []) (refl) ▸ done


-- nat 2 SBOX(3;0;4;1): 3 steps
lem-nat-2-SBOX⟨3·0·4·1⟩ : WsL → ⟪ (Sw23 ∷ Sb3-0-4-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-4-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨3·0·4·1⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb3-0-4-1 ∷ []) (Sb2-0-4-1 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS04 ∷ []) (refl) ▸
       at 0 2 (CS04 ∷ Sw23 ∷ []) (lem-nat-2-CS04 c4) ▸
       at 0 1 (Sb2-0-4-1 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(3;0;4;1): 3 steps
lem-nat-2-SBOXd⟨3·0·4·1⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻3-0-4-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-0-4-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨3·0·4·1⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻3-0-4-1 ∷ []) (Sb⁻2-0-4-1 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS04⁻ ∷ []) (refl) ▸
       at 0 2 (CS04⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd04 c4) ▸
       at 0 1 (Sb⁻2-0-4-1 ∷ []) (refl) ▸ done


-- nat 2 SBOX(3;0;21;4): 7 steps
lem-nat-2-SBOX⟨3·0·21·4⟩ : WsL → ⟪ (Sw23 ∷ Sb3-0-21-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-31-4 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨3·0·21·4⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb3-0-21-4 ∷ []) (Sb2-0-31-4 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx3-0214 ∷ Toff412 ∷ Sb3-0-4-1 ∷ Toff412 ∷ Sb⁻3-0-4-1 ∷ []) (refl) ▸
       at 0 2 (Bx2-0314 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0214⟩ c4) ▸
       at 1 2 (Toff413 ∷ Sw23 ∷ []) (lem-nat-2-TOFF412 c4) ▸
       at 2 2 (Sb2-0-4-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·0·4·1⟩ c4) ▸
       at 3 2 (Toff413 ∷ Sw23 ∷ []) (lem-nat-2-TOFF412 c4) ▸
       at 4 2 (Sb⁻2-0-4-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨3·0·4·1⟩ c4) ▸
       at 0 5 (Sb2-0-31-4 ∷ []) (refl) ▸ done


-- nat 2 SBOX(4;0;2;1): 3 steps
lem-nat-2-SBOX⟨4·0·2·1⟩ : WsL → ⟪ (Sw23 ∷ Sb4-0-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-0-3-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨4·0·2·1⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb4-0-2-1 ∷ []) (Sb4-0-3-1 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS02 ∷ []) (refl) ▸
       at 0 2 (CS03 ∷ Sw23 ∷ []) (lem-nat-2-CS02 c4) ▸
       at 0 1 (Sb4-0-3-1 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(4;0;2;1): 3 steps
lem-nat-2-SBOXd⟨4·0·2·1⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻4-0-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻4-0-3-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨4·0·2·1⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻4-0-2-1 ∷ []) (Sb⁻4-0-3-1 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS02⁻ ∷ []) (refl) ▸
       at 0 2 (CS03⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd02 c4) ▸
       at 0 1 (Sb⁻4-0-3-1 ∷ []) (refl) ▸ done


-- nat 2 SBOX(4;0;31;2): 7 steps
lem-nat-2-SBOX⟨4·0·31·2⟩ : WsL → ⟪ (Sw23 ∷ Sb4-0-31-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-0-21-3 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨4·0·31·2⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb4-0-31-2 ∷ []) (Sb4-0-21-3 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx4-0312 ∷ Toff213 ∷ Sb4-0-2-1 ∷ Toff213 ∷ Sb⁻4-0-2-1 ∷ []) (refl) ▸
       at 0 2 (Bx4-0213 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·0312⟩ c4) ▸
       at 1 2 (Toff312 ∷ Sw23 ∷ []) (wl0158 c4) ▸
       at 2 2 (Sb4-0-3-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨4·0·2·1⟩ c4) ▸
       at 3 2 (Toff312 ∷ Sw23 ∷ []) (wl0158 c4) ▸
       at 4 2 (Sb⁻4-0-3-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨4·0·2·1⟩ c4) ▸
       at 0 5 (Sb4-0-21-3 ∷ []) (refl) ▸ done


-- nat 0 SBOX(1;4;2;0): 2 steps
lem-nat-0-SBOX⟨1·4·2·0⟩ : WsL → ⟪ (Sw01 ∷ Sb1-4-2-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-4-2-1 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨1·4·2·0⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb1-4-2-0 ∷ []) (Sb0-4-2-1 ∷ Sw01 ∷ [])
  b0 = at 0 2 (Sb1-4-2-0 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑)) ▸
       at 0 1 (Sb0-4-2-1 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 SBOX(0;4;2;1): 2 steps
lem-nat-0-SBOX⟨0·4·2·1⟩ : WsL → ⟪ (Sw01 ∷ Sb0-4-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-4-2-0 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨0·4·2·1⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb0-4-2-1 ∷ []) (Sb1-4-2-0 ∷ Sw01 ∷ [])
  b0 = at 0 2 (Sb0-4-2-1 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑)) ▸
       at 0 1 (Sb1-4-2-0 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 1 SBOX(1;4;2;0): 3 steps
lem-nat-1-SBOX⟨1·4·2·0⟩ : WsL → ⟪ (Sw12 ∷ Sb1-4-2-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-1-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨1·4·2·0⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb1-4-2-0 ∷ []) (Sb2-4-1-0 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS24 ∷ []) (refl) ▸
       at 0 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0017 c4)) ▸
       at 0 1 (Sb2-4-1-0 ∷ []) (refl) ▸ done


-- nat 3 SBOX(4;3;1;0): 3 steps
lem-nat-3-SBOX⟨4·3·1·0⟩ : WsL → ⟪ (Sw34 ∷ Sb4-3-1-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-4-1-0 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨4·3·1·0⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb4-3-1-0 ∷ []) (Sb3-4-1-0 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS13 ∷ []) (refl) ▸
       at 0 2 (CS14 ∷ Sw34 ∷ []) (lem-nat-3-CS13 c4) ▸
       at 0 1 (Sb3-4-1-0 ∷ []) (refl) ▸ done


-- nat 3 SBOX(3;4;1;0): 3 steps
lem-nat-3-SBOX⟨3·4·1·0⟩ : WsL → ⟪ (Sw34 ∷ Sb3-4-1-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-3-1-0 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨3·4·1·0⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb3-4-1-0 ∷ []) (Sb4-3-1-0 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS14 ∷ []) (refl) ▸
       at 0 2 (CS13 ∷ Sw34 ∷ []) (lem-nat-3-CS14 c4) ▸
       at 0 1 (Sb4-3-1-0 ∷ []) (refl) ▸ done


-- nat 1 SBOX(4;3;2;0): 3 steps
lem-nat-1-SBOX⟨4·3·2·0⟩ : WsL → ⟪ (Sw12 ∷ Sb4-3-2-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-3-1-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨4·3·2·0⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb4-3-2-0 ∷ []) (Sb4-3-1-0 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS23 ∷ []) (refl) ▸
       at 0 2 (CS13 ∷ Sw12 ∷ []) (sym (wl0024 c4)) ▸
       at 0 1 (Sb4-3-1-0 ∷ []) (refl) ▸ done


-- nat 1 SBOX(4;3;1;0): 3 steps
lem-nat-1-SBOX⟨4·3·1·0⟩ : WsL → ⟪ (Sw12 ∷ Sb4-3-1-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-3-2-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨4·3·1·0⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb4-3-1-0 ∷ []) (Sb4-3-2-0 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS13 ∷ []) (refl) ▸
       at 0 2 (CS23 ∷ Sw12 ∷ []) (sym (wl0025 c4)) ▸
       at 0 1 (Sb4-3-2-0 ∷ []) (refl) ▸ done


-- nat 2 SBOX(4;2;3;0): 3 steps
lem-nat-2-SBOX⟨4·2·3·0⟩ : WsL → ⟪ (Sw23 ∷ Sb4-2-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-3-2-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨4·2·3·0⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb4-2-3-0 ∷ []) (Sb4-3-2-0 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS23 ∷ []) (refl) ▸
       at 0 2 (CS23 ∷ Sw23 ∷ []) (sym (wl0152 c4)) ▸
       at 0 1 (Sb4-3-2-0 ∷ []) (refl) ▸ done


-- nat 2 SBOX(4;3;2;0): 3 steps
lem-nat-2-SBOX⟨4·3·2·0⟩ : WsL → ⟪ (Sw23 ∷ Sb4-3-2-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-2-3-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨4·3·2·0⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb4-3-2-0 ∷ []) (Sb4-2-3-0 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS23 ∷ []) (refl) ▸
       at 0 2 (CS23 ∷ Sw23 ∷ []) (sym (wl0152 c4)) ▸
       at 0 1 (Sb4-2-3-0 ∷ []) (refl) ▸ done


-- nat 1 SBOX(4;1;3;0): 3 steps
lem-nat-1-SBOX⟨4·1·3·0⟩ : WsL → ⟪ (Sw12 ∷ Sb4-1-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-2-3-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨4·1·3·0⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb4-1-3-0 ∷ []) (Sb4-2-3-0 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS13 ∷ []) (refl) ▸
       at 0 2 (CS23 ∷ Sw12 ∷ []) (sym (wl0025 c4)) ▸
       at 0 1 (Sb4-2-3-0 ∷ []) (refl) ▸ done


-- nat 1 SBOX(4;2;3;0): 3 steps
lem-nat-1-SBOX⟨4·2·3·0⟩ : WsL → ⟪ (Sw12 ∷ Sb4-2-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-1-3-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨4·2·3·0⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb4-2-3-0 ∷ []) (Sb4-1-3-0 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS23 ∷ []) (refl) ▸
       at 0 2 (CS13 ∷ Sw12 ∷ []) (sym (wl0024 c4)) ▸
       at 0 1 (Sb4-1-3-0 ∷ []) (refl) ▸ done


-- nat 0 SBOX(4;0;3;1): 3 steps
lem-nat-0-SBOX⟨4·0·3·1⟩ : WsL → ⟪ (Sw01 ∷ Sb4-0-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-1-3-0 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨4·0·3·1⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb4-0-3-1 ∷ []) (Sb4-1-3-0 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS03 ∷ []) (refl) ▸
       at 0 2 (CS13 ∷ Sw01 ∷ []) (sym (wl0061 c4)) ▸
       at 0 1 (Sb4-1-3-0 ∷ []) (refl) ▸ done


-- nat 0 SBOX(4;1;3;0): 3 steps
lem-nat-0-SBOX⟨4·1·3·0⟩ : WsL → ⟪ (Sw01 ∷ Sb4-1-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-0-3-1 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨4·1·3·0⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb4-1-3-0 ∷ []) (Sb4-0-3-1 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS13 ∷ []) (refl) ▸
       at 0 2 (CS03 ∷ Sw01 ∷ []) (sym (wl0019 c4)) ▸
       at 0 1 (Sb4-0-3-1 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(4;0;3;1): 3 steps
lem-nat-2-SBOXd⟨4·0·3·1⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻4-0-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻4-0-2-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨4·0·3·1⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻4-0-3-1 ∷ []) (Sb⁻4-0-2-1 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS03⁻ ∷ []) (refl) ▸
       at 0 2 (CS02⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd03 c4) ▸
       at 0 1 (Sb⁻4-0-2-1 ∷ []) (refl) ▸ done


-- nat 2 SBOX(2;0;4;1): 3 steps
lem-nat-2-SBOX⟨2·0·4·1⟩ : WsL → ⟪ (Sw23 ∷ Sb2-0-4-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-4-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨2·0·4·1⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb2-0-4-1 ∷ []) (Sb3-0-4-1 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS04 ∷ []) (refl) ▸
       at 0 2 (CS04 ∷ Sw23 ∷ []) (lem-nat-2-CS04 c4) ▸
       at 0 1 (Sb3-0-4-1 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(2;0;4;1): 3 steps
lem-nat-2-SBOXd⟨2·0·4·1⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻2-0-4-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻3-0-4-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨2·0·4·1⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻2-0-4-1 ∷ []) (Sb⁻3-0-4-1 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS04⁻ ∷ []) (refl) ▸
       at 0 2 (CS04⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd04 c4) ▸
       at 0 1 (Sb⁻3-0-4-1 ∷ []) (refl) ▸ done


-- nat 2 SBOX(2;0;31;4): 7 steps
lem-nat-2-SBOX⟨2·0·31·4⟩ : WsL → ⟪ (Sw23 ∷ Sb2-0-31-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-21-4 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨2·0·31·4⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb2-0-31-4 ∷ []) (Sb3-0-21-4 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx2-0314 ∷ Toff413 ∷ Sb2-0-4-1 ∷ Toff413 ∷ Sb⁻2-0-4-1 ∷ []) (refl) ▸
       at 0 2 (Bx3-0214 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0314⟩ c4) ▸
       at 1 2 (Toff412 ∷ Sw23 ∷ []) (lem-nat-2-TOFF413 c4) ▸
       at 2 2 (Sb3-0-4-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨2·0·4·1⟩ c4) ▸
       at 3 2 (Toff412 ∷ Sw23 ∷ []) (lem-nat-2-TOFF413 c4) ▸
       at 4 2 (Sb⁻3-0-4-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨2·0·4·1⟩ c4) ▸
       at 0 5 (Sb3-0-21-4 ∷ []) (refl) ▸ done


-- nat 3 SBOX(2;0;3;1): 3 steps
lem-nat-3-SBOX⟨2·0·3·1⟩ : WsL → ⟪ (Sw34 ∷ Sb2-0-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-4-1 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨2·0·3·1⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb2-0-3-1 ∷ []) (Sb2-0-4-1 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS03 ∷ []) (refl) ▸
       at 0 2 (CS04 ∷ Sw34 ∷ []) (lem-nat-3-CS03 c4) ▸
       at 0 1 (Sb2-0-4-1 ∷ []) (refl) ▸ done


-- nat 3 SBOXd(2;0;3;1): 3 steps
lem-nat-3-SBOXd⟨2·0·3·1⟩ : WsL → ⟪ (Sw34 ∷ Sb⁻2-0-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-0-4-1 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨2·0·3·1⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb⁻2-0-3-1 ∷ []) (Sb⁻2-0-4-1 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS03⁻ ∷ []) (refl) ▸
       at 0 2 (CS04⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd03 c4) ▸
       at 0 1 (Sb⁻2-0-4-1 ∷ []) (refl) ▸ done


-- nat 3 SBOX(2;0;41;3): 7 steps
lem-nat-3-SBOX⟨2·0·41·3⟩ : WsL → ⟪ (Sw34 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-31-4 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨2·0·41·3⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-31-4 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 0 2 (Bx2-0314 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·0413⟩ c4) ▸
       at 1 2 (Toff413 ∷ Sw34 ∷ []) (wl0142 c4) ▸
       at 2 2 (Sb2-0-4-1 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨2·0·3·1⟩ c4) ▸
       at 3 2 (Toff413 ∷ Sw34 ∷ []) (wl0142 c4) ▸
       at 4 2 (Sb⁻2-0-4-1 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨2·0·3·1⟩ c4) ▸
       at 0 5 (Sb2-0-31-4 ∷ []) (refl) ▸ done


-- nat 0 BOX(4;301): 8 steps
lem-nat-0-BOX⟨4·301⟩ : WsL → ⟪ (Sw01 ∷ Bx4-301 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-310 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·301⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx4-301 ∷ []) (Bx4-310 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff403 ∷ Bx3-41 ∷ Toff403 ∷ CCZ034 ∷ Bx3-41 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4) ▸
       at 1 2 (Toff413 ∷ Sw01 ∷ []) (lem-nat-0-TOFF403 c4) ▸
       at 2 2 (Bx3-40 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·41⟩ c4) ▸
       at 3 2 (Toff413 ∷ Sw01 ∷ []) (lem-nat-0-TOFF403 c4) ▸
       at 4 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4) ▸
       at 5 2 (Bx3-40 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·41⟩ c4) ▸
       at 0 6 (Bx4-310 ∷ []) (refl) ▸ done


-- nat 0 BOX(3;4201): 8 steps
lem-nat-0-BOX⟨3·4201⟩ : WsL → ⟪ (Sw01 ∷ Bx3-4201 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4210 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·4201⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx3-4201 ∷ []) (Bx3-4210 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff324 ∷ Bx4-301 ∷ Toff324 ∷ CCZ234 ∷ Bx4-301 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 1 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 2 2 (Bx4-310 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·301⟩ c4) ▸
       at 3 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 4 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 5 2 (Bx4-310 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·301⟩ c4) ▸
       at 0 6 (Bx3-4210 ∷ []) (refl) ▸ done


-- resp TOFF124 at 3: 7 steps
lem-resp-TOFF124-at-3 : WsL → ⟪ (Toff124 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ Toff234 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-TOFF124-at-3 c4 = run b0
  where
  b0 : Chain (Toff124 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ Toff234 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 1 3 (Toff134 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 1 2 (Sw12 ∷ Toff234 ∷ []) (sym (wl0140 c4)) ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 c4)) ▸
       at 2 2 (Sw01 ∷ Toff234 ∷ []) (sym (c₂ (Swap) (Toff))) ▸ done


-- resp CK40 at 2: 12 steps
lem-resp-CK40-at-2 : WsL → ⟪ (CK40 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CK41 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CK40-at-2 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CK40 ∷ []) (Sw12 ∷ Sw34 ∷ CK30 ∷ Sw34 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 0 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 1 2 (Sw12 ∷ CK30 ∷ []) (wl0159 c4) ▸
       at 0 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 1 3 (CK40 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 c4)) ▸
       at 1 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw12 ∷ Sw34 ∷ CK30 ∷ Sw34 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw01 ∷ CK41 ∷ Sw01 ∷ Sw12 ∷ [])
  b1 = at 3 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 2 2 (Sw01 ∷ CK31 ∷ []) (wl0117 c4) ▸
       at 1 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 2 3 (CK41 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp TOFF014 at 2: 74 steps
lem-resp-TOFF014-at-2 : WsL → ⟪ (Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ Toff124 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-TOFF014-at-2 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (run b9)))))))))
  where
  b0 : Chain (Toff014 ∷ []) (Sw12 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 1 3 (Toff024 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 c4)) ▸
       at 1 1 (Sw12 ∷ Toff014 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ Toff013 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw12 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ [])
  b1 = at 3 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 6 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸ done

  b2 : Chain (Sw12 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ Sw34 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ [])
  b2 = at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 10 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 11 2 [] (wl0006 c4) ▸
       at 2 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 5 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 3 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸ done

  b3 : Chain (Sw12 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ Sw34 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ [])
  b3 = at 7 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 5 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 9 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 7 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 9 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 10 2 [] (wl0007 c4) ▸ done

  b4 : Chain (Sw12 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw12 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ [])
  b4 = at 1 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 2 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0008 c4)) ▸
       at 5 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 3 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS24⁻ ∷ Sw12 ∷ []) (sym (wl0009 c4)) ▸
       at 7 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 5 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b5 : Chain (Sw12 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw12 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0 ∷ Sw01 ∷ ι ∷ Sw01 ∷ Sw12 ∷ [])
  b5 = at 6 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 7 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 c4)) ▸
       at 8 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 6 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 8 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 9 2 [] (wl0001 c4) ▸
       at 8 2 (Sw01 ∷ ι ∷ []) (sym (wl0030 c4)) ▸ done

  b6 : Chain (Sw12 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0 ∷ Sw01 ∷ ι ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ K0 ∷ CS24 ∷ CX02 ∷ Sw01 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K1 ∷ ι ∷ Sw01 ∷ Sw12 ∷ [])
  b6 = at 7 2 (Sw01 ∷ K1 ∷ []) (wl0031 c4) ▸
       at 6 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 7 2 (Sw01 ∷ CS13 ∷ []) (wl0019 c4) ▸
       at 6 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 7 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw01 ∷ CX12 ∷ []) (wl0048 c4) ▸
       at 4 2 (Sw01 ∷ CS24⁻ ∷ []) (sym (c₂ (Swap) (Swap ↑ • (CS • CS • CS) • Swap ↑))) ▸ done

  b7 : Chain (Sw12 ∷ K0 ∷ CS24 ∷ CX02 ∷ Sw01 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K1 ∷ ι ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw01 ∷ Sw34 ∷ K1 ∷ CS23 ∷ CX12 ∷ Sw34 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K1 ∷ ι ∷ Sw01 ∷ Sw12 ∷ [])
  b7 = at 3 2 (Sw01 ∷ CX12 ∷ []) (wl0048 c4) ▸
       at 2 2 (Sw01 ∷ CS24 ∷ []) (sym (c₂ (Swap) (Swap ↑ • CS • Swap ↑))) ▸
       at 1 2 (Sw01 ∷ K1 ∷ []) (wl0031 c4) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 3 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 5 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0007 c4) ▸
       at 5 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸ done

  b8 : Chain (Sw12 ∷ Sw01 ∷ Sw34 ∷ K1 ∷ CS23 ∷ CX12 ∷ Sw34 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K1 ∷ ι ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw01 ∷ Sw34 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw34 ∷ Sw01 ∷ Sw12 ∷ [])
  b8 = at 7 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0007 c4) ▸
       at 7 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 9 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0007 c4) ▸
       at 9 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 10 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 3 8 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (wl0032 c4) ▸ done

  b9 : Chain (Sw12 ∷ Sw01 ∷ Sw34 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw34 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw01 ∷ Toff124 ∷ Sw01 ∷ Sw12 ∷ [])
  b9 = at 3 8 (Toff123 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (Toff124 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp CK41 at 2: 4 steps
lem-resp-CK41-at-2 : WsL → ⟪ (CK41 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CK42 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CK41-at-2 c4 = run b0
  where
  b0 : Chain (CK41 ∷ []) (Sw12 ∷ Sw01 ∷ CK42 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 0 2 (Sw12 ∷ CK42 ∷ []) (wl0160 c4) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 c4)) ▸
       at 1 2 (Sw01 ∷ CK42 ∷ []) (sym (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑))) ▸ done


-- nat 0 BOX(3;01): 3 steps
lem-nat-0-BOX⟨3·01⟩ : WsL → ⟪ (Sw01 ∷ Bx3-01 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-10 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·01⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx3-01 ∷ []) (Bx3-10 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CZ01 ∷ []) (refl) ▸
       at 0 2 (CZ01 ∷ Sw01 ∷ []) (sym (wl0130 c4)) ▸
       at 0 1 (Bx3-10 ∷ []) (refl) ▸ done


-- nat 0 BOX(0;321): 8 steps
lem-nat-0-BOX⟨0·321⟩ : WsL → ⟪ (Sw01 ∷ Bx0-321 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-320 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·321⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-321 ∷ []) (Bx1-320 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff023 ∷ Bx3-01 ∷ Toff023 ∷ CCZ023 ∷ Bx3-01 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw01 ∷ []) (sym (wl0103 c4)) ▸
       at 1 2 (Toff123 ∷ Sw01 ∷ []) (wl0108 c4) ▸
       at 2 2 (Bx3-10 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·01⟩ c4) ▸
       at 3 2 (Toff123 ∷ Sw01 ∷ []) (wl0108 c4) ▸
       at 4 2 (CCZ123 ∷ Sw01 ∷ []) (sym (wl0103 c4)) ▸
       at 5 2 (Bx3-10 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·01⟩ c4) ▸
       at 0 6 (Bx1-320 ∷ []) (refl) ▸ done


-- nat 0 BOX(3;0421): 8 steps
lem-nat-0-BOX⟨3·0421⟩ : WsL → ⟪ (Sw01 ∷ Bx3-0421 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1420 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·0421⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx3-0421 ∷ []) (Bx3-1420 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff304 ∷ Bx0-321 ∷ Toff304 ∷ CCZ034 ∷ Bx0-321 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4) ▸
       at 1 2 (Toff314 ∷ Sw01 ∷ []) (lem-nat-0-TOFF304 c4) ▸
       at 2 2 (Bx1-320 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·321⟩ c4) ▸
       at 3 2 (Toff314 ∷ Sw01 ∷ []) (lem-nat-0-TOFF304 c4) ▸
       at 4 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4) ▸
       at 5 2 (Bx1-320 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·321⟩ c4) ▸
       at 0 6 (Bx3-1420 ∷ []) (refl) ▸ done


-- nat 0 SBOX(3;0;1;2): 3 steps
lem-nat-0-SBOX⟨3·0·1·2⟩ : WsL → ⟪ (Sw01 ∷ Sb3-0-1-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-1-0-2 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨3·0·1·2⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb3-0-1-2 ∷ []) (Sb3-1-0-2 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS01 ∷ []) (refl) ▸
       at 0 2 (CS01 ∷ Sw01 ∷ []) (sym (wl0132 c4)) ▸
       at 0 1 (Sb3-1-0-2 ∷ []) (refl) ▸ done


-- nat 0 SBOXd(3;0;1;2): 3 steps
lem-nat-0-SBOXd⟨3·0·1·2⟩ : WsL → ⟪ (Sw01 ∷ Sb⁻3-0-1-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻3-1-0-2 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨3·0·1·2⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻3-0-1-2 ∷ []) (Sb⁻3-1-0-2 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS01⁻ ∷ []) (refl) ▸
       at 0 2 (CS01⁻ ∷ Sw01 ∷ []) (sym (wl0133 c4)) ▸
       at 0 1 (Sb⁻3-1-0-2 ∷ []) (refl) ▸ done


-- nat 0 SBOX(3;0;42;1): 7 steps
lem-nat-0-SBOX⟨3·0·42·1⟩ : WsL → ⟪ (Sw01 ∷ Sb3-0-42-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-1-42-0 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨3·0·42·1⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb3-0-42-1 ∷ []) (Sb3-1-42-0 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx3-0421 ∷ Toff124 ∷ Sb3-0-1-2 ∷ Toff124 ∷ Sb⁻3-0-1-2 ∷ []) (refl) ▸
       at 0 2 (Bx3-1420 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·0421⟩ c4) ▸
       at 1 2 (Toff024 ∷ Sw01 ∷ []) (lem-nat-0-TOFF124 c4) ▸
       at 2 2 (Sb3-1-0-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·0·1·2⟩ c4) ▸
       at 3 2 (Toff024 ∷ Sw01 ∷ []) (lem-nat-0-TOFF124 c4) ▸
       at 4 2 (Sb⁻3-1-0-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨3·0·1·2⟩ c4) ▸
       at 0 5 (Sb3-1-42-0 ∷ []) (refl) ▸ done


-- nat 0 BOX(3;10): 3 steps
lem-nat-0-BOX⟨3·10⟩ : WsL → ⟪ (Sw01 ∷ Bx3-10 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-01 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·10⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx3-10 ∷ []) (Bx3-01 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CZ01 ∷ []) (refl) ▸
       at 0 2 (CZ01 ∷ Sw01 ∷ []) (sym (wl0130 c4)) ▸
       at 0 1 (Bx3-01 ∷ []) (refl) ▸ done


-- nat 0 BOX(1;320): 8 steps
lem-nat-0-BOX⟨1·320⟩ : WsL → ⟪ (Sw01 ∷ Bx1-320 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-321 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·320⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-320 ∷ []) (Bx0-321 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff123 ∷ Bx3-10 ∷ Toff123 ∷ CCZ123 ∷ Bx3-10 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw01 ∷ []) (sym (wl0003 c4)) ▸
       at 1 2 (Toff023 ∷ Sw01 ∷ []) (wl0053 c4) ▸
       at 2 2 (Bx3-01 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·10⟩ c4) ▸
       at 3 2 (Toff023 ∷ Sw01 ∷ []) (wl0053 c4) ▸
       at 4 2 (CCZ023 ∷ Sw01 ∷ []) (sym (wl0003 c4)) ▸
       at 5 2 (Bx3-01 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·10⟩ c4) ▸
       at 0 6 (Bx0-321 ∷ []) (refl) ▸ done


-- nat 0 BOX(3;1420): 8 steps
lem-nat-0-BOX⟨3·1420⟩ : WsL → ⟪ (Sw01 ∷ Bx3-1420 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0421 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·1420⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx3-1420 ∷ []) (Bx3-0421 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff314 ∷ Bx1-320 ∷ Toff314 ∷ CCZ134 ∷ Bx1-320 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 1 2 (Toff304 ∷ Sw01 ∷ []) (lem-nat-0-TOFF314 c4) ▸
       at 2 2 (Bx0-321 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·320⟩ c4) ▸
       at 3 2 (Toff304 ∷ Sw01 ∷ []) (lem-nat-0-TOFF314 c4) ▸
       at 4 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 5 2 (Bx0-321 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·320⟩ c4) ▸
       at 0 6 (Bx3-0421 ∷ []) (refl) ▸ done


-- nat 0 BOX(3;12): 3 steps
lem-nat-0-BOX⟨3·12⟩ : WsL → ⟪ (Sw01 ∷ Bx3-12 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-02 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·12⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx3-12 ∷ []) (Bx3-02 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CZ12 ∷ []) (refl) ▸
       at 0 2 (CZ02 ∷ Sw01 ∷ []) (sym (wl0105 c4)) ▸
       at 0 1 (Bx3-02 ∷ []) (refl) ▸ done


-- nat 0 BOX(1;302): 8 steps
lem-nat-0-BOX⟨1·302⟩ : WsL → ⟪ (Sw01 ∷ Bx1-302 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-312 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·302⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-302 ∷ []) (Bx0-312 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff103 ∷ Bx3-12 ∷ Toff103 ∷ CCZ013 ∷ Bx3-12 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw01 ∷ []) (sym (wl0100 c4)) ▸
       at 1 2 (Toff013 ∷ Sw01 ∷ []) (wl0102 c4) ▸
       at 2 2 (Bx3-02 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·12⟩ c4) ▸
       at 3 2 (Toff013 ∷ Sw01 ∷ []) (wl0102 c4) ▸
       at 4 2 (CCZ013 ∷ Sw01 ∷ []) (sym (wl0100 c4)) ▸
       at 5 2 (Bx3-02 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·12⟩ c4) ▸
       at 0 6 (Bx0-312 ∷ []) (refl) ▸ done


-- nat 0 BOX(3;1402): 8 steps
lem-nat-0-BOX⟨3·1402⟩ : WsL → ⟪ (Sw01 ∷ Bx3-1402 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·1402⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx3-1402 ∷ []) (Bx3-0412 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff314 ∷ Bx1-302 ∷ Toff314 ∷ CCZ134 ∷ Bx1-302 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 1 2 (Toff304 ∷ Sw01 ∷ []) (lem-nat-0-TOFF314 c4) ▸
       at 2 2 (Bx0-312 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·302⟩ c4) ▸
       at 3 2 (Toff304 ∷ Sw01 ∷ []) (lem-nat-0-TOFF314 c4) ▸
       at 4 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 5 2 (Bx0-312 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·302⟩ c4) ▸
       at 0 6 (Bx3-0412 ∷ []) (refl) ▸ done


-- resp TOFF024 at 3: 239 steps
lem-resp-TOFF024-at-3 : WsL → ⟪ (Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ Toff134 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-TOFF024-at-3 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (run b29)))))))))))))))))))))))))))))
  where
  b0 : Chain (Toff024 ∷ []) (Sw23 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 1 3 (Toff034 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 1 1 (Sw23 ∷ Toff024 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw12 ∷ Toff014 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw34 ∷ Toff013 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ [])
  b1 = at 5 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 5 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 7 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸ done

  b2 : Chain (Sw23 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw23 ∷ Sw12 ∷ K0 ∷ CS14 ∷ Sw34 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ [])
  b2 = at 11 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 9 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 11 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 12 2 [] (wl0006 c4) ▸
       at 3 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 6 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 4 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸ done

  b3 : Chain (Sw23 ∷ Sw23 ∷ Sw12 ∷ K0 ∷ CS14 ∷ Sw34 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw23 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ [])
  b3 = at 5 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 6 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 10 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 8 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 10 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸ done

  b4 : Chain (Sw23 ∷ Sw23 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw23 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw12 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ [])
  b4 = at 11 2 [] (wl0007 c4) ▸
       at 2 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 3 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0008 c4)) ▸
       at 6 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 4 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS24⁻ ∷ Sw12 ∷ []) (sym (wl0009 c4)) ▸
       at 8 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 6 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸ done

  b5 : Chain (Sw23 ∷ Sw23 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw12 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw23 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ [])
  b5 = at 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 8 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 c4)) ▸
       at 9 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 7 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 9 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 10 2 [] (wl0001 c4) ▸ done

  b6 : Chain (Sw23 ∷ Sw23 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ K0 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw23 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ [])
  b6 = at 1 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 2 2 (CS34 ∷ Sw23 ∷ []) (sym (wl0011 c4)) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 3 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS34⁻ ∷ Sw23 ∷ []) (sym (wl0012 c4)) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 5 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b7 : Chain (Sw23 ∷ K0 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw23 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ K0 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ [])
  b7 = at 6 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (wl0013 c4) ▸
       at 8 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 9 2 (CS01 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸
       at 10 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 11 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (sym (wl0013 c4)) ▸
       at 6 7 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 8 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸ done

  b8 : Chain (Sw23 ∷ K0 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ K0 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw12 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ [])
  b8 = at 9 2 [] (wl0006 c4) ▸
       at 8 2 (Sw12 ∷ ι ∷ []) (c₁ (iI) (Swap)) ▸
       at 7 2 (Sw12 ∷ K0 ∷ []) (c₁ (K) (Swap)) ▸
       at 6 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 7 2 (Sw12 ∷ CS03 ∷ []) (wl0010 c4) ▸
       at 6 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 7 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸ done

  b9 : Chain (Sw23 ∷ K0 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw12 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw23 ∷ K0 ∷ CS24 ∷ Sw23 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ [])
  b9 = at 5 2 (Sw12 ∷ CX03 ∷ []) (wl0014 c4) ▸
       at 4 2 (Sw12 ∷ CS34⁻ ∷ []) (sym (c₃ (Swap ↑) (CS • CS • CS))) ▸
       at 3 2 (Sw12 ∷ CX03 ∷ []) (wl0014 c4) ▸
       at 2 2 (Sw12 ∷ CS34 ∷ []) (sym (c₃ (Swap ↑) (CS))) ▸
       at 1 2 (Sw12 ∷ K0 ∷ []) (c₁ (K) (Swap)) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 3 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 4 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0015 c4)) ▸ done

  b10 : Chain (Sw23 ∷ Sw12 ∷ Sw23 ∷ K0 ∷ CS24 ∷ Sw23 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw23 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ [])
  b10 = at 6 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0006 c4) ▸
       at 6 2 (CS24⁻ ∷ Sw23 ∷ []) (sym (wl0016 c4)) ▸
       at 8 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0006 c4) ▸
       at 9 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (wl0013 c4) ▸
       at 10 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸ done

  b11 : Chain (Sw23 ∷ Sw12 ∷ Sw23 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ K0 ∷ Sw12 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ [])
  b11 = at 11 2 (CS01 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸
       at 12 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 13 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (sym (wl0013 c4)) ▸
       at 8 7 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 10 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 3 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 4 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸ done

  b12 : Chain (Sw23 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ K0 ∷ Sw12 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ Sw12 ∷ CS03 ∷ Sw34 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ [])
  b12 = at 5 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0017 c4)) ▸
       at 7 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0001 c4) ▸
       at 7 2 (CS14⁻ ∷ Sw12 ∷ []) (sym (wl0018 c4)) ▸
       at 9 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0001 c4) ▸
       at 10 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸ done

  b13 : Chain (Sw23 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ Sw12 ∷ CS03 ∷ Sw34 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ Sw34 ∷ Sw34 ∷ CS13 ∷ Sw34 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ [])
  b13 = at 10 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 c4)) ▸
       at 11 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 9 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 11 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 4 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 5 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 7 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b14 : Chain (Sw23 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ Sw34 ∷ Sw34 ∷ CS13 ∷ Sw34 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ Sw34 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ [])
  b14 = at 6 2 [] (wl0007 c4) ▸
       at 7 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 9 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0007 c4) ▸
       at 9 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 11 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (wl0007 c4) ▸
       at 11 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸ done

  b15 : Chain (Sw23 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ Sw34 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ [])
  b15 = at 12 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 6 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0006 c4) ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 10 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (wl0006 c4) ▸ done

  b16 : Chain (Sw23 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Toff014 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ [])
  b16 = at 10 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] (wl0006 c4) ▸
       at 12 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 13 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 6 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 5 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸
       at 4 3 (Toff014 ∷ []) (by-assoc Eq.refl) ▸ done

  b17 : Chain (Sw23 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Toff014 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b17 = at 3 3 (Toff024 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (Toff034 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 c4)) ▸
       at 2 1 (Sw23 ∷ Toff024 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw12 ∷ Toff014 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (Sw34 ∷ Toff013 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸ done

  b18 : Chain (Sw23 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b18 = at 5 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 6 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 8 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸ done

  b19 : Chain (Sw23 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ Sw34 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b19 = at 10 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 12 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 13 2 [] (wl0006 c4) ▸
       at 4 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 5 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸ done

  b20 : Chain (Sw23 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ Sw34 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b20 = at 9 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 7 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 11 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 9 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 11 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 12 2 [] (wl0007 c4) ▸ done

  b21 : Chain (Sw23 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw23 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw12 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b21 = at 3 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 4 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0008 c4)) ▸
       at 7 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 5 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CS24⁻ ∷ Sw12 ∷ []) (sym (wl0009 c4)) ▸
       at 9 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 7 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 9 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b22 : Chain (Sw23 ∷ Sw12 ∷ Sw23 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw12 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ K0 ∷ Sw23 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b22 = at 8 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 9 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 c4)) ▸
       at 10 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 8 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 10 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 11 2 [] (wl0001 c4) ▸
       at 2 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸ done

  b23 : Chain (Sw23 ∷ Sw12 ∷ K0 ∷ Sw23 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ K0 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw34 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b23 = at 3 2 (CS34 ∷ Sw23 ∷ []) (sym (wl0011 c4)) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 4 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS34⁻ ∷ Sw23 ∷ []) (sym (wl0012 c4)) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 6 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (wl0013 c4) ▸ done

  b24 : Chain (Sw23 ∷ Sw12 ∷ K0 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw34 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ K0 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K0 ∷ ι ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b24 = at 9 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 10 2 (CS01 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸
       at 11 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 12 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (sym (wl0013 c4)) ▸
       at 7 7 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 10 2 [] (wl0006 c4) ▸ done

  b25 : Chain (Sw23 ∷ Sw12 ∷ K0 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K0 ∷ ι ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ K0 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ Sw01 ∷ CX13 ∷ CS14 ∷ K1 ∷ ι ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b25 = at 9 2 (Sw01 ∷ ι ∷ []) (sym (wl0030 c4)) ▸
       at 8 2 (Sw01 ∷ K1 ∷ []) (wl0031 c4) ▸
       at 7 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 8 2 (Sw01 ∷ CS13 ∷ []) (wl0019 c4) ▸
       at 7 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 8 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw01 ∷ CX13 ∷ []) (wl0020 c4) ▸ done

  b26 : Chain (Sw23 ∷ Sw12 ∷ K0 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ Sw01 ∷ CX13 ∷ CS14 ∷ K1 ∷ ι ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ K1 ∷ CS24 ∷ Sw23 ∷ Sw23 ∷ CX12 ∷ Sw23 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1 ∷ ι ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b26 = at 5 2 (Sw01 ∷ CS34⁻ ∷ []) (sym (c₂ (Swap) ((CS • CS • CS) ↑))) ▸
       at 4 2 (Sw01 ∷ CX13 ∷ []) (wl0020 c4) ▸
       at 3 2 (Sw01 ∷ CS34 ∷ []) (sym (c₂ (Swap) (CS ↑))) ▸
       at 2 2 (Sw01 ∷ K1 ∷ []) (wl0031 c4) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 4 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 5 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0015 c4)) ▸
       at 7 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b27 : Chain (Sw23 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ K1 ∷ CS24 ∷ Sw23 ∷ Sw23 ∷ CX12 ∷ Sw23 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1 ∷ ι ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ K1 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b27 = at 6 2 [] (wl0006 c4) ▸
       at 7 2 (CS24⁻ ∷ Sw23 ∷ []) (sym (wl0016 c4)) ▸
       at 9 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0006 c4) ▸
       at 9 2 (CS14 ∷ Sw23 ∷ []) (sym (wl0021 c4)) ▸
       at 10 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 11 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 4 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸ done

  b28 : Chain (Sw23 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ K1 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw34 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw34 ∷ Sw34 ∷ CS13 ∷ Sw34 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b28 = at 5 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 7 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0007 c4) ▸
       at 7 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 9 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0007 c4) ▸
       at 9 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 11 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b29 : Chain (Sw23 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw34 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw34 ∷ Sw34 ∷ CS13 ∷ Sw34 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ Toff134 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b29 = at 10 2 [] (wl0007 c4) ▸
       at 11 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 12 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 5 8 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (wl0032 c4) ▸
       at 5 8 (Toff123 ∷ []) (by-assoc Eq.refl) ▸
       at 4 3 (Toff124 ∷ []) (by-assoc Eq.refl) ▸
       at 3 3 (Toff134 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp CZ24 at 3: 6 steps
lem-resp-CZ24-at-3 : WsL → ⟪ (CZ24 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ CZ34 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-CZ24-at-3 c4 = run b0
  where
  b0 : Chain (CZ24 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ CZ34 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 0 2 (Sw23 ∷ CZ34 ∷ []) (wl0027 c4) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 1 2 (Sw12 ∷ CZ34 ∷ []) (sym (c₃ (Swap ↑) (CZ))) ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 c4)) ▸
       at 2 2 (Sw01 ∷ CZ34 ∷ []) (sym (c₂ (Swap) (CZ ↑))) ▸ done


-- nat 2 BOX(2;13): 3 steps
lem-nat-2-BOX⟨2·13⟩ : WsL → ⟪ (Sw23 ∷ Bx2-13 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-12 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·13⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx2-13 ∷ []) (Bx3-12 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ13 ∷ []) (refl) ▸
       at 0 2 (CZ12 ∷ Sw23 ∷ []) (lem-nat-2-CZ13 c4) ▸
       at 0 1 (Bx3-12 ∷ []) (refl) ▸ done


-- nat 2 BOX(1;243): 8 steps
lem-nat-2-BOX⟨1·243⟩ : WsL → ⟪ (Sw23 ∷ Bx1-243 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-342 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·243⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx1-243 ∷ []) (Bx1-342 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff124 ∷ Bx2-13 ∷ Toff124 ∷ CCZ124 ∷ Bx2-13 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 1 2 (Toff134 ∷ Sw23 ∷ []) (lem-nat-2-TOFF124 c4) ▸
       at 2 2 (Bx3-12 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·13⟩ c4) ▸
       at 3 2 (Toff134 ∷ Sw23 ∷ []) (lem-nat-2-TOFF124 c4) ▸
       at 4 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 5 2 (Bx3-12 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·13⟩ c4) ▸
       at 0 6 (Bx1-342 ∷ []) (refl) ▸ done


-- nat 2 BOX(2;1043): 8 steps
lem-nat-2-BOX⟨2·1043⟩ : WsL → ⟪ (Sw23 ∷ Bx2-1043 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1042 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·1043⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx2-1043 ∷ []) (Bx3-1042 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff201 ∷ Bx1-243 ∷ Toff201 ∷ CCZ012 ∷ Bx1-243 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 1 2 (Toff301 ∷ Sw23 ∷ []) (lem-nat-2-TOFF201 c4) ▸
       at 2 2 (Bx1-342 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·243⟩ c4) ▸
       at 3 2 (Toff301 ∷ Sw23 ∷ []) (lem-nat-2-TOFF201 c4) ▸
       at 4 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 5 2 (Bx1-342 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·243⟩ c4) ▸
       at 0 6 (Bx3-1042 ∷ []) (refl) ▸ done


-- nat 1 BOX(1;342): 8 steps
lem-nat-1-BOX⟨1·342⟩ : WsL → ⟪ (Sw12 ∷ Bx1-342 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-341 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·342⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx1-342 ∷ []) (Bx2-341 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff134 ∷ Bx3-12 ∷ Toff134 ∷ CCZ134 ∷ Bx3-12 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw12 ∷ []) (sym (wl0084 c4)) ▸
       at 1 2 (Toff234 ∷ Sw12 ∷ []) (wl0136 c4) ▸
       at 2 2 (Bx3-21 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·12⟩ c4) ▸
       at 3 2 (Toff234 ∷ Sw12 ∷ []) (wl0136 c4) ▸
       at 4 2 (CCZ234 ∷ Sw12 ∷ []) (sym (wl0084 c4)) ▸
       at 5 2 (Bx3-21 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·12⟩ c4) ▸
       at 0 6 (Bx2-341 ∷ []) (refl) ▸ done


-- nat 1 BOX(3;1042): 8 steps
lem-nat-1-BOX⟨3·1042⟩ : WsL → ⟪ (Sw12 ∷ Bx3-1042 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2041 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·1042⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-1042 ∷ []) (Bx3-2041 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff301 ∷ Bx1-342 ∷ Toff301 ∷ CCZ013 ∷ Bx1-342 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 1 2 (Toff302 ∷ Sw12 ∷ []) (lem-nat-1-TOFF301 c4) ▸
       at 2 2 (Bx2-341 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·342⟩ c4) ▸
       at 3 2 (Toff302 ∷ Sw12 ∷ []) (lem-nat-1-TOFF301 c4) ▸
       at 4 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 5 2 (Bx2-341 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·342⟩ c4) ▸
       at 0 6 (Bx3-2041 ∷ []) (refl) ▸ done


-- nat 0 BOX(1;342): 8 steps
lem-nat-0-BOX⟨1·342⟩ : WsL → ⟪ (Sw01 ∷ Bx1-342 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-342 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·342⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-342 ∷ []) (Bx0-342 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff134 ∷ Bx3-12 ∷ Toff134 ∷ CCZ134 ∷ Bx3-12 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 1 2 (Toff034 ∷ Sw01 ∷ []) (lem-nat-0-TOFF134 c4) ▸
       at 2 2 (Bx3-02 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·12⟩ c4) ▸
       at 3 2 (Toff034 ∷ Sw01 ∷ []) (lem-nat-0-TOFF134 c4) ▸
       at 4 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 5 2 (Bx3-02 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·12⟩ c4) ▸
       at 0 6 (Bx0-342 ∷ []) (refl) ▸ done


-- nat 0 BOX(3;1042): 8 steps
lem-nat-0-BOX⟨3·1042⟩ : WsL → ⟪ (Sw01 ∷ Bx3-1042 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0142 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·1042⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx3-1042 ∷ []) (Bx3-0142 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff301 ∷ Bx1-342 ∷ Toff301 ∷ CCZ013 ∷ Bx1-342 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw01 ∷ []) (sym (wl0100 c4)) ▸
       at 1 2 (Toff301 ∷ Sw01 ∷ []) (wl0115 c4) ▸
       at 2 2 (Bx0-342 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·342⟩ c4) ▸
       at 3 2 (Toff301 ∷ Sw01 ∷ []) (wl0115 c4) ▸
       at 4 2 (CCZ013 ∷ Sw01 ∷ []) (sym (wl0100 c4)) ▸
       at 5 2 (Bx0-342 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·342⟩ c4) ▸
       at 0 6 (Bx3-0142 ∷ []) (refl) ▸ done


-- nat 1 BOX(3;21): 3 steps
lem-nat-1-BOX⟨3·21⟩ : WsL → ⟪ (Sw12 ∷ Bx3-21 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-12 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·21⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-21 ∷ []) (Bx3-12 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ12 ∷ []) (refl) ▸
       at 0 2 (CZ12 ∷ Sw12 ∷ []) (sym (wl0109 c4)) ▸
       at 0 1 (Bx3-12 ∷ []) (refl) ▸ done


-- nat 1 BOX(2;341): 8 steps
lem-nat-1-BOX⟨2·341⟩ : WsL → ⟪ (Sw12 ∷ Bx2-341 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-342 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·341⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx2-341 ∷ []) (Bx1-342 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff234 ∷ Bx3-21 ∷ Toff234 ∷ CCZ234 ∷ Bx3-21 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0034 c4)) ▸
       at 1 2 (Toff134 ∷ Sw12 ∷ []) (wl0140 c4) ▸
       at 2 2 (Bx3-12 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·21⟩ c4) ▸
       at 3 2 (Toff134 ∷ Sw12 ∷ []) (wl0140 c4) ▸
       at 4 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0034 c4)) ▸
       at 5 2 (Bx3-12 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·21⟩ c4) ▸
       at 0 6 (Bx1-342 ∷ []) (refl) ▸ done


-- nat 1 BOX(3;2041): 8 steps
lem-nat-1-BOX⟨3·2041⟩ : WsL → ⟪ (Sw12 ∷ Bx3-2041 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1042 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·2041⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-2041 ∷ []) (Bx3-1042 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff302 ∷ Bx2-341 ∷ Toff302 ∷ CCZ023 ∷ Bx2-341 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 1 2 (Toff301 ∷ Sw12 ∷ []) (lem-nat-1-TOFF302 c4) ▸
       at 2 2 (Bx1-342 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·341⟩ c4) ▸
       at 3 2 (Toff301 ∷ Sw12 ∷ []) (lem-nat-1-TOFF302 c4) ▸
       at 4 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 5 2 (Bx1-342 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·341⟩ c4) ▸
       at 0 6 (Bx3-1042 ∷ []) (refl) ▸ done


-- nat 1 BOX(2;301): 8 steps
lem-nat-1-BOX⟨2·301⟩ : WsL → ⟪ (Sw12 ∷ Bx2-301 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-302 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·301⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx2-301 ∷ []) (Bx1-302 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff203 ∷ Bx3-21 ∷ Toff203 ∷ CCZ023 ∷ Bx3-21 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 1 2 (Toff103 ∷ Sw12 ∷ []) (lem-nat-1-TOFF203 c4) ▸
       at 2 2 (Bx3-12 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·21⟩ c4) ▸
       at 3 2 (Toff103 ∷ Sw12 ∷ []) (lem-nat-1-TOFF203 c4) ▸
       at 4 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 5 2 (Bx3-12 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·21⟩ c4) ▸
       at 0 6 (Bx1-302 ∷ []) (refl) ▸ done


-- nat 1 BOX(3;2401): 8 steps
lem-nat-1-BOX⟨3·2401⟩ : WsL → ⟪ (Sw12 ∷ Bx3-2401 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1402 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·2401⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-2401 ∷ []) (Bx3-1402 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff324 ∷ Bx2-301 ∷ Toff324 ∷ CCZ234 ∷ Bx2-301 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0034 c4)) ▸
       at 1 2 (Toff314 ∷ Sw12 ∷ []) (wl0063 c4) ▸
       at 2 2 (Bx1-302 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·301⟩ c4) ▸
       at 3 2 (Toff314 ∷ Sw12 ∷ []) (wl0063 c4) ▸
       at 4 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0034 c4)) ▸
       at 5 2 (Bx1-302 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·301⟩ c4) ▸
       at 0 6 (Bx3-1402 ∷ []) (refl) ▸ done


-- nat 0 BOX(0;342): 8 steps
lem-nat-0-BOX⟨0·342⟩ : WsL → ⟪ (Sw01 ∷ Bx0-342 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-342 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·342⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-342 ∷ []) (Bx1-342 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff034 ∷ Bx3-02 ∷ Toff034 ∷ CCZ034 ∷ Bx3-02 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4) ▸
       at 1 2 (Toff134 ∷ Sw01 ∷ []) (lem-nat-0-TOFF034 c4) ▸
       at 2 2 (Bx3-12 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·02⟩ c4) ▸
       at 3 2 (Toff134 ∷ Sw01 ∷ []) (lem-nat-0-TOFF034 c4) ▸
       at 4 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4) ▸
       at 5 2 (Bx3-12 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·02⟩ c4) ▸
       at 0 6 (Bx1-342 ∷ []) (refl) ▸ done


-- nat 0 BOX(3;0142): 8 steps
lem-nat-0-BOX⟨3·0142⟩ : WsL → ⟪ (Sw01 ∷ Bx3-0142 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1042 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·0142⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx3-0142 ∷ []) (Bx3-1042 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff301 ∷ Bx0-342 ∷ Toff301 ∷ CCZ013 ∷ Bx0-342 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw01 ∷ []) (sym (wl0100 c4)) ▸
       at 1 2 (Toff301 ∷ Sw01 ∷ []) (wl0115 c4) ▸
       at 2 2 (Bx1-342 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·342⟩ c4) ▸
       at 3 2 (Toff301 ∷ Sw01 ∷ []) (wl0115 c4) ▸
       at 4 2 (CCZ013 ∷ Sw01 ∷ []) (sym (wl0100 c4)) ▸
       at 5 2 (Bx1-342 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·342⟩ c4) ▸
       at 0 6 (Bx3-1042 ∷ []) (refl) ▸ done


-- nat 0 BOX(0;324): 8 steps
lem-nat-0-BOX⟨0·324⟩ : WsL → ⟪ (Sw01 ∷ Bx0-324 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-324 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·324⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-324 ∷ []) (Bx1-324 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff023 ∷ Bx3-04 ∷ Toff023 ∷ CCZ023 ∷ Bx3-04 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw01 ∷ []) (sym (wl0103 c4)) ▸
       at 1 2 (Toff123 ∷ Sw01 ∷ []) (wl0108 c4) ▸
       at 2 2 (Bx3-14 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·04⟩ c4) ▸
       at 3 2 (Toff123 ∷ Sw01 ∷ []) (wl0108 c4) ▸
       at 4 2 (CCZ123 ∷ Sw01 ∷ []) (sym (wl0103 c4)) ▸
       at 5 2 (Bx3-14 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·04⟩ c4) ▸
       at 0 6 (Bx1-324 ∷ []) (refl) ▸ done


-- nat 0 BOX(3;0124): 8 steps
lem-nat-0-BOX⟨3·0124⟩ : WsL → ⟪ (Sw01 ∷ Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1024 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·0124⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx3-0124 ∷ []) (Bx3-1024 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff301 ∷ Bx0-324 ∷ Toff301 ∷ CCZ013 ∷ Bx0-324 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw01 ∷ []) (sym (wl0100 c4)) ▸
       at 1 2 (Toff301 ∷ Sw01 ∷ []) (wl0115 c4) ▸
       at 2 2 (Bx1-324 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·324⟩ c4) ▸
       at 3 2 (Toff301 ∷ Sw01 ∷ []) (wl0115 c4) ▸
       at 4 2 (CCZ013 ∷ Sw01 ∷ []) (sym (wl0100 c4)) ▸
       at 5 2 (Bx1-324 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·324⟩ c4) ▸
       at 0 6 (Bx3-1024 ∷ []) (refl) ▸ done


-- nat 1 BOX(3;14): 3 steps
lem-nat-1-BOX⟨3·14⟩ : WsL → ⟪ (Sw12 ∷ Bx3-14 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-24 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·14⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-14 ∷ []) (Bx3-24 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ14 ∷ []) (refl) ▸
       at 0 2 (CZ24 ∷ Sw12 ∷ []) (sym (wl0089 c4)) ▸
       at 0 1 (Bx3-24 ∷ []) (refl) ▸ done


-- nat 1 BOX(1;324): 8 steps
lem-nat-1-BOX⟨1·324⟩ : WsL → ⟪ (Sw12 ∷ Bx1-324 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-314 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·324⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx1-324 ∷ []) (Bx2-314 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff123 ∷ Bx3-14 ∷ Toff123 ∷ CCZ123 ∷ Bx3-14 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw12 ∷ []) (sym (wl0111 c4)) ▸
       at 1 2 (Toff213 ∷ Sw12 ∷ []) (wl0146 c4) ▸
       at 2 2 (Bx3-24 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·14⟩ c4) ▸
       at 3 2 (Toff213 ∷ Sw12 ∷ []) (wl0146 c4) ▸
       at 4 2 (CCZ123 ∷ Sw12 ∷ []) (sym (wl0111 c4)) ▸
       at 5 2 (Bx3-24 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·14⟩ c4) ▸
       at 0 6 (Bx2-314 ∷ []) (refl) ▸ done


-- nat 1 BOX(3;1024): 8 steps
lem-nat-1-BOX⟨3·1024⟩ : WsL → ⟪ (Sw12 ∷ Bx3-1024 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2014 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·1024⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-1024 ∷ []) (Bx3-2014 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff301 ∷ Bx1-324 ∷ Toff301 ∷ CCZ013 ∷ Bx1-324 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 1 2 (Toff302 ∷ Sw12 ∷ []) (lem-nat-1-TOFF301 c4) ▸
       at 2 2 (Bx2-314 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·324⟩ c4) ▸
       at 3 2 (Toff302 ∷ Sw12 ∷ []) (lem-nat-1-TOFF301 c4) ▸
       at 4 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 5 2 (Bx2-314 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·324⟩ c4) ▸
       at 0 6 (Bx3-2014 ∷ []) (refl) ▸ done


-- nat 1 BOX(3;24): 3 steps
lem-nat-1-BOX⟨3·24⟩ : WsL → ⟪ (Sw12 ∷ Bx3-24 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-14 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·24⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-24 ∷ []) (Bx3-14 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ24 ∷ []) (refl) ▸
       at 0 2 (CZ14 ∷ Sw12 ∷ []) (sym (wl0005 c4)) ▸
       at 0 1 (Bx3-14 ∷ []) (refl) ▸ done


-- nat 1 BOX(2;314): 8 steps
lem-nat-1-BOX⟨2·314⟩ : WsL → ⟪ (Sw12 ∷ Bx2-314 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-324 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·314⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx2-314 ∷ []) (Bx1-324 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff213 ∷ Bx3-24 ∷ Toff213 ∷ CCZ123 ∷ Bx3-24 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw12 ∷ []) (sym (wl0111 c4)) ▸
       at 1 2 (Toff123 ∷ Sw12 ∷ []) (wl0112 c4) ▸
       at 2 2 (Bx3-14 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·24⟩ c4) ▸
       at 3 2 (Toff123 ∷ Sw12 ∷ []) (wl0112 c4) ▸
       at 4 2 (CCZ123 ∷ Sw12 ∷ []) (sym (wl0111 c4)) ▸
       at 5 2 (Bx3-14 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·24⟩ c4) ▸
       at 0 6 (Bx1-324 ∷ []) (refl) ▸ done


-- nat 1 BOX(3;2014): 8 steps
lem-nat-1-BOX⟨3·2014⟩ : WsL → ⟪ (Sw12 ∷ Bx3-2014 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1024 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·2014⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-2014 ∷ []) (Bx3-1024 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff302 ∷ Bx2-314 ∷ Toff302 ∷ CCZ023 ∷ Bx2-314 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 1 2 (Toff301 ∷ Sw12 ∷ []) (lem-nat-1-TOFF302 c4) ▸
       at 2 2 (Bx1-324 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·314⟩ c4) ▸
       at 3 2 (Toff301 ∷ Sw12 ∷ []) (lem-nat-1-TOFF302 c4) ▸
       at 4 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 5 2 (Bx1-324 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·314⟩ c4) ▸
       at 0 6 (Bx3-1024 ∷ []) (refl) ▸ done


-- nat 2 BOX(2;31): 3 steps
lem-nat-2-BOX⟨2·31⟩ : WsL → ⟪ (Sw23 ∷ Bx2-31 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-21 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·31⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx2-31 ∷ []) (Bx3-21 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ13 ∷ []) (refl) ▸
       at 0 2 (CZ12 ∷ Sw23 ∷ []) (lem-nat-2-CZ13 c4) ▸
       at 0 1 (Bx3-21 ∷ []) (refl) ▸ done


-- nat 2 BOX(3;201): 8 steps
lem-nat-2-BOX⟨3·201⟩ : WsL → ⟪ (Sw23 ∷ Bx3-201 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-301 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·201⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx3-201 ∷ []) (Bx2-301 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff302 ∷ Bx2-31 ∷ Toff302 ∷ CCZ023 ∷ Bx2-31 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw23 ∷ []) (sym (wl0065 c4)) ▸
       at 1 2 (Toff203 ∷ Sw23 ∷ []) (wl0066 c4) ▸
       at 2 2 (Bx3-21 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·31⟩ c4) ▸
       at 3 2 (Toff203 ∷ Sw23 ∷ []) (wl0066 c4) ▸
       at 4 2 (CCZ023 ∷ Sw23 ∷ []) (sym (wl0065 c4)) ▸
       at 5 2 (Bx3-21 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·31⟩ c4) ▸
       at 0 6 (Bx2-301 ∷ []) (refl) ▸ done


-- nat 2 BOX(2;3401): 8 steps
lem-nat-2-BOX⟨2·3401⟩ : WsL → ⟪ (Sw23 ∷ Bx2-3401 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2401 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·3401⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx2-3401 ∷ []) (Bx3-2401 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff234 ∷ Bx3-201 ∷ Toff234 ∷ CCZ234 ∷ Bx3-201 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw23 ∷ []) (sym (wl0086 c4)) ▸
       at 1 2 (Toff324 ∷ Sw23 ∷ []) (wl0127 c4) ▸
       at 2 2 (Bx2-301 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·201⟩ c4) ▸
       at 3 2 (Toff324 ∷ Sw23 ∷ []) (wl0127 c4) ▸
       at 4 2 (CCZ234 ∷ Sw23 ∷ []) (sym (wl0086 c4)) ▸
       at 5 2 (Bx2-301 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·201⟩ c4) ▸
       at 0 6 (Bx3-2401 ∷ []) (refl) ▸ done


-- nat 0 SBOX(0;1;2;3): 3 steps
lem-nat-0-SBOX⟨0·1·2·3⟩ : WsL → ⟪ (Sw01 ∷ Sb0-1-2-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-2-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨0·1·2·3⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb0-1-2-3 ∷ []) (Sb1-0-2-3 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS12 ∷ []) (refl) ▸
       at 0 2 (CS02 ∷ Sw01 ∷ []) (sym (wl0035 c4)) ▸
       at 0 1 (Sb1-0-2-3 ∷ []) (refl) ▸ done


-- nat 0 SBOXd(0;1;2;3): 3 steps
lem-nat-0-SBOXd⟨0·1·2·3⟩ : WsL → ⟪ (Sw01 ∷ Sb⁻0-1-2-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-2-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨0·1·2·3⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻0-1-2-3 ∷ []) (Sb⁻1-0-2-3 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS12⁻ ∷ []) (refl) ▸
       at 0 2 (CS02⁻ ∷ Sw01 ∷ []) (sym (wl0036 c4)) ▸
       at 0 1 (Sb⁻1-0-2-3 ∷ []) (refl) ▸ done


-- nat 0 SBOX(0;1;43;2): 7 steps
lem-nat-0-SBOX⟨0·1·43·2⟩ : WsL → ⟪ (Sw01 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-43-2 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨0·1·43·2⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb0-1-43-2 ∷ []) (Sb1-0-43-2 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx0-1432 ∷ Toff234 ∷ Sb0-1-2-3 ∷ Toff234 ∷ Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 0 2 (Bx1-0432 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1432⟩ c4) ▸
       at 1 2 (Toff234 ∷ Sw01 ∷ []) (c₂ (Swap) (Toff)) ▸
       at 2 2 (Sb1-0-2-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·2·3⟩ c4) ▸
       at 3 2 (Toff234 ∷ Sw01 ∷ []) (c₂ (Swap) (Toff)) ▸
       at 4 2 (Sb⁻1-0-2-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨0·1·2·3⟩ c4) ▸
       at 0 5 (Sb1-0-43-2 ∷ []) (refl) ▸ done


-- nat 1 BOX(0;42): 3 steps
lem-nat-1-BOX⟨0·42⟩ : WsL → ⟪ (Sw12 ∷ Bx0-42 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-41 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·42⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-42 ∷ []) (Bx0-41 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ24 ∷ []) (refl) ▸
       at 0 2 (CZ14 ∷ Sw12 ∷ []) (sym (wl0005 c4)) ▸
       at 0 1 (Bx0-41 ∷ []) (refl) ▸ done


-- nat 1 BOX(4;032): 8 steps
lem-nat-1-BOX⟨4·032⟩ : WsL → ⟪ (Sw12 ∷ Bx4-032 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-031 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·032⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx4-032 ∷ []) (Bx4-031 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff403 ∷ Bx0-42 ∷ Toff403 ∷ CCZ034 ∷ Bx0-42 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 1 2 (Toff403 ∷ Sw12 ∷ []) (lem-nat-1-TOFF403 c4) ▸
       at 2 2 (Bx0-41 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·42⟩ c4) ▸
       at 3 2 (Toff403 ∷ Sw12 ∷ []) (lem-nat-1-TOFF403 c4) ▸
       at 4 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 5 2 (Bx0-41 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·42⟩ c4) ▸
       at 0 6 (Bx4-031 ∷ []) (refl) ▸ done


-- nat 1 BOX(0;4132): 8 steps
lem-nat-1-BOX⟨0·4132⟩ : WsL → ⟪ (Sw12 ∷ Bx0-4132 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4231 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·4132⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-4132 ∷ []) (Bx0-4231 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff014 ∷ Bx4-032 ∷ Toff014 ∷ CCZ014 ∷ Bx4-032 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 1 2 (Toff024 ∷ Sw12 ∷ []) (lem-nat-1-TOFF014 c4) ▸
       at 2 2 (Bx4-031 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·032⟩ c4) ▸
       at 3 2 (Toff024 ∷ Sw12 ∷ []) (lem-nat-1-TOFF014 c4) ▸
       at 4 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 5 2 (Bx4-031 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·032⟩ c4) ▸
       at 0 6 (Bx0-4231 ∷ []) (refl) ▸ done

