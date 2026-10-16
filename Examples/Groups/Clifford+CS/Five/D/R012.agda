{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.R012 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (WsL ; wl0001 ; wl0002 ; wl0003 ; wl0006 ; wl0007 ; wl0008 ; wl0009 ; wl0011 ; wl0012 ; wl0016 ; wl0017 ; wl0018 ; wl0019 ; wl0021 ; wl0022 ; wl0023 ; wl0024 ; wl0027 ; wl0028 ; wl0029 ; wl0033 ; wl0034 ; wl0037 ; wl0038 ; wl0039 ; wl0040 ; wl0042 ; wl0043 ; wl0044 ; wl0045 ; wl0047 ; wl0050 ; wl0051 ; wl0064 ; wl0065 ; wl0078 ; wl0084 ; wl0085 ; wl0086 ; wl0090 ; wl0091 ; wl0095 ; wl0099 ; wl0100 ; wl0101 ; wl0103 ; wl0109 ; wl0110 ; wl0113 ; wl0114 ; wl0115 ; wl0116 ; wl0126 ; wl0128 ; wl0129 ; wl0130 ; wl0134 ; wl0135 ; wl0136 ; wl0137 ; wl0138 ; wl0139 ; wl0140 ; wl0143 ; wl0144 ; wl0152 ; wl0153 ; wl0154 ; wl0155)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-nat-1-BOX⟨0·2134⟩ ; lem-nat-1-CCZ023 ; lem-nat-1-CCZ024 ; lem-nat-1-TOFF024 ; lem-nat-2-CCZ012 ; lem-nat-2-CCZ013 ; lem-nat-2-CCZ034 ; lem-nat-2-TOFF102 ; lem-nat-2-TOFF301 ; lem-nat-3-CCZ014 ; lem-nat-3-CZ13 ; lem-nat-3-TOFF104)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-0-CCZ124 ; lem-nat-1-CCZ013 ; lem-nat-1-CCZ014 ; lem-nat-1-TOFF103 ; lem-nat-1-TOFF301 ; lem-nat-1-TOFF302 ; lem-nat-2-CCZ134 ; lem-nat-2-TOFF201 ; lem-nat-2-TOFF204 ; lem-nat-3-CCZ023 ; lem-nat-3-TOFF203)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-0-BOX⟨1·43⟩ ; lem-nat-0-CCZ014 ; lem-nat-0-CCZ034 ; lem-nat-0-CCZ134 ; lem-nat-0-TOFF304 ; lem-nat-0-TOFF403 ; lem-nat-1-TOFF204 ; lem-nat-3-CZ23)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-0-BOX⟨3·40⟩ ; lem-nat-0-TOFF214 ; lem-nat-0-TOFF413 ; lem-nat-1-BOX⟨0·1234⟩ ; lem-nat-1-TOFF304 ; lem-nat-2-TOFF104 ; lem-nat-3-TOFF302)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-0-TOFF401 ; lem-nat-1-CZ04 ; lem-nat-1-TOFF023 ; lem-nat-1-TOFF401 ; lem-nat-2-CCZ014 ; lem-nat-3-CCZ123 ; lem-nat-3-CCZ124 ; lem-nat-3-CZ03 ; lem-nat-3-CZ04)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-0-BOX⟨0·2134⟩ ; lem-nat-0-BOX⟨1·2034⟩ ; lem-nat-2-CS12 ; lem-nat-2-CSd12 ; lem-nat-2-CZ12 ; lem-nat-3-CS13 ; lem-nat-3-CSd13 ; lem-nat-3-CZ24)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-0-BOX⟨2·1403⟩ ; lem-nat-0-CS04 ; lem-nat-0-TOFF134 ; lem-nat-1-BOX⟨2·41⟩ ; lem-nat-1-CS04 ; lem-nat-2-TOFF403 ; lem-nat-3-CS24)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-nat-0-BOX⟨0·32⟩ ; lem-nat-0-BOX⟨1·32⟩ ; lem-nat-0-TOFF034 ; lem-nat-1-BOX⟨1·32⟩ ; lem-nat-1-BOX⟨2·31⟩ ; lem-nat-1-CSd04 ; lem-nat-3-TOFF401)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-0-CSd04 ; lem-nat-1-TOFF402 ; lem-nat-2-TOFF401)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-nat-0-BOX⟨2·30⟩ ; lem-nat-0-BOX⟨2·31⟩ ; lem-nat-0-TOFF124 ; lem-nat-3-TOFF123 ; lem-nat-3-TOFF124)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-nat-1-BOX⟨1·23⟩ ; lem-nat-2-TOFF134)
-- nat 2 BOX(1;24): 3 steps
lem-nat-2-BOX⟨1·24⟩ : WsL → ⟪ (Sw23 ∷ Bx1-24 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-34 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·24⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx1-24 ∷ []) (Bx1-34 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ24 ∷ []) (refl) ▸
       at 0 2 (CZ34 ∷ Sw23 ∷ []) (sym (wl0028 c4)) ▸
       at 0 1 (Bx1-34 ∷ []) (refl) ▸ done


-- nat 2 BOX(2;104): 8 steps
lem-nat-2-BOX⟨2·104⟩ : WsL → ⟪ (Sw23 ∷ Bx2-104 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-104 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·104⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx2-104 ∷ []) (Bx3-104 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff201 ∷ Bx1-24 ∷ Toff201 ∷ CCZ012 ∷ Bx1-24 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 1 2 (Toff301 ∷ Sw23 ∷ []) (lem-nat-2-TOFF201 c4) ▸
       at 2 2 (Bx1-34 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·24⟩ c4) ▸
       at 3 2 (Toff301 ∷ Sw23 ∷ []) (lem-nat-2-TOFF201 c4) ▸
       at 4 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 5 2 (Bx1-34 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·24⟩ c4) ▸
       at 0 6 (Bx3-104 ∷ []) (refl) ▸ done


-- nat 2 BOX(1;2304): 8 steps
lem-nat-2-BOX⟨1·2304⟩ : WsL → ⟪ (Sw23 ∷ Bx1-2304 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3204 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·2304⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx1-2304 ∷ []) (Bx1-3204 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff123 ∷ Bx2-104 ∷ Toff123 ∷ CCZ123 ∷ Bx2-104 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw23 ∷ []) (sym (wl0113 c4)) ▸
       at 1 2 (Toff123 ∷ Sw23 ∷ []) (wl0114 c4) ▸
       at 2 2 (Bx3-104 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·104⟩ c4) ▸
       at 3 2 (Toff123 ∷ Sw23 ∷ []) (wl0114 c4) ▸
       at 4 2 (CCZ123 ∷ Sw23 ∷ []) (sym (wl0113 c4)) ▸
       at 5 2 (Bx3-104 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·104⟩ c4) ▸
       at 0 6 (Bx1-3204 ∷ []) (refl) ▸ done


-- nat 2 BOX(1;34): 3 steps
lem-nat-2-BOX⟨1·34⟩ : WsL → ⟪ (Sw23 ∷ Bx1-34 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-24 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·34⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx1-34 ∷ []) (Bx1-24 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ34 ∷ []) (refl) ▸
       at 0 2 (CZ24 ∷ Sw23 ∷ []) (sym (wl0027 c4)) ▸
       at 0 1 (Bx1-24 ∷ []) (refl) ▸ done


-- nat 2 BOX(3;104): 8 steps
lem-nat-2-BOX⟨3·104⟩ : WsL → ⟪ (Sw23 ∷ Bx3-104 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-104 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·104⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx3-104 ∷ []) (Bx2-104 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff301 ∷ Bx1-34 ∷ Toff301 ∷ CCZ013 ∷ Bx1-34 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 1 2 (Toff201 ∷ Sw23 ∷ []) (lem-nat-2-TOFF301 c4) ▸
       at 2 2 (Bx1-24 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·34⟩ c4) ▸
       at 3 2 (Toff201 ∷ Sw23 ∷ []) (lem-nat-2-TOFF301 c4) ▸
       at 4 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 5 2 (Bx1-24 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·34⟩ c4) ▸
       at 0 6 (Bx2-104 ∷ []) (refl) ▸ done


-- nat 2 BOX(1;3204): 8 steps
lem-nat-2-BOX⟨1·3204⟩ : WsL → ⟪ (Sw23 ∷ Bx1-3204 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2304 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·3204⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx1-3204 ∷ []) (Bx1-2304 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff123 ∷ Bx3-104 ∷ Toff123 ∷ CCZ123 ∷ Bx3-104 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw23 ∷ []) (sym (wl0113 c4)) ▸
       at 1 2 (Toff123 ∷ Sw23 ∷ []) (wl0114 c4) ▸
       at 2 2 (Bx2-104 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·104⟩ c4) ▸
       at 3 2 (Toff123 ∷ Sw23 ∷ []) (wl0114 c4) ▸
       at 4 2 (CCZ123 ∷ Sw23 ∷ []) (sym (wl0113 c4)) ▸
       at 5 2 (Bx2-104 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·104⟩ c4) ▸
       at 0 6 (Bx1-2304 ∷ []) (refl) ▸ done


-- nat 3 BOX(1;23): 3 steps
lem-nat-3-BOX⟨1·23⟩ : WsL → ⟪ (Sw34 ∷ Bx1-23 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-24 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨1·23⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx1-23 ∷ []) (Bx1-24 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CZ23 ∷ []) (refl) ▸
       at 0 2 (CZ24 ∷ Sw34 ∷ []) (lem-nat-3-CZ23 c4) ▸
       at 0 1 (Bx1-24 ∷ []) (refl) ▸ done


-- nat 3 BOX(2;103): 8 steps
lem-nat-3-BOX⟨2·103⟩ : WsL → ⟪ (Sw34 ∷ Bx2-103 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-104 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨2·103⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx2-103 ∷ []) (Bx2-104 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff201 ∷ Bx1-23 ∷ Toff201 ∷ CCZ012 ∷ Bx1-23 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 1 2 (Toff201 ∷ Sw34 ∷ []) (sym (c₃ (Toffᵗ) (Swap))) ▸
       at 2 2 (Bx1-24 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·23⟩ c4) ▸
       at 3 2 (Toff201 ∷ Sw34 ∷ []) (sym (c₃ (Toffᵗ) (Swap))) ▸
       at 4 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 5 2 (Bx1-24 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·23⟩ c4) ▸
       at 0 6 (Bx2-104 ∷ []) (refl) ▸ done


-- nat 3 BOX(1;2403): 8 steps
lem-nat-3-BOX⟨1·2403⟩ : WsL → ⟪ (Sw34 ∷ Bx1-2403 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2304 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨1·2403⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx1-2403 ∷ []) (Bx1-2304 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff124 ∷ Bx2-103 ∷ Toff124 ∷ CCZ124 ∷ Bx2-103 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw34 ∷ []) (lem-nat-3-CCZ124 c4) ▸
       at 1 2 (Toff123 ∷ Sw34 ∷ []) (lem-nat-3-TOFF124 c4) ▸
       at 2 2 (Bx2-104 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·103⟩ c4) ▸
       at 3 2 (Toff123 ∷ Sw34 ∷ []) (lem-nat-3-TOFF124 c4) ▸
       at 4 2 (CCZ123 ∷ Sw34 ∷ []) (lem-nat-3-CCZ124 c4) ▸
       at 5 2 (Bx2-104 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·103⟩ c4) ▸
       at 0 6 (Bx1-2304 ∷ []) (refl) ▸ done


-- nat 3 BOX(1;24): 3 steps
lem-nat-3-BOX⟨1·24⟩ : WsL → ⟪ (Sw34 ∷ Bx1-24 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-23 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨1·24⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx1-24 ∷ []) (Bx1-23 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CZ24 ∷ []) (refl) ▸
       at 0 2 (CZ23 ∷ Sw34 ∷ []) (lem-nat-3-CZ24 c4) ▸
       at 0 1 (Bx1-23 ∷ []) (refl) ▸ done


-- nat 3 BOX(2;104): 8 steps
lem-nat-3-BOX⟨2·104⟩ : WsL → ⟪ (Sw34 ∷ Bx2-104 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-103 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨2·104⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx2-104 ∷ []) (Bx2-103 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff201 ∷ Bx1-24 ∷ Toff201 ∷ CCZ012 ∷ Bx1-24 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 1 2 (Toff201 ∷ Sw34 ∷ []) (sym (c₃ (Toffᵗ) (Swap))) ▸
       at 2 2 (Bx1-23 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·24⟩ c4) ▸
       at 3 2 (Toff201 ∷ Sw34 ∷ []) (sym (c₃ (Toffᵗ) (Swap))) ▸
       at 4 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 5 2 (Bx1-23 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·24⟩ c4) ▸
       at 0 6 (Bx2-103 ∷ []) (refl) ▸ done


-- nat 3 BOX(1;2304): 8 steps
lem-nat-3-BOX⟨1·2304⟩ : WsL → ⟪ (Sw34 ∷ Bx1-2304 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2403 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨1·2304⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx1-2304 ∷ []) (Bx1-2403 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff123 ∷ Bx2-104 ∷ Toff123 ∷ CCZ123 ∷ Bx2-104 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw34 ∷ []) (lem-nat-3-CCZ123 c4) ▸
       at 1 2 (Toff124 ∷ Sw34 ∷ []) (lem-nat-3-TOFF123 c4) ▸
       at 2 2 (Bx2-103 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·104⟩ c4) ▸
       at 3 2 (Toff124 ∷ Sw34 ∷ []) (lem-nat-3-TOFF123 c4) ▸
       at 4 2 (CCZ124 ∷ Sw34 ∷ []) (lem-nat-3-CCZ123 c4) ▸
       at 5 2 (Bx2-103 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·104⟩ c4) ▸
       at 0 6 (Bx1-2403 ∷ []) (refl) ▸ done


-- nat 1 BOX(2;13): 3 steps
lem-nat-1-BOX⟨2·13⟩ : WsL → ⟪ (Sw12 ∷ Bx2-13 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-23 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·13⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx2-13 ∷ []) (Bx1-23 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ13 ∷ []) (refl) ▸
       at 0 2 (CZ23 ∷ Sw12 ∷ []) (sym (wl0029 c4)) ▸
       at 0 1 (Bx1-23 ∷ []) (refl) ▸ done


-- nat 1 BOX(1;203): 8 steps
lem-nat-1-BOX⟨1·203⟩ : WsL → ⟪ (Sw12 ∷ Bx1-203 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-103 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·203⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx1-203 ∷ []) (Bx2-103 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff102 ∷ Bx2-13 ∷ Toff102 ∷ CCZ012 ∷ Bx2-13 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw12 ∷ []) (sym (wl0037 c4)) ▸
       at 1 2 (Toff201 ∷ Sw12 ∷ []) (wl0047 c4) ▸
       at 2 2 (Bx1-23 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·13⟩ c4) ▸
       at 3 2 (Toff201 ∷ Sw12 ∷ []) (wl0047 c4) ▸
       at 4 2 (CCZ012 ∷ Sw12 ∷ []) (sym (wl0037 c4)) ▸
       at 5 2 (Bx1-23 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·13⟩ c4) ▸
       at 0 6 (Bx2-103 ∷ []) (refl) ▸ done


-- nat 1 BOX(2;1403): 8 steps
lem-nat-1-BOX⟨2·1403⟩ : WsL → ⟪ (Sw12 ∷ Bx2-1403 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2403 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·1403⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx2-1403 ∷ []) (Bx1-2403 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff214 ∷ Bx1-203 ∷ Toff214 ∷ CCZ124 ∷ Bx1-203 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw12 ∷ []) (sym (wl0078 c4)) ▸
       at 1 2 (Toff124 ∷ Sw12 ∷ []) (wl0126 c4) ▸
       at 2 2 (Bx2-103 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·203⟩ c4) ▸
       at 3 2 (Toff124 ∷ Sw12 ∷ []) (wl0126 c4) ▸
       at 4 2 (CCZ124 ∷ Sw12 ∷ []) (sym (wl0078 c4)) ▸
       at 5 2 (Bx2-103 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·203⟩ c4) ▸
       at 0 6 (Bx1-2403 ∷ []) (refl) ▸ done


-- nat 1 BOX(2;103): 8 steps
lem-nat-1-BOX⟨2·103⟩ : WsL → ⟪ (Sw12 ∷ Bx2-103 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-203 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·103⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx2-103 ∷ []) (Bx1-203 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff201 ∷ Bx1-23 ∷ Toff201 ∷ CCZ012 ∷ Bx1-23 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw12 ∷ []) (sym (wl0037 c4)) ▸
       at 1 2 (Toff102 ∷ Sw12 ∷ []) (wl0044 c4) ▸
       at 2 2 (Bx2-13 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·23⟩ c4) ▸
       at 3 2 (Toff102 ∷ Sw12 ∷ []) (wl0044 c4) ▸
       at 4 2 (CCZ012 ∷ Sw12 ∷ []) (sym (wl0037 c4)) ▸
       at 5 2 (Bx2-13 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·23⟩ c4) ▸
       at 0 6 (Bx1-203 ∷ []) (refl) ▸ done


-- nat 1 BOX(1;2403): 8 steps
lem-nat-1-BOX⟨1·2403⟩ : WsL → ⟪ (Sw12 ∷ Bx1-2403 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1403 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·2403⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx1-2403 ∷ []) (Bx2-1403 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff124 ∷ Bx2-103 ∷ Toff124 ∷ CCZ124 ∷ Bx2-103 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw12 ∷ []) (sym (wl0078 c4)) ▸
       at 1 2 (Toff214 ∷ Sw12 ∷ []) (wl0095 c4) ▸
       at 2 2 (Bx1-203 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·103⟩ c4) ▸
       at 3 2 (Toff214 ∷ Sw12 ∷ []) (wl0095 c4) ▸
       at 4 2 (CCZ124 ∷ Sw12 ∷ []) (sym (wl0078 c4)) ▸
       at 5 2 (Bx1-203 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·103⟩ c4) ▸
       at 0 6 (Bx2-1403 ∷ []) (refl) ▸ done


-- nat 0 SBOX(0;2;4;3): 2 steps
lem-nat-0-SBOX⟨0·2·4·3⟩ : WsL → ⟪ (Sw01 ∷ Sb0-2-4-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-4-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨0·2·4·3⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb0-2-4-3 ∷ []) (Sb1-2-4-3 ∷ Sw01 ∷ [])
  b0 = at 0 2 (Sb0-2-4-3 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑)) ▸
       at 0 1 (Sb1-2-4-3 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 SBOXd(0;2;4;3): 2 steps
lem-nat-0-SBOXd⟨0·2·4·3⟩ : WsL → ⟪ (Sw01 ∷ Sb⁻0-2-4-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-2-4-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨0·2·4·3⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻0-2-4-3 ∷ []) (Sb⁻1-2-4-3 ∷ Sw01 ∷ [])
  b0 = at 0 2 (Sb⁻0-2-4-3 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • (CS • CS • CS) • Swap ↑)) ▸
       at 0 1 (Sb⁻1-2-4-3 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 SBOX(0;2;13;4): 7 steps
lem-nat-0-SBOX⟨0·2·13·4⟩ : WsL → ⟪ (Sw01 ∷ Sb0-2-13-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-03-4 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨0·2·13·4⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb0-2-13-4 ∷ []) (Sb1-2-03-4 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx0-2134 ∷ Toff413 ∷ Sb0-2-4-3 ∷ Toff413 ∷ Sb⁻0-2-4-3 ∷ []) (refl) ▸
       at 0 2 (Bx1-2034 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·2134⟩ c4) ▸
       at 1 2 (Toff403 ∷ Sw01 ∷ []) (lem-nat-0-TOFF413 c4) ▸
       at 2 2 (Sb1-2-4-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·2·4·3⟩ c4) ▸
       at 3 2 (Toff403 ∷ Sw01 ∷ []) (lem-nat-0-TOFF413 c4) ▸
       at 4 2 (Sb⁻1-2-4-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨0·2·4·3⟩ c4) ▸
       at 0 5 (Sb1-2-03-4 ∷ []) (refl) ▸ done


-- nat 0 SBOX(1;2;4;3): 2 steps
lem-nat-0-SBOX⟨1·2·4·3⟩ : WsL → ⟪ (Sw01 ∷ Sb1-2-4-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-4-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨1·2·4·3⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb1-2-4-3 ∷ []) (Sb0-2-4-3 ∷ Sw01 ∷ [])
  b0 = at 0 2 (Sb1-2-4-3 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑)) ▸
       at 0 1 (Sb0-2-4-3 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 SBOXd(1;2;4;3): 2 steps
lem-nat-0-SBOXd⟨1·2·4·3⟩ : WsL → ⟪ (Sw01 ∷ Sb⁻1-2-4-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-2-4-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨1·2·4·3⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻1-2-4-3 ∷ []) (Sb⁻0-2-4-3 ∷ Sw01 ∷ [])
  b0 = at 0 2 (Sb⁻1-2-4-3 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • (CS • CS • CS) • Swap ↑)) ▸
       at 0 1 (Sb⁻0-2-4-3 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 SBOX(1;2;03;4): 7 steps
lem-nat-0-SBOX⟨1·2·03·4⟩ : WsL → ⟪ (Sw01 ∷ Sb1-2-03-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-13-4 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨1·2·03·4⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb1-2-03-4 ∷ []) (Sb0-2-13-4 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx1-2034 ∷ Toff403 ∷ Sb1-2-4-3 ∷ Toff403 ∷ Sb⁻1-2-4-3 ∷ []) (refl) ▸
       at 0 2 (Bx0-2134 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·2034⟩ c4) ▸
       at 1 2 (Toff413 ∷ Sw01 ∷ []) (lem-nat-0-TOFF403 c4) ▸
       at 2 2 (Sb0-2-4-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·2·4·3⟩ c4) ▸
       at 3 2 (Toff413 ∷ Sw01 ∷ []) (lem-nat-0-TOFF403 c4) ▸
       at 4 2 (Sb⁻0-2-4-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·2·4·3⟩ c4) ▸
       at 0 5 (Sb0-2-13-4 ∷ []) (refl) ▸ done


-- nat 1 SBOX(0;1;4;3): 3 steps
lem-nat-1-SBOX⟨0·1·4·3⟩ : WsL → ⟪ (Sw12 ∷ Sb0-1-4-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-4-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨0·1·4·3⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb0-1-4-3 ∷ []) (Sb0-2-4-3 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS14 ∷ []) (refl) ▸
       at 0 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0008 c4)) ▸
       at 0 1 (Sb0-2-4-3 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(0;1;4;3): 3 steps
lem-nat-1-SBOXd⟨0·1·4·3⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻0-1-4-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-2-4-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨0·1·4·3⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻0-1-4-3 ∷ []) (Sb⁻0-2-4-3 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS14⁻ ∷ []) (refl) ▸
       at 0 2 (CS24⁻ ∷ Sw12 ∷ []) (sym (wl0009 c4)) ▸
       at 0 1 (Sb⁻0-2-4-3 ∷ []) (refl) ▸ done


-- nat 1 SBOX(0;1;23;4): 7 steps
lem-nat-1-SBOX⟨0·1·23·4⟩ : WsL → ⟪ (Sw12 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-13-4 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨0·1·23·4⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb0-1-23-4 ∷ []) (Sb0-2-13-4 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 0 2 (Bx0-2134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1234⟩ c4) ▸
       at 1 2 (Toff413 ∷ Sw12 ∷ []) (wl0091 c4) ▸
       at 2 2 (Sb0-2-4-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·4·3⟩ c4) ▸
       at 3 2 (Toff413 ∷ Sw12 ∷ []) (wl0091 c4) ▸
       at 4 2 (Sb⁻0-2-4-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨0·1·4·3⟩ c4) ▸
       at 0 5 (Sb0-2-13-4 ∷ []) (refl) ▸ done


-- nat 1 SBOX(0;2;4;3): 3 steps
lem-nat-1-SBOX⟨0·2·4·3⟩ : WsL → ⟪ (Sw12 ∷ Sb0-2-4-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-4-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨0·2·4·3⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb0-2-4-3 ∷ []) (Sb0-1-4-3 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS24 ∷ []) (refl) ▸
       at 0 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0017 c4)) ▸
       at 0 1 (Sb0-1-4-3 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(0;2;4;3): 3 steps
lem-nat-1-SBOXd⟨0·2·4·3⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻0-2-4-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-4-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨0·2·4·3⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻0-2-4-3 ∷ []) (Sb⁻0-1-4-3 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS24⁻ ∷ []) (refl) ▸
       at 0 2 (CS14⁻ ∷ Sw12 ∷ []) (sym (wl0018 c4)) ▸
       at 0 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸ done


-- nat 1 SBOX(0;2;13;4): 7 steps
lem-nat-1-SBOX⟨0·2·13·4⟩ : WsL → ⟪ (Sw12 ∷ Sb0-2-13-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-23-4 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨0·2·13·4⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb0-2-13-4 ∷ []) (Sb0-1-23-4 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx0-2134 ∷ Toff413 ∷ Sb0-2-4-3 ∷ Toff413 ∷ Sb⁻0-2-4-3 ∷ []) (refl) ▸
       at 0 2 (Bx0-1234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2134⟩ c4) ▸
       at 1 2 (Toff423 ∷ Sw12 ∷ []) (wl0085 c4) ▸
       at 2 2 (Sb0-1-4-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·4·3⟩ c4) ▸
       at 3 2 (Toff423 ∷ Sw12 ∷ []) (wl0085 c4) ▸
       at 4 2 (Sb⁻0-1-4-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨0·2·4·3⟩ c4) ▸
       at 0 5 (Sb0-1-23-4 ∷ []) (refl) ▸ done


-- nat 0 SBOX(2;1;3;0): 3 steps
lem-nat-0-SBOX⟨2·1·3·0⟩ : WsL → ⟪ (Sw01 ∷ Sb2-1-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-3-1 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨2·1·3·0⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb2-1-3-0 ∷ []) (Sb2-0-3-1 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS13 ∷ []) (refl) ▸
       at 0 2 (CS03 ∷ Sw01 ∷ []) (sym (wl0019 c4)) ▸
       at 0 1 (Sb2-0-3-1 ∷ []) (refl) ▸ done


-- nat 0 SBOXd(2;1;3;0): 3 steps
lem-nat-0-SBOXd⟨2·1·3·0⟩ : WsL → ⟪ (Sw01 ∷ Sb⁻2-1-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-0-3-1 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨2·1·3·0⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻2-1-3-0 ∷ []) (Sb⁻2-0-3-1 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS13⁻ ∷ []) (refl) ▸
       at 0 2 (CS03⁻ ∷ Sw01 ∷ []) (sym (wl0022 c4)) ▸
       at 0 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸ done


-- nat 0 SBOX(2;1;40;3): 7 steps
lem-nat-0-SBOX⟨2·1·40·3⟩ : WsL → ⟪ (Sw01 ∷ Sb2-1-40-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨2·1·40·3⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb2-1-40-3 ∷ []) (Sb2-0-41-3 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx2-1403 ∷ Toff304 ∷ Sb2-1-3-0 ∷ Toff304 ∷ Sb⁻2-1-3-0 ∷ []) (refl) ▸
       at 0 2 (Bx2-0413 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·1403⟩ c4) ▸
       at 1 2 (Toff314 ∷ Sw01 ∷ []) (lem-nat-0-TOFF304 c4) ▸
       at 2 2 (Sb2-0-3-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·1·3·0⟩ c4) ▸
       at 3 2 (Toff314 ∷ Sw01 ∷ []) (lem-nat-0-TOFF304 c4) ▸
       at 4 2 (Sb⁻2-0-3-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨2·1·3·0⟩ c4) ▸
       at 0 5 (Sb2-0-41-3 ∷ []) (refl) ▸ done


-- nat 0 BOX(3;02): 3 steps
lem-nat-0-BOX⟨3·02⟩ : WsL → ⟪ (Sw01 ∷ Bx3-02 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-12 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·02⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx3-02 ∷ []) (Bx3-12 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CZ02 ∷ []) (refl) ▸
       at 0 2 (CZ12 ∷ Sw01 ∷ []) (sym (wl0137 c4)) ▸
       at 0 1 (Bx3-12 ∷ []) (refl) ▸ done


-- nat 0 BOX(0;312): 8 steps
lem-nat-0-BOX⟨0·312⟩ : WsL → ⟪ (Sw01 ∷ Bx0-312 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-302 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·312⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-312 ∷ []) (Bx1-302 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff013 ∷ Bx3-02 ∷ Toff013 ∷ CCZ013 ∷ Bx3-02 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw01 ∷ []) (sym (wl0100 c4)) ▸
       at 1 2 (Toff103 ∷ Sw01 ∷ []) (wl0101 c4) ▸
       at 2 2 (Bx3-12 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·02⟩ c4) ▸
       at 3 2 (Toff103 ∷ Sw01 ∷ []) (wl0101 c4) ▸
       at 4 2 (CCZ013 ∷ Sw01 ∷ []) (sym (wl0100 c4)) ▸
       at 5 2 (Bx3-12 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·02⟩ c4) ▸
       at 0 6 (Bx1-302 ∷ []) (refl) ▸ done


-- nat 0 BOX(3;0412): 8 steps
lem-nat-0-BOX⟨3·0412⟩ : WsL → ⟪ (Sw01 ∷ Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1402 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·0412⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx3-0412 ∷ []) (Bx3-1402 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff304 ∷ Bx0-312 ∷ Toff304 ∷ CCZ034 ∷ Bx0-312 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4) ▸
       at 1 2 (Toff314 ∷ Sw01 ∷ []) (lem-nat-0-TOFF304 c4) ▸
       at 2 2 (Bx1-302 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·312⟩ c4) ▸
       at 3 2 (Toff314 ∷ Sw01 ∷ []) (lem-nat-0-TOFF304 c4) ▸
       at 4 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4) ▸
       at 5 2 (Bx1-302 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·312⟩ c4) ▸
       at 0 6 (Bx3-1402 ∷ []) (refl) ▸ done


-- nat 0 SBOX(3;0;2;1): 3 steps
lem-nat-0-SBOX⟨3·0·2·1⟩ : WsL → ⟪ (Sw01 ∷ Sb3-0-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-1-2-0 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨3·0·2·1⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb3-0-2-1 ∷ []) (Sb3-1-2-0 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS02 ∷ []) (refl) ▸
       at 0 2 (CS12 ∷ Sw01 ∷ []) (sym (wl0138 c4)) ▸
       at 0 1 (Sb3-1-2-0 ∷ []) (refl) ▸ done


-- nat 0 SBOXd(3;0;2;1): 3 steps
lem-nat-0-SBOXd⟨3·0·2·1⟩ : WsL → ⟪ (Sw01 ∷ Sb⁻3-0-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻3-1-2-0 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨3·0·2·1⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻3-0-2-1 ∷ []) (Sb⁻3-1-2-0 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS02⁻ ∷ []) (refl) ▸
       at 0 2 (CS12⁻ ∷ Sw01 ∷ []) (sym (wl0139 c4)) ▸
       at 0 1 (Sb⁻3-1-2-0 ∷ []) (refl) ▸ done


-- nat 0 SBOX(3;0;41;2): 7 steps
lem-nat-0-SBOX⟨3·0·41·2⟩ : WsL → ⟪ (Sw01 ∷ Sb3-0-41-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-1-40-2 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨3·0·41·2⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb3-0-41-2 ∷ []) (Sb3-1-40-2 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (refl) ▸
       at 0 2 (Bx3-1402 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·0412⟩ c4) ▸
       at 1 2 (Toff204 ∷ Sw01 ∷ []) (lem-nat-0-TOFF214 c4) ▸
       at 2 2 (Sb3-1-2-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·0·2·1⟩ c4) ▸
       at 3 2 (Toff204 ∷ Sw01 ∷ []) (lem-nat-0-TOFF214 c4) ▸
       at 4 2 (Sb⁻3-1-2-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨3·0·2·1⟩ c4) ▸
       at 0 5 (Sb3-1-40-2 ∷ []) (refl) ▸ done


-- nat 1 SBOX(1;2;3;0): 3 steps
lem-nat-1-SBOX⟨1·2·3·0⟩ : WsL → ⟪ (Sw12 ∷ Sb1-2-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-1-3-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨1·2·3·0⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb1-2-3-0 ∷ []) (Sb2-1-3-0 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS23 ∷ []) (refl) ▸
       at 0 2 (CS13 ∷ Sw12 ∷ []) (sym (wl0024 c4)) ▸
       at 0 1 (Sb2-1-3-0 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(1;2;3;0): 3 steps
lem-nat-1-SBOXd⟨1·2·3·0⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻1-2-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-1-3-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨1·2·3·0⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻1-2-3-0 ∷ []) (Sb⁻2-1-3-0 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS23⁻ ∷ []) (refl) ▸
       at 0 2 (CS13⁻ ∷ Sw12 ∷ []) (sym (wl0043 c4)) ▸
       at 0 1 (Sb⁻2-1-3-0 ∷ []) (refl) ▸ done


-- nat 1 SBOX(1;2;40;3): 7 steps
lem-nat-1-SBOX⟨1·2·40·3⟩ : WsL → ⟪ (Sw12 ∷ Sb1-2-40-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-1-40-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨1·2·40·3⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb1-2-40-3 ∷ []) (Sb2-1-40-3 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx1-2403 ∷ Toff304 ∷ Sb1-2-3-0 ∷ Toff304 ∷ Sb⁻1-2-3-0 ∷ []) (refl) ▸
       at 0 2 (Bx2-1403 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·2403⟩ c4) ▸
       at 1 2 (Toff304 ∷ Sw12 ∷ []) (lem-nat-1-TOFF304 c4) ▸
       at 2 2 (Sb2-1-3-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·2·3·0⟩ c4) ▸
       at 3 2 (Toff304 ∷ Sw12 ∷ []) (lem-nat-1-TOFF304 c4) ▸
       at 4 2 (Sb⁻2-1-3-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·2·3·0⟩ c4) ▸
       at 0 5 (Sb2-1-40-3 ∷ []) (refl) ▸ done


-- nat 1 BOX(3;12): 3 steps
lem-nat-1-BOX⟨3·12⟩ : WsL → ⟪ (Sw12 ∷ Bx3-12 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-21 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·12⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-12 ∷ []) (Bx3-21 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ12 ∷ []) (refl) ▸
       at 0 2 (CZ12 ∷ Sw12 ∷ []) (sym (wl0109 c4)) ▸
       at 0 1 (Bx3-21 ∷ []) (refl) ▸ done


-- nat 1 BOX(1;302): 8 steps
lem-nat-1-BOX⟨1·302⟩ : WsL → ⟪ (Sw12 ∷ Bx1-302 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-301 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·302⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx1-302 ∷ []) (Bx2-301 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff103 ∷ Bx3-12 ∷ Toff103 ∷ CCZ013 ∷ Bx3-12 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 1 2 (Toff203 ∷ Sw12 ∷ []) (lem-nat-1-TOFF103 c4) ▸
       at 2 2 (Bx3-21 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·12⟩ c4) ▸
       at 3 2 (Toff203 ∷ Sw12 ∷ []) (lem-nat-1-TOFF103 c4) ▸
       at 4 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 5 2 (Bx3-21 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·12⟩ c4) ▸
       at 0 6 (Bx2-301 ∷ []) (refl) ▸ done


-- nat 1 BOX(3;1402): 8 steps
lem-nat-1-BOX⟨3·1402⟩ : WsL → ⟪ (Sw12 ∷ Bx3-1402 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2401 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·1402⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-1402 ∷ []) (Bx3-2401 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff314 ∷ Bx1-302 ∷ Toff314 ∷ CCZ134 ∷ Bx1-302 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw12 ∷ []) (sym (wl0084 c4)) ▸
       at 1 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 c4) ▸
       at 2 2 (Bx2-301 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·302⟩ c4) ▸
       at 3 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 c4) ▸
       at 4 2 (CCZ234 ∷ Sw12 ∷ []) (sym (wl0084 c4)) ▸
       at 5 2 (Bx2-301 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·302⟩ c4) ▸
       at 0 6 (Bx3-2401 ∷ []) (refl) ▸ done


-- nat 1 SBOX(3;1;2;0): 3 steps
lem-nat-1-SBOX⟨3·1·2·0⟩ : WsL → ⟪ (Sw12 ∷ Sb3-1-2-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-2-1-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨3·1·2·0⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb3-1-2-0 ∷ []) (Sb3-2-1-0 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS12 ∷ []) (refl) ▸
       at 0 2 (CS12 ∷ Sw12 ∷ []) (sym (wl0134 c4)) ▸
       at 0 1 (Sb3-2-1-0 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(3;1;2;0): 3 steps
lem-nat-1-SBOXd⟨3·1·2·0⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻3-1-2-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻3-2-1-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨3·1·2·0⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻3-1-2-0 ∷ []) (Sb⁻3-2-1-0 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS12⁻ ∷ []) (refl) ▸
       at 0 2 (CS12⁻ ∷ Sw12 ∷ []) (sym (wl0135 c4)) ▸
       at 0 1 (Sb⁻3-2-1-0 ∷ []) (refl) ▸ done


-- nat 1 SBOX(3;1;40;2): 7 steps
lem-nat-1-SBOX⟨3·1·40·2⟩ : WsL → ⟪ (Sw12 ∷ Sb3-1-40-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-2-40-1 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨3·1·40·2⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb3-1-40-2 ∷ []) (Sb3-2-40-1 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx3-1402 ∷ Toff204 ∷ Sb3-1-2-0 ∷ Toff204 ∷ Sb⁻3-1-2-0 ∷ []) (refl) ▸
       at 0 2 (Bx3-2401 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·1402⟩ c4) ▸
       at 1 2 (Toff104 ∷ Sw12 ∷ []) (lem-nat-1-TOFF204 c4) ▸
       at 2 2 (Sb3-2-1-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·1·2·0⟩ c4) ▸
       at 3 2 (Toff104 ∷ Sw12 ∷ []) (lem-nat-1-TOFF204 c4) ▸
       at 4 2 (Sb⁻3-2-1-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨3·1·2·0⟩ c4) ▸
       at 0 5 (Sb3-2-40-1 ∷ []) (refl) ▸ done


-- nat 2 BOX(1;32): 3 steps
lem-nat-2-BOX⟨1·32⟩ : WsL → ⟪ (Sw23 ∷ Bx1-32 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-23 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·32⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx1-32 ∷ []) (Bx1-23 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ23 ∷ []) (refl) ▸
       at 0 2 (CZ23 ∷ Sw23 ∷ []) (sym (wl0045 c4)) ▸
       at 0 1 (Bx1-23 ∷ []) (refl) ▸ done


-- nat 2 BOX(3;102): 8 steps
lem-nat-2-BOX⟨3·102⟩ : WsL → ⟪ (Sw23 ∷ Bx3-102 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-103 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·102⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx3-102 ∷ []) (Bx2-103 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff301 ∷ Bx1-32 ∷ Toff301 ∷ CCZ013 ∷ Bx1-32 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 1 2 (Toff201 ∷ Sw23 ∷ []) (lem-nat-2-TOFF301 c4) ▸
       at 2 2 (Bx1-23 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·32⟩ c4) ▸
       at 3 2 (Toff201 ∷ Sw23 ∷ []) (lem-nat-2-TOFF301 c4) ▸
       at 4 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 5 2 (Bx1-23 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·32⟩ c4) ▸
       at 0 6 (Bx2-103 ∷ []) (refl) ▸ done


-- nat 2 BOX(1;3402): 8 steps
lem-nat-2-BOX⟨1·3402⟩ : WsL → ⟪ (Sw23 ∷ Bx1-3402 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2403 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·3402⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx1-3402 ∷ []) (Bx1-2403 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff134 ∷ Bx3-102 ∷ Toff134 ∷ CCZ134 ∷ Bx3-102 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 1 2 (Toff124 ∷ Sw23 ∷ []) (lem-nat-2-TOFF134 c4) ▸
       at 2 2 (Bx2-103 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·102⟩ c4) ▸
       at 3 2 (Toff124 ∷ Sw23 ∷ []) (lem-nat-2-TOFF134 c4) ▸
       at 4 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 5 2 (Bx2-103 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·102⟩ c4) ▸
       at 0 6 (Bx1-2403 ∷ []) (refl) ▸ done


-- nat 2 SBOX(1;3;2;0): 3 steps
lem-nat-2-SBOX⟨1·3·2·0⟩ : WsL → ⟪ (Sw23 ∷ Sb1-3-2-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-3-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨1·3·2·0⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb1-3-2-0 ∷ []) (Sb1-2-3-0 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS23 ∷ []) (refl) ▸
       at 0 2 (CS23 ∷ Sw23 ∷ []) (sym (wl0152 c4)) ▸
       at 0 1 (Sb1-2-3-0 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(1;3;2;0): 3 steps
lem-nat-2-SBOXd⟨1·3·2·0⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻1-3-2-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-2-3-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨1·3·2·0⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻1-3-2-0 ∷ []) (Sb⁻1-2-3-0 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS23⁻ ∷ []) (refl) ▸
       at 0 2 (CS23⁻ ∷ Sw23 ∷ []) (sym (wl0153 c4)) ▸
       at 0 1 (Sb⁻1-2-3-0 ∷ []) (refl) ▸ done


-- nat 2 SBOX(1;3;40;2): 7 steps
lem-nat-2-SBOX⟨1·3·40·2⟩ : WsL → ⟪ (Sw23 ∷ Sb1-3-40-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-40-3 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨1·3·40·2⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb1-3-40-2 ∷ []) (Sb1-2-40-3 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx1-3402 ∷ Toff204 ∷ Sb1-3-2-0 ∷ Toff204 ∷ Sb⁻1-3-2-0 ∷ []) (refl) ▸
       at 0 2 (Bx1-2403 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·3402⟩ c4) ▸
       at 1 2 (Toff304 ∷ Sw23 ∷ []) (lem-nat-2-TOFF204 c4) ▸
       at 2 2 (Sb1-2-3-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·3·2·0⟩ c4) ▸
       at 3 2 (Toff304 ∷ Sw23 ∷ []) (lem-nat-2-TOFF204 c4) ▸
       at 4 2 (Sb⁻1-2-3-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·3·2·0⟩ c4) ▸
       at 0 5 (Sb1-2-40-3 ∷ []) (refl) ▸ done


-- nat 2 BOX(3;21): 3 steps
lem-nat-2-BOX⟨3·21⟩ : WsL → ⟪ (Sw23 ∷ Bx3-21 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-31 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·21⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx3-21 ∷ []) (Bx2-31 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ12 ∷ []) (refl) ▸
       at 0 2 (CZ13 ∷ Sw23 ∷ []) (lem-nat-2-CZ12 c4) ▸
       at 0 1 (Bx2-31 ∷ []) (refl) ▸ done


-- nat 2 BOX(2;301): 8 steps
lem-nat-2-BOX⟨2·301⟩ : WsL → ⟪ (Sw23 ∷ Bx2-301 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-201 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·301⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx2-301 ∷ []) (Bx3-201 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff203 ∷ Bx3-21 ∷ Toff203 ∷ CCZ023 ∷ Bx3-21 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw23 ∷ []) (sym (wl0065 c4)) ▸
       at 1 2 (Toff302 ∷ Sw23 ∷ []) (wl0090 c4) ▸
       at 2 2 (Bx2-31 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·21⟩ c4) ▸
       at 3 2 (Toff302 ∷ Sw23 ∷ []) (wl0090 c4) ▸
       at 4 2 (CCZ023 ∷ Sw23 ∷ []) (sym (wl0065 c4)) ▸
       at 5 2 (Bx2-31 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·21⟩ c4) ▸
       at 0 6 (Bx3-201 ∷ []) (refl) ▸ done


-- nat 2 BOX(3;2401): 8 steps
lem-nat-2-BOX⟨3·2401⟩ : WsL → ⟪ (Sw23 ∷ Bx3-2401 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3401 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·2401⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx3-2401 ∷ []) (Bx2-3401 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff324 ∷ Bx2-301 ∷ Toff324 ∷ CCZ234 ∷ Bx2-301 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw23 ∷ []) (sym (wl0086 c4)) ▸
       at 1 2 (Toff234 ∷ Sw23 ∷ []) (wl0144 c4) ▸
       at 2 2 (Bx3-201 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·301⟩ c4) ▸
       at 3 2 (Toff234 ∷ Sw23 ∷ []) (wl0144 c4) ▸
       at 4 2 (CCZ234 ∷ Sw23 ∷ []) (sym (wl0086 c4)) ▸
       at 5 2 (Bx3-201 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·301⟩ c4) ▸
       at 0 6 (Bx2-3401 ∷ []) (refl) ▸ done


-- nat 2 SBOX(3;2;1;0): 3 steps
lem-nat-2-SBOX⟨3·2·1·0⟩ : WsL → ⟪ (Sw23 ∷ Sb3-2-1-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-3-1-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨3·2·1·0⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb3-2-1-0 ∷ []) (Sb2-3-1-0 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS12 ∷ []) (refl) ▸
       at 0 2 (CS13 ∷ Sw23 ∷ []) (lem-nat-2-CS12 c4) ▸
       at 0 1 (Sb2-3-1-0 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(3;2;1;0): 3 steps
lem-nat-2-SBOXd⟨3·2·1·0⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻3-2-1-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-3-1-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨3·2·1·0⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻3-2-1-0 ∷ []) (Sb⁻2-3-1-0 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS12⁻ ∷ []) (refl) ▸
       at 0 2 (CS13⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd12 c4) ▸
       at 0 1 (Sb⁻2-3-1-0 ∷ []) (refl) ▸ done


-- nat 2 SBOX(3;2;40;1): 7 steps
lem-nat-2-SBOX⟨3·2·40·1⟩ : WsL → ⟪ (Sw23 ∷ Sb3-2-40-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-3-40-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨3·2·40·1⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb3-2-40-1 ∷ []) (Sb2-3-40-1 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx3-2401 ∷ Toff104 ∷ Sb3-2-1-0 ∷ Toff104 ∷ Sb⁻3-2-1-0 ∷ []) (refl) ▸
       at 0 2 (Bx2-3401 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·2401⟩ c4) ▸
       at 1 2 (Toff104 ∷ Sw23 ∷ []) (lem-nat-2-TOFF104 c4) ▸
       at 2 2 (Sb2-3-1-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·2·1·0⟩ c4) ▸
       at 3 2 (Toff104 ∷ Sw23 ∷ []) (lem-nat-2-TOFF104 c4) ▸
       at 4 2 (Sb⁻2-3-1-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨3·2·1·0⟩ c4) ▸
       at 0 5 (Sb2-3-40-1 ∷ []) (refl) ▸ done


-- nat 3 BOX(1;42): 3 steps
lem-nat-3-BOX⟨1·42⟩ : WsL → ⟪ (Sw34 ∷ Bx1-42 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-32 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨1·42⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx1-42 ∷ []) (Bx1-32 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CZ24 ∷ []) (refl) ▸
       at 0 2 (CZ23 ∷ Sw34 ∷ []) (lem-nat-3-CZ24 c4) ▸
       at 0 1 (Bx1-32 ∷ []) (refl) ▸ done


-- nat 3 BOX(4;102): 8 steps
lem-nat-3-BOX⟨4·102⟩ : WsL → ⟪ (Sw34 ∷ Bx4-102 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-102 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨4·102⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx4-102 ∷ []) (Bx3-102 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff401 ∷ Bx1-42 ∷ Toff401 ∷ CCZ014 ∷ Bx1-42 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4) ▸
       at 1 2 (Toff301 ∷ Sw34 ∷ []) (lem-nat-3-TOFF401 c4) ▸
       at 2 2 (Bx1-32 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·42⟩ c4) ▸
       at 3 2 (Toff301 ∷ Sw34 ∷ []) (lem-nat-3-TOFF401 c4) ▸
       at 4 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4) ▸
       at 5 2 (Bx1-32 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·42⟩ c4) ▸
       at 0 6 (Bx3-102 ∷ []) (refl) ▸ done


-- nat 3 BOX(1;4302): 8 steps
lem-nat-3-BOX⟨1·4302⟩ : WsL → ⟪ (Sw34 ∷ Bx1-4302 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3402 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨1·4302⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx1-4302 ∷ []) (Bx1-3402 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff134 ∷ Bx4-102 ∷ Toff134 ∷ CCZ134 ∷ Bx4-102 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw34 ∷ []) (sym (wl0154 c4)) ▸
       at 1 2 (Toff134 ∷ Sw34 ∷ []) (wl0129 c4) ▸
       at 2 2 (Bx3-102 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·102⟩ c4) ▸
       at 3 2 (Toff134 ∷ Sw34 ∷ []) (wl0129 c4) ▸
       at 4 2 (CCZ134 ∷ Sw34 ∷ []) (sym (wl0154 c4)) ▸
       at 5 2 (Bx3-102 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·102⟩ c4) ▸
       at 0 6 (Bx1-3402 ∷ []) (refl) ▸ done


-- nat 3 SBOX(1;4;2;0): 3 steps
lem-nat-3-SBOX⟨1·4·2·0⟩ : WsL → ⟪ (Sw34 ∷ Sb1-4-2-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-3-2-0 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨1·4·2·0⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb1-4-2-0 ∷ []) (Sb1-3-2-0 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS24 ∷ []) (refl) ▸
       at 0 2 (CS23 ∷ Sw34 ∷ []) (lem-nat-3-CS24 c4) ▸
       at 0 1 (Sb1-3-2-0 ∷ []) (refl) ▸ done


-- nat 3 CSd24: 2 steps
lem-nat-3-CSd24 : WsL → ⟪ (Sw34 ∷ CS24⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-CSd24 c4 = run b0
  where
  b0 : Chain (Sw34 ∷ CS24⁻ ∷ []) (CS23⁻ ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0007 c4) ▸ done


-- nat 3 SBOXd(1;4;2;0): 3 steps
lem-nat-3-SBOXd⟨1·4·2·0⟩ : WsL → ⟪ (Sw34 ∷ Sb⁻1-4-2-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-3-2-0 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨1·4·2·0⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb⁻1-4-2-0 ∷ []) (Sb⁻1-3-2-0 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS24⁻ ∷ []) (refl) ▸
       at 0 2 (CS23⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd24 c4) ▸
       at 0 1 (Sb⁻1-3-2-0 ∷ []) (refl) ▸ done


-- nat 3 SBOX(1;4;30;2): 7 steps
lem-nat-3-SBOX⟨1·4·30·2⟩ : WsL → ⟪ (Sw34 ∷ Sb1-4-30-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-3-40-2 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨1·4·30·2⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb1-4-30-2 ∷ []) (Sb1-3-40-2 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx1-4302 ∷ Toff203 ∷ Sb1-4-2-0 ∷ Toff203 ∷ Sb⁻1-4-2-0 ∷ []) (refl) ▸
       at 0 2 (Bx1-3402 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·4302⟩ c4) ▸
       at 1 2 (Toff204 ∷ Sw34 ∷ []) (lem-nat-3-TOFF203 c4) ▸
       at 2 2 (Sb1-3-2-0 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨1·4·2·0⟩ c4) ▸
       at 3 2 (Toff204 ∷ Sw34 ∷ []) (lem-nat-3-TOFF203 c4) ▸
       at 4 2 (Sb⁻1-3-2-0 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨1·4·2·0⟩ c4) ▸
       at 0 5 (Sb1-3-40-2 ∷ []) (refl) ▸ done


-- nat 3 BOX(2;31): 3 steps
lem-nat-3-BOX⟨2·31⟩ : WsL → ⟪ (Sw34 ∷ Bx2-31 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-41 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨2·31⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx2-31 ∷ []) (Bx2-41 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CZ13 ∷ []) (refl) ▸
       at 0 2 (CZ14 ∷ Sw34 ∷ []) (lem-nat-3-CZ13 c4) ▸
       at 0 1 (Bx2-41 ∷ []) (refl) ▸ done


-- nat 3 BOX(3;201): 8 steps
lem-nat-3-BOX⟨3·201⟩ : WsL → ⟪ (Sw34 ∷ Bx3-201 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-201 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨3·201⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx3-201 ∷ []) (Bx4-201 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff302 ∷ Bx2-31 ∷ Toff302 ∷ CCZ023 ∷ Bx2-31 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw34 ∷ []) (lem-nat-3-CCZ023 c4) ▸
       at 1 2 (Toff402 ∷ Sw34 ∷ []) (lem-nat-3-TOFF302 c4) ▸
       at 2 2 (Bx2-41 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·31⟩ c4) ▸
       at 3 2 (Toff402 ∷ Sw34 ∷ []) (lem-nat-3-TOFF302 c4) ▸
       at 4 2 (CCZ024 ∷ Sw34 ∷ []) (lem-nat-3-CCZ023 c4) ▸
       at 5 2 (Bx2-41 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·31⟩ c4) ▸
       at 0 6 (Bx4-201 ∷ []) (refl) ▸ done


-- nat 3 BOX(2;3401): 8 steps
lem-nat-3-BOX⟨2·3401⟩ : WsL → ⟪ (Sw34 ∷ Bx2-3401 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4301 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨2·3401⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx2-3401 ∷ []) (Bx2-4301 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff234 ∷ Bx3-201 ∷ Toff234 ∷ CCZ234 ∷ Bx3-201 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw34 ∷ []) (sym (wl0155 c4)) ▸
       at 1 2 (Toff234 ∷ Sw34 ∷ []) (wl0128 c4) ▸
       at 2 2 (Bx4-201 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·201⟩ c4) ▸
       at 3 2 (Toff234 ∷ Sw34 ∷ []) (wl0128 c4) ▸
       at 4 2 (CCZ234 ∷ Sw34 ∷ []) (sym (wl0155 c4)) ▸
       at 5 2 (Bx4-201 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·201⟩ c4) ▸
       at 0 6 (Bx2-4301 ∷ []) (refl) ▸ done


-- nat 3 SBOX(2;3;1;0): 3 steps
lem-nat-3-SBOX⟨2·3·1·0⟩ : WsL → ⟪ (Sw34 ∷ Sb2-3-1-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-1-0 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨2·3·1·0⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb2-3-1-0 ∷ []) (Sb2-4-1-0 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS13 ∷ []) (refl) ▸
       at 0 2 (CS14 ∷ Sw34 ∷ []) (lem-nat-3-CS13 c4) ▸
       at 0 1 (Sb2-4-1-0 ∷ []) (refl) ▸ done


-- nat 3 SBOXd(2;3;1;0): 3 steps
lem-nat-3-SBOXd⟨2·3·1·0⟩ : WsL → ⟪ (Sw34 ∷ Sb⁻2-3-1-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-4-1-0 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨2·3·1·0⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb⁻2-3-1-0 ∷ []) (Sb⁻2-4-1-0 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS13⁻ ∷ []) (refl) ▸
       at 0 2 (CS14⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd13 c4) ▸
       at 0 1 (Sb⁻2-4-1-0 ∷ []) (refl) ▸ done


-- nat 3 SBOX(2;3;40;1): 7 steps
lem-nat-3-SBOX⟨2·3·40·1⟩ : WsL → ⟪ (Sw34 ∷ Sb2-3-40-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-30-1 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨2·3·40·1⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb2-3-40-1 ∷ []) (Sb2-4-30-1 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx2-3401 ∷ Toff104 ∷ Sb2-3-1-0 ∷ Toff104 ∷ Sb⁻2-3-1-0 ∷ []) (refl) ▸
       at 0 2 (Bx2-4301 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·3401⟩ c4) ▸
       at 1 2 (Toff103 ∷ Sw34 ∷ []) (lem-nat-3-TOFF104 c4) ▸
       at 2 2 (Sb2-4-1-0 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨2·3·1·0⟩ c4) ▸
       at 3 2 (Toff103 ∷ Sw34 ∷ []) (lem-nat-3-TOFF104 c4) ▸
       at 4 2 (Sb⁻2-4-1-0 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨2·3·1·0⟩ c4) ▸
       at 0 5 (Sb2-4-30-1 ∷ []) (refl) ▸ done


-- nat 1 BOX(4;201): 8 steps
lem-nat-1-BOX⟨4·201⟩ : WsL → ⟪ (Sw12 ∷ Bx4-201 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-102 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·201⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx4-201 ∷ []) (Bx4-102 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff402 ∷ Bx2-41 ∷ Toff402 ∷ CCZ024 ∷ Bx2-41 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 1 2 (Toff401 ∷ Sw12 ∷ []) (lem-nat-1-TOFF402 c4) ▸
       at 2 2 (Bx1-42 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·41⟩ c4) ▸
       at 3 2 (Toff401 ∷ Sw12 ∷ []) (lem-nat-1-TOFF402 c4) ▸
       at 4 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 5 2 (Bx1-42 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·41⟩ c4) ▸
       at 0 6 (Bx4-102 ∷ []) (refl) ▸ done


-- nat 1 BOX(2;4301): 8 steps
lem-nat-1-BOX⟨2·4301⟩ : WsL → ⟪ (Sw12 ∷ Bx2-4301 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-4302 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·4301⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx2-4301 ∷ []) (Bx1-4302 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff234 ∷ Bx4-201 ∷ Toff234 ∷ CCZ234 ∷ Bx4-201 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0034 c4)) ▸
       at 1 2 (Toff134 ∷ Sw12 ∷ []) (wl0140 c4) ▸
       at 2 2 (Bx4-102 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·201⟩ c4) ▸
       at 3 2 (Toff134 ∷ Sw12 ∷ []) (wl0140 c4) ▸
       at 4 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0034 c4)) ▸
       at 5 2 (Bx4-102 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·201⟩ c4) ▸
       at 0 6 (Bx1-4302 ∷ []) (refl) ▸ done


-- nat 1 SBOX(2;4;1;0): 3 steps
lem-nat-1-SBOX⟨2·4·1·0⟩ : WsL → ⟪ (Sw12 ∷ Sb2-4-1-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-4-2-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨2·4·1·0⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb2-4-1-0 ∷ []) (Sb1-4-2-0 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS14 ∷ []) (refl) ▸
       at 0 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0008 c4)) ▸
       at 0 1 (Sb1-4-2-0 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(2;4;1;0): 3 steps
lem-nat-1-SBOXd⟨2·4·1·0⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻2-4-1-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-4-2-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨2·4·1·0⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻2-4-1-0 ∷ []) (Sb⁻1-4-2-0 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS14⁻ ∷ []) (refl) ▸
       at 0 2 (CS24⁻ ∷ Sw12 ∷ []) (sym (wl0009 c4)) ▸
       at 0 1 (Sb⁻1-4-2-0 ∷ []) (refl) ▸ done


-- nat 1 SBOX(2;4;30;1): 7 steps
lem-nat-1-SBOX⟨2·4·30·1⟩ : WsL → ⟪ (Sw12 ∷ Sb2-4-30-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-4-30-2 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨2·4·30·1⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb2-4-30-1 ∷ []) (Sb1-4-30-2 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx2-4301 ∷ Toff103 ∷ Sb2-4-1-0 ∷ Toff103 ∷ Sb⁻2-4-1-0 ∷ []) (refl) ▸
       at 0 2 (Bx1-4302 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·4301⟩ c4) ▸
       at 1 2 (Toff203 ∷ Sw12 ∷ []) (lem-nat-1-TOFF103 c4) ▸
       at 2 2 (Sb1-4-2-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·4·1·0⟩ c4) ▸
       at 3 2 (Toff203 ∷ Sw12 ∷ []) (lem-nat-1-TOFF103 c4) ▸
       at 4 2 (Sb⁻1-4-2-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·4·1·0⟩ c4) ▸
       at 0 5 (Sb1-4-30-2 ∷ []) (refl) ▸ done


-- nat 2 BOX(3;41): 3 steps
lem-nat-2-BOX⟨3·41⟩ : WsL → ⟪ (Sw23 ∷ Bx3-41 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-41 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·41⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx3-41 ∷ []) (Bx2-41 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ14 ∷ []) (refl) ▸
       at 0 2 (CZ14 ∷ Sw23 ∷ []) (sym (wl0042 c4)) ▸
       at 0 1 (Bx2-41 ∷ []) (refl) ▸ done


-- nat 2 BOX(4;301): 8 steps
lem-nat-2-BOX⟨4·301⟩ : WsL → ⟪ (Sw23 ∷ Bx4-301 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-201 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·301⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx4-301 ∷ []) (Bx4-201 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff403 ∷ Bx3-41 ∷ Toff403 ∷ CCZ034 ∷ Bx3-41 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 1 2 (Toff402 ∷ Sw23 ∷ []) (lem-nat-2-TOFF403 c4) ▸
       at 2 2 (Bx2-41 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·41⟩ c4) ▸
       at 3 2 (Toff402 ∷ Sw23 ∷ []) (lem-nat-2-TOFF403 c4) ▸
       at 4 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 5 2 (Bx2-41 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·41⟩ c4) ▸
       at 0 6 (Bx4-201 ∷ []) (refl) ▸ done


-- nat 2 BOX(3;4201): 8 steps
lem-nat-2-BOX⟨3·4201⟩ : WsL → ⟪ (Sw23 ∷ Bx3-4201 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4301 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·4201⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx3-4201 ∷ []) (Bx2-4301 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff324 ∷ Bx4-301 ∷ Toff324 ∷ CCZ234 ∷ Bx4-301 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw23 ∷ []) (sym (wl0086 c4)) ▸
       at 1 2 (Toff234 ∷ Sw23 ∷ []) (wl0144 c4) ▸
       at 2 2 (Bx4-201 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·301⟩ c4) ▸
       at 3 2 (Toff234 ∷ Sw23 ∷ []) (wl0144 c4) ▸
       at 4 2 (CCZ234 ∷ Sw23 ∷ []) (sym (wl0086 c4)) ▸
       at 5 2 (Bx4-201 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·301⟩ c4) ▸
       at 0 6 (Bx2-4301 ∷ []) (refl) ▸ done


-- nat 2 SBOX(3;4;1;0): 3 steps
lem-nat-2-SBOX⟨3·4·1·0⟩ : WsL → ⟪ (Sw23 ∷ Sb3-4-1-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-1-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨3·4·1·0⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb3-4-1-0 ∷ []) (Sb2-4-1-0 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS14 ∷ []) (refl) ▸
       at 0 2 (CS14 ∷ Sw23 ∷ []) (sym (wl0021 c4)) ▸
       at 0 1 (Sb2-4-1-0 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(3;4;1;0): 3 steps
lem-nat-2-SBOXd⟨3·4·1·0⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻3-4-1-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-4-1-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨3·4·1·0⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻3-4-1-0 ∷ []) (Sb⁻2-4-1-0 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS14⁻ ∷ []) (refl) ▸
       at 0 2 (CS14⁻ ∷ Sw23 ∷ []) (sym (wl0033 c4)) ▸
       at 0 1 (Sb⁻2-4-1-0 ∷ []) (refl) ▸ done


-- nat 2 SBOX(3;4;20;1): 7 steps
lem-nat-2-SBOX⟨3·4·20·1⟩ : WsL → ⟪ (Sw23 ∷ Sb3-4-20-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-30-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨3·4·20·1⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb3-4-20-1 ∷ []) (Sb2-4-30-1 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx3-4201 ∷ Toff102 ∷ Sb3-4-1-0 ∷ Toff102 ∷ Sb⁻3-4-1-0 ∷ []) (refl) ▸
       at 0 2 (Bx2-4301 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·4201⟩ c4) ▸
       at 1 2 (Toff103 ∷ Sw23 ∷ []) (lem-nat-2-TOFF102 c4) ▸
       at 2 2 (Sb2-4-1-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·4·1·0⟩ c4) ▸
       at 3 2 (Toff103 ∷ Sw23 ∷ []) (lem-nat-2-TOFF102 c4) ▸
       at 4 2 (Sb⁻2-4-1-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨3·4·1·0⟩ c4) ▸
       at 0 5 (Sb2-4-30-1 ∷ []) (refl) ▸ done


-- nat 2 BOX(1;42): 3 steps
lem-nat-2-BOX⟨1·42⟩ : WsL → ⟪ (Sw23 ∷ Bx1-42 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-43 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·42⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx1-42 ∷ []) (Bx1-43 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ24 ∷ []) (refl) ▸
       at 0 2 (CZ34 ∷ Sw23 ∷ []) (sym (wl0028 c4)) ▸
       at 0 1 (Bx1-43 ∷ []) (refl) ▸ done


-- nat 2 BOX(4;102): 8 steps
lem-nat-2-BOX⟨4·102⟩ : WsL → ⟪ (Sw23 ∷ Bx4-102 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-103 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·102⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx4-102 ∷ []) (Bx4-103 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff401 ∷ Bx1-42 ∷ Toff401 ∷ CCZ014 ∷ Bx1-42 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 1 2 (Toff401 ∷ Sw23 ∷ []) (lem-nat-2-TOFF401 c4) ▸
       at 2 2 (Bx1-43 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·42⟩ c4) ▸
       at 3 2 (Toff401 ∷ Sw23 ∷ []) (lem-nat-2-TOFF401 c4) ▸
       at 4 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 5 2 (Bx1-43 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·42⟩ c4) ▸
       at 0 6 (Bx4-103 ∷ []) (refl) ▸ done


-- nat 2 BOX(1;4302): 8 steps
lem-nat-2-BOX⟨1·4302⟩ : WsL → ⟪ (Sw23 ∷ Bx1-4302 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-4203 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·4302⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx1-4302 ∷ []) (Bx1-4203 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff134 ∷ Bx4-102 ∷ Toff134 ∷ CCZ134 ∷ Bx4-102 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 1 2 (Toff124 ∷ Sw23 ∷ []) (lem-nat-2-TOFF134 c4) ▸
       at 2 2 (Bx4-103 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·102⟩ c4) ▸
       at 3 2 (Toff124 ∷ Sw23 ∷ []) (lem-nat-2-TOFF134 c4) ▸
       at 4 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 5 2 (Bx4-103 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·102⟩ c4) ▸
       at 0 6 (Bx1-4203 ∷ []) (refl) ▸ done


-- nat 2 SBOX(1;4;2;0): 3 steps
lem-nat-2-SBOX⟨1·4·2·0⟩ : WsL → ⟪ (Sw23 ∷ Sb1-4-2-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-4-3-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨1·4·2·0⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb1-4-2-0 ∷ []) (Sb1-4-3-0 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS24 ∷ []) (refl) ▸
       at 0 2 (CS34 ∷ Sw23 ∷ []) (sym (wl0011 c4)) ▸
       at 0 1 (Sb1-4-3-0 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(1;4;2;0): 3 steps
lem-nat-2-SBOXd⟨1·4·2·0⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻1-4-2-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-4-3-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨1·4·2·0⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻1-4-2-0 ∷ []) (Sb⁻1-4-3-0 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS24⁻ ∷ []) (refl) ▸
       at 0 2 (CS34⁻ ∷ Sw23 ∷ []) (sym (wl0012 c4)) ▸
       at 0 1 (Sb⁻1-4-3-0 ∷ []) (refl) ▸ done


-- nat 2 SBOX(1;4;30;2): 7 steps
lem-nat-2-SBOX⟨1·4·30·2⟩ : WsL → ⟪ (Sw23 ∷ Sb1-4-30-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-4-20-3 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨1·4·30·2⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb1-4-30-2 ∷ []) (Sb1-4-20-3 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx1-4302 ∷ Toff203 ∷ Sb1-4-2-0 ∷ Toff203 ∷ Sb⁻1-4-2-0 ∷ []) (refl) ▸
       at 0 2 (Bx1-4203 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·4302⟩ c4) ▸
       at 1 2 (Toff302 ∷ Sw23 ∷ []) (wl0090 c4) ▸
       at 2 2 (Sb1-4-3-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·4·2·0⟩ c4) ▸
       at 3 2 (Toff302 ∷ Sw23 ∷ []) (wl0090 c4) ▸
       at 4 2 (Sb⁻1-4-3-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·4·2·0⟩ c4) ▸
       at 0 5 (Sb1-4-20-3 ∷ []) (refl) ▸ done


-- nat 0 BOX(4;310): 8 steps
lem-nat-0-BOX⟨4·310⟩ : WsL → ⟪ (Sw01 ∷ Bx4-310 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-301 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·310⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx4-310 ∷ []) (Bx4-301 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff413 ∷ Bx3-40 ∷ Toff413 ∷ CCZ134 ∷ Bx3-40 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 1 2 (Toff403 ∷ Sw01 ∷ []) (lem-nat-0-TOFF413 c4) ▸
       at 2 2 (Bx3-41 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·40⟩ c4) ▸
       at 3 2 (Toff403 ∷ Sw01 ∷ []) (lem-nat-0-TOFF413 c4) ▸
       at 4 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 5 2 (Bx3-41 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·40⟩ c4) ▸
       at 0 6 (Bx4-301 ∷ []) (refl) ▸ done


-- nat 0 BOX(3;4210): 8 steps
lem-nat-0-BOX⟨3·4210⟩ : WsL → ⟪ (Sw01 ∷ Bx3-4210 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4201 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·4210⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx3-4210 ∷ []) (Bx3-4201 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff324 ∷ Bx4-310 ∷ Toff324 ∷ CCZ234 ∷ Bx4-310 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 1 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 2 2 (Bx4-301 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·310⟩ c4) ▸
       at 3 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 4 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 5 2 (Bx4-301 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·310⟩ c4) ▸
       at 0 6 (Bx3-4201 ∷ []) (refl) ▸ done


-- nat 0 SBOX(3;4;0;1): 3 steps
lem-nat-0-SBOX⟨3·4·0·1⟩ : WsL → ⟪ (Sw01 ∷ Sb3-4-0-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-4-1-0 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨3·4·0·1⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb3-4-0-1 ∷ []) (Sb3-4-1-0 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS04 ∷ []) (refl) ▸
       at 0 2 (CS14 ∷ Sw01 ∷ []) (lem-nat-0-CS04 c4) ▸
       at 0 1 (Sb3-4-1-0 ∷ []) (refl) ▸ done


-- nat 0 SBOXd(3;4;0;1): 3 steps
lem-nat-0-SBOXd⟨3·4·0·1⟩ : WsL → ⟪ (Sw01 ∷ Sb⁻3-4-0-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻3-4-1-0 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨3·4·0·1⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻3-4-0-1 ∷ []) (Sb⁻3-4-1-0 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS04⁻ ∷ []) (refl) ▸
       at 0 2 (CS14⁻ ∷ Sw01 ∷ []) (lem-nat-0-CSd04 c4) ▸
       at 0 1 (Sb⁻3-4-1-0 ∷ []) (refl) ▸ done


-- nat 0 SBOX(3;4;21;0): 7 steps
lem-nat-0-SBOX⟨3·4·21·0⟩ : WsL → ⟪ (Sw01 ∷ Sb3-4-21-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-4-20-1 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨3·4·21·0⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb3-4-21-0 ∷ []) (Sb3-4-20-1 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx3-4210 ∷ Toff012 ∷ Sb3-4-0-1 ∷ Toff012 ∷ Sb⁻3-4-0-1 ∷ []) (refl) ▸
       at 0 2 (Bx3-4201 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·4210⟩ c4) ▸
       at 1 2 (Toff102 ∷ Sw01 ∷ []) (wl0099 c4) ▸
       at 2 2 (Sb3-4-1-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·4·0·1⟩ c4) ▸
       at 3 2 (Toff102 ∷ Sw01 ∷ []) (wl0099 c4) ▸
       at 4 2 (Sb⁻3-4-1-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨3·4·0·1⟩ c4) ▸
       at 0 5 (Sb3-4-20-1 ∷ []) (refl) ▸ done


-- nat 0 BOX(4;103): 8 steps
lem-nat-0-BOX⟨4·103⟩ : WsL → ⟪ (Sw01 ∷ Bx4-103 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-013 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·103⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx4-103 ∷ []) (Bx4-013 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff401 ∷ Bx1-43 ∷ Toff401 ∷ CCZ014 ∷ Bx1-43 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 1 2 (Toff401 ∷ Sw01 ∷ []) (lem-nat-0-TOFF401 c4) ▸
       at 2 2 (Bx0-43 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·43⟩ c4) ▸
       at 3 2 (Toff401 ∷ Sw01 ∷ []) (lem-nat-0-TOFF401 c4) ▸
       at 4 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 5 2 (Bx0-43 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·43⟩ c4) ▸
       at 0 6 (Bx4-013 ∷ []) (refl) ▸ done


-- nat 0 BOX(1;4203): 8 steps
lem-nat-0-BOX⟨1·4203⟩ : WsL → ⟪ (Sw01 ∷ Bx1-4203 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4213 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·4203⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-4203 ∷ []) (Bx0-4213 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff124 ∷ Bx4-103 ∷ Toff124 ∷ CCZ124 ∷ Bx4-103 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 1 2 (Toff024 ∷ Sw01 ∷ []) (lem-nat-0-TOFF124 c4) ▸
       at 2 2 (Bx4-013 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·103⟩ c4) ▸
       at 3 2 (Toff024 ∷ Sw01 ∷ []) (lem-nat-0-TOFF124 c4) ▸
       at 4 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 5 2 (Bx4-013 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·103⟩ c4) ▸
       at 0 6 (Bx0-4213 ∷ []) (refl) ▸ done


-- nat 0 SBOX(1;4;3;0): 2 steps
lem-nat-0-SBOX⟨1·4·3·0⟩ : WsL → ⟪ (Sw01 ∷ Sb1-4-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-4-3-1 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨1·4·3·0⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb1-4-3-0 ∷ []) (Sb0-4-3-1 ∷ Sw01 ∷ [])
  b0 = at 0 2 (Sb1-4-3-0 ∷ Sw01 ∷ []) (c₂ (Swap) (CS ↑)) ▸
       at 0 1 (Sb0-4-3-1 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 SBOXd(1;4;3;0): 2 steps
lem-nat-0-SBOXd⟨1·4·3·0⟩ : WsL → ⟪ (Sw01 ∷ Sb⁻1-4-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-4-3-1 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨1·4·3·0⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻1-4-3-0 ∷ []) (Sb⁻0-4-3-1 ∷ Sw01 ∷ [])
  b0 = at 0 2 (Sb⁻1-4-3-0 ∷ Sw01 ∷ []) (c₂ (Swap) ((CS • CS • CS) ↑)) ▸
       at 0 1 (Sb⁻0-4-3-1 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 SBOX(1;4;20;3): 7 steps
lem-nat-0-SBOX⟨1·4·20·3⟩ : WsL → ⟪ (Sw01 ∷ Sb1-4-20-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-4-21-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨1·4·20·3⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb1-4-20-3 ∷ []) (Sb0-4-21-3 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx1-4203 ∷ Toff302 ∷ Sb1-4-3-0 ∷ Toff302 ∷ Sb⁻1-4-3-0 ∷ []) (refl) ▸
       at 0 2 (Bx0-4213 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·4203⟩ c4) ▸
       at 1 2 (Toff312 ∷ Sw01 ∷ []) (wl0116 c4) ▸
       at 2 2 (Sb0-4-3-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·4·3·0⟩ c4) ▸
       at 3 2 (Toff312 ∷ Sw01 ∷ []) (wl0116 c4) ▸
       at 4 2 (Sb⁻0-4-3-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·4·3·0⟩ c4) ▸
       at 0 5 (Sb0-4-21-3 ∷ []) (refl) ▸ done


-- nat 1 BOX(3;40): 3 steps
lem-nat-1-BOX⟨3·40⟩ : WsL → ⟪ (Sw12 ∷ Bx3-40 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-40 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·40⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-40 ∷ []) (Bx3-40 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ04 ∷ []) (refl) ▸
       at 0 2 (CZ04 ∷ Sw12 ∷ []) (lem-nat-1-CZ04 c4) ▸
       at 0 1 (Bx3-40 ∷ []) (refl) ▸ done


-- nat 1 BOX(4;320): 8 steps
lem-nat-1-BOX⟨4·320⟩ : WsL → ⟪ (Sw12 ∷ Bx4-320 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-310 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·320⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx4-320 ∷ []) (Bx4-310 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff423 ∷ Bx3-40 ∷ Toff423 ∷ CCZ234 ∷ Bx3-40 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0034 c4)) ▸
       at 1 2 (Toff413 ∷ Sw12 ∷ []) (wl0091 c4) ▸
       at 2 2 (Bx3-40 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·40⟩ c4) ▸
       at 3 2 (Toff413 ∷ Sw12 ∷ []) (wl0091 c4) ▸
       at 4 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0034 c4)) ▸
       at 5 2 (Bx3-40 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·40⟩ c4) ▸
       at 0 6 (Bx4-310 ∷ []) (refl) ▸ done


-- nat 1 BOX(3;4120): 8 steps
lem-nat-1-BOX⟨3·4120⟩ : WsL → ⟪ (Sw12 ∷ Bx3-4120 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4210 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·4120⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-4120 ∷ []) (Bx3-4210 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff314 ∷ Bx4-320 ∷ Toff314 ∷ CCZ134 ∷ Bx4-320 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw12 ∷ []) (sym (wl0084 c4)) ▸
       at 1 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 c4) ▸
       at 2 2 (Bx4-310 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·320⟩ c4) ▸
       at 3 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 c4) ▸
       at 4 2 (CCZ234 ∷ Sw12 ∷ []) (sym (wl0084 c4)) ▸
       at 5 2 (Bx4-310 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·320⟩ c4) ▸
       at 0 6 (Bx3-4210 ∷ []) (refl) ▸ done


-- nat 1 SBOX(3;4;0;2): 3 steps
lem-nat-1-SBOX⟨3·4·0·2⟩ : WsL → ⟪ (Sw12 ∷ Sb3-4-0-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-4-0-1 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨3·4·0·2⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb3-4-0-2 ∷ []) (Sb3-4-0-1 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS04 ∷ []) (refl) ▸
       at 0 2 (CS04 ∷ Sw12 ∷ []) (lem-nat-1-CS04 c4) ▸
       at 0 1 (Sb3-4-0-1 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(3;4;0;2): 3 steps
lem-nat-1-SBOXd⟨3·4·0·2⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻3-4-0-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻3-4-0-1 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨3·4·0·2⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻3-4-0-2 ∷ []) (Sb⁻3-4-0-1 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS04⁻ ∷ []) (refl) ▸
       at 0 2 (CS04⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd04 c4) ▸
       at 0 1 (Sb⁻3-4-0-1 ∷ []) (refl) ▸ done


-- nat 1 SBOX(3;4;12;0): 7 steps
lem-nat-1-SBOX⟨3·4·12·0⟩ : WsL → ⟪ (Sw12 ∷ Sb3-4-12-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-4-21-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨3·4·12·0⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb3-4-12-0 ∷ []) (Sb3-4-21-0 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx3-4120 ∷ Toff012 ∷ Sb3-4-0-2 ∷ Toff012 ∷ Sb⁻3-4-0-2 ∷ []) (refl) ▸
       at 0 2 (Bx3-4210 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·4120⟩ c4) ▸
       at 1 2 (Toff012 ∷ Sw12 ∷ []) (wl0038 c4) ▸
       at 2 2 (Sb3-4-0-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·4·0·2⟩ c4) ▸
       at 3 2 (Toff012 ∷ Sw12 ∷ []) (wl0038 c4) ▸
       at 4 2 (Sb⁻3-4-0-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨3·4·0·2⟩ c4) ▸
       at 0 5 (Sb3-4-21-0 ∷ []) (refl) ▸ done


-- nat 1 BOX(4;013): 8 steps
lem-nat-1-BOX⟨4·013⟩ : WsL → ⟪ (Sw12 ∷ Bx4-013 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-023 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·013⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx4-013 ∷ []) (Bx4-023 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff401 ∷ Bx0-43 ∷ Toff401 ∷ CCZ014 ∷ Bx0-43 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 1 2 (Toff402 ∷ Sw12 ∷ []) (lem-nat-1-TOFF401 c4) ▸
       at 2 2 (Bx0-43 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CZ)) ▸
       at 3 2 (Toff402 ∷ Sw12 ∷ []) (lem-nat-1-TOFF401 c4) ▸
       at 4 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 5 2 (Bx0-43 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CZ)) ▸
       at 0 6 (Bx4-023 ∷ []) (refl) ▸ done


-- nat 1 BOX(0;4213): 8 steps
lem-nat-1-BOX⟨0·4213⟩ : WsL → ⟪ (Sw12 ∷ Bx0-4213 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4123 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·4213⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-4213 ∷ []) (Bx0-4123 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff024 ∷ Bx4-013 ∷ Toff024 ∷ CCZ024 ∷ Bx4-013 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 1 2 (Toff014 ∷ Sw12 ∷ []) (lem-nat-1-TOFF024 c4) ▸
       at 2 2 (Bx4-023 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·013⟩ c4) ▸
       at 3 2 (Toff014 ∷ Sw12 ∷ []) (lem-nat-1-TOFF024 c4) ▸
       at 4 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 5 2 (Bx4-023 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·013⟩ c4) ▸
       at 0 6 (Bx0-4123 ∷ []) (refl) ▸ done


-- nat 1 SBOX(0;4;3;1): 2 steps
lem-nat-1-SBOX⟨0·4·3·1⟩ : WsL → ⟪ (Sw12 ∷ Sb0-4-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-4-3-2 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨0·4·3·1⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb0-4-3-1 ∷ []) (Sb0-4-3-2 ∷ Sw12 ∷ [])
  b0 = at 0 2 (Sb0-4-3-1 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS)) ▸
       at 0 1 (Sb0-4-3-2 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 1 SBOXd(0;4;3;1): 2 steps
lem-nat-1-SBOXd⟨0·4·3·1⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻0-4-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-4-3-2 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨0·4·3·1⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻0-4-3-1 ∷ []) (Sb⁻0-4-3-2 ∷ Sw12 ∷ [])
  b0 = at 0 2 (Sb⁻0-4-3-1 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS • CS • CS)) ▸
       at 0 1 (Sb⁻0-4-3-2 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 1 SBOX(0;4;21;3): 7 steps
lem-nat-1-SBOX⟨0·4·21·3⟩ : WsL → ⟪ (Sw12 ∷ Sb0-4-21-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-4-12-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨0·4·21·3⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb0-4-21-3 ∷ []) (Sb0-4-12-3 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx0-4213 ∷ Toff312 ∷ Sb0-4-3-1 ∷ Toff312 ∷ Sb⁻0-4-3-1 ∷ []) (refl) ▸
       at 0 2 (Bx0-4123 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·4213⟩ c4) ▸
       at 1 2 (Toff312 ∷ Sw12 ∷ []) (wl0143 c4) ▸
       at 2 2 (Sb0-4-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·4·3·1⟩ c4) ▸
       at 3 2 (Toff312 ∷ Sw12 ∷ []) (wl0143 c4) ▸
       at 4 2 (Sb⁻0-4-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨0·4·3·1⟩ c4) ▸
       at 0 5 (Sb0-4-12-3 ∷ []) (refl) ▸ done


-- nat 3 SBOX(0;4;3;2): 3 steps
lem-nat-3-SBOX⟨0·4·3·2⟩ : WsL → ⟪ (Sw34 ∷ Sb0-4-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-3-4-2 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨0·4·3·2⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb0-4-3-2 ∷ []) (Sb0-3-4-2 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS34 ∷ []) (refl) ▸
       at 0 2 (CS34 ∷ Sw34 ∷ []) (sym (wl0039 c4)) ▸
       at 0 1 (Sb0-3-4-2 ∷ []) (refl) ▸ done


-- nat 3 SBOX(0;3;4;2): 3 steps
lem-nat-3-SBOX⟨0·3·4·2⟩ : WsL → ⟪ (Sw34 ∷ Sb0-3-4-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-4-3-2 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨0·3·4·2⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb0-3-4-2 ∷ []) (Sb0-4-3-2 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS34 ∷ []) (refl) ▸
       at 0 2 (CS34 ∷ Sw34 ∷ []) (sym (wl0039 c4)) ▸
       at 0 1 (Sb0-4-3-2 ∷ []) (refl) ▸ done


-- nat 3 SBOXd(0;4;3;2): 3 steps
lem-nat-3-SBOXd⟨0·4·3·2⟩ : WsL → ⟪ (Sw34 ∷ Sb⁻0-4-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-3-4-2 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨0·4·3·2⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb⁻0-4-3-2 ∷ []) (Sb⁻0-3-4-2 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS34⁻ ∷ []) (refl) ▸
       at 0 2 (CS34⁻ ∷ Sw34 ∷ []) (sym (wl0040 c4)) ▸
       at 0 1 (Sb⁻0-3-4-2 ∷ []) (refl) ▸ done


-- nat 3 SBOXd(0;3;4;2): 3 steps
lem-nat-3-SBOXd⟨0·3·4·2⟩ : WsL → ⟪ (Sw34 ∷ Sb⁻0-3-4-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-4-3-2 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨0·3·4·2⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb⁻0-3-4-2 ∷ []) (Sb⁻0-4-3-2 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS34⁻ ∷ []) (refl) ▸
       at 0 2 (CS34⁻ ∷ Sw34 ∷ []) (sym (wl0040 c4)) ▸
       at 0 1 (Sb⁻0-4-3-2 ∷ []) (refl) ▸ done


-- comm TOFF013 CSd24: 15 steps
lem-comm-TOFF013-CSd24 : WsL → ⟪ (Toff013 ∷ CS24⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS24⁻ ∷ Toff013 ∷ []) ⟫ʷ
lem-comm-TOFF013-CSd24 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff013 ∷ CS24⁻ ∷ []) (Sw34 ∷ Sw34 ∷ Sw23 ∷ CS34⁻ ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 1 3 (Toff014 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 5 3 (CS24⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS34⁻ ∷ Sw23 ∷ []) (sym (wl0012 c4)) ▸
       at 3 2 (CS34⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (CS • CS • CS)) ▸ done

  b1 : Chain (Sw34 ∷ Sw34 ∷ Sw23 ∷ CS34⁻ ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ []) (CS24⁻ ∷ Toff013 ∷ [])
  b1 = at 2 2 (CS24⁻ ∷ Sw23 ∷ []) (sym (wl0016 c4)) ▸
       at 2 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (wl0007 c4) ▸
       at 2 5 (Toff014 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ Toff013 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0007 c4) ▸
       at 0 3 (CS24⁻ ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 1 BOX(3;014): 8 steps
lem-nat-1-BOX⟨3·014⟩ : WsL → ⟪ (Sw12 ∷ Bx3-014 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-024 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·014⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-014 ∷ []) (Bx3-024 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff301 ∷ Bx0-34 ∷ Toff301 ∷ CCZ013 ∷ Bx0-34 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 1 2 (Toff302 ∷ Sw12 ∷ []) (lem-nat-1-TOFF301 c4) ▸
       at 2 2 (Bx0-34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CZ)) ▸
       at 3 2 (Toff302 ∷ Sw12 ∷ []) (lem-nat-1-TOFF301 c4) ▸
       at 4 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 5 2 (Bx0-34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CZ)) ▸
       at 0 6 (Bx3-024 ∷ []) (refl) ▸ done


-- nat 1 BOX(0;3214): 8 steps
lem-nat-1-BOX⟨0·3214⟩ : WsL → ⟪ (Sw12 ∷ Bx0-3214 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3124 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·3214⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-3214 ∷ []) (Bx0-3124 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff023 ∷ Bx3-014 ∷ Toff023 ∷ CCZ023 ∷ Bx3-014 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 1 2 (Toff013 ∷ Sw12 ∷ []) (lem-nat-1-TOFF023 c4) ▸
       at 2 2 (Bx3-024 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·014⟩ c4) ▸
       at 3 2 (Toff013 ∷ Sw12 ∷ []) (lem-nat-1-TOFF023 c4) ▸
       at 4 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 5 2 (Bx3-024 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·014⟩ c4) ▸
       at 0 6 (Bx0-3124 ∷ []) (refl) ▸ done


-- comm CCZ014 CX23: 9 steps
lem-comm-CCZ014-CX23 : WsL → ⟪ (CCZ014 ∷ CX23 ∷ []) ⟫ʷ ≈ ⟪ (CX23 ∷ CCZ014 ∷ []) ⟫ʷ
lem-comm-CCZ014-CX23 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ014 ∷ CX23 ∷ []) (CX23 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 0 1 (Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 4 3 (CX24 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX34 ∷ Sw23 ∷ []) (sym (wl0051 c4)) ▸
       at 2 2 (CX34 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CX₀₁)) ▸
       at 1 2 (CX24 ∷ Sw23 ∷ []) (sym (wl0050 c4)) ▸
       at 1 1 (Sw34 ∷ CX23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0007 c4) ▸ done

  b1 : Chain (CX23 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ []) (CX23 ∷ CCZ014 ∷ [])
  b1 = at 1 5 (CCZ014 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp CSd24 at 3: 6 steps
lem-resp-CSd24-at-3 : WsL → ⟪ (CS24⁻ ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ CS34⁻ ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-CSd24-at-3 c4 = run b0
  where
  b0 : Chain (CS24⁻ ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ CS34⁻ ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 0 2 (Sw23 ∷ CS34⁻ ∷ []) (wl0016 c4) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 1 2 (Sw12 ∷ CS34⁻ ∷ []) (sym (c₃ (Swap ↑) (CS • CS • CS))) ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 c4)) ▸
       at 2 2 (Sw01 ∷ CS34⁻ ∷ []) (sym (c₂ (Swap) ((CS • CS • CS) ↑))) ▸ done


-- nat 0 BOX(3;102): 8 steps
lem-nat-0-BOX⟨3·102⟩ : WsL → ⟪ (Sw01 ∷ Bx3-102 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-012 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·102⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx3-102 ∷ []) (Bx3-012 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff301 ∷ Bx1-32 ∷ Toff301 ∷ CCZ013 ∷ Bx1-32 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw01 ∷ []) (sym (wl0100 c4)) ▸
       at 1 2 (Toff301 ∷ Sw01 ∷ []) (wl0115 c4) ▸
       at 2 2 (Bx0-32 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·32⟩ c4) ▸
       at 3 2 (Toff301 ∷ Sw01 ∷ []) (wl0115 c4) ▸
       at 4 2 (CCZ013 ∷ Sw01 ∷ []) (sym (wl0100 c4)) ▸
       at 5 2 (Bx0-32 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·32⟩ c4) ▸
       at 0 6 (Bx3-012 ∷ []) (refl) ▸ done


-- nat 0 BOX(1;3402): 8 steps
lem-nat-0-BOX⟨1·3402⟩ : WsL → ⟪ (Sw01 ∷ Bx1-3402 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3412 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·3402⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-3402 ∷ []) (Bx0-3412 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff134 ∷ Bx3-102 ∷ Toff134 ∷ CCZ134 ∷ Bx3-102 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 1 2 (Toff034 ∷ Sw01 ∷ []) (lem-nat-0-TOFF134 c4) ▸
       at 2 2 (Bx3-012 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·102⟩ c4) ▸
       at 3 2 (Toff034 ∷ Sw01 ∷ []) (lem-nat-0-TOFF134 c4) ▸
       at 4 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 5 2 (Bx3-012 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·102⟩ c4) ▸
       at 0 6 (Bx0-3412 ∷ []) (refl) ▸ done


-- nat 1 BOX(3;201): 8 steps
lem-nat-1-BOX⟨3·201⟩ : WsL → ⟪ (Sw12 ∷ Bx3-201 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-102 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·201⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-201 ∷ []) (Bx3-102 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff302 ∷ Bx2-31 ∷ Toff302 ∷ CCZ023 ∷ Bx2-31 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 1 2 (Toff301 ∷ Sw12 ∷ []) (lem-nat-1-TOFF302 c4) ▸
       at 2 2 (Bx1-32 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·31⟩ c4) ▸
       at 3 2 (Toff301 ∷ Sw12 ∷ []) (lem-nat-1-TOFF302 c4) ▸
       at 4 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 5 2 (Bx1-32 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·31⟩ c4) ▸
       at 0 6 (Bx3-102 ∷ []) (refl) ▸ done


-- nat 1 BOX(2;3401): 8 steps
lem-nat-1-BOX⟨2·3401⟩ : WsL → ⟪ (Sw12 ∷ Bx2-3401 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3402 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·3401⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx2-3401 ∷ []) (Bx1-3402 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff234 ∷ Bx3-201 ∷ Toff234 ∷ CCZ234 ∷ Bx3-201 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0034 c4)) ▸
       at 1 2 (Toff134 ∷ Sw12 ∷ []) (wl0140 c4) ▸
       at 2 2 (Bx3-102 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·201⟩ c4) ▸
       at 3 2 (Toff134 ∷ Sw12 ∷ []) (wl0140 c4) ▸
       at 4 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0034 c4)) ▸
       at 5 2 (Bx3-102 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·201⟩ c4) ▸
       at 0 6 (Bx1-3402 ∷ []) (refl) ▸ done


-- nat 0 BOX(3;210): 8 steps
lem-nat-0-BOX⟨3·210⟩ : WsL → ⟪ (Sw01 ∷ Bx3-210 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-201 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·210⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx3-210 ∷ []) (Bx3-201 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff312 ∷ Bx2-30 ∷ Toff312 ∷ CCZ123 ∷ Bx2-30 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw01 ∷ []) (sym (wl0003 c4)) ▸
       at 1 2 (Toff302 ∷ Sw01 ∷ []) (wl0110 c4) ▸
       at 2 2 (Bx2-31 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·30⟩ c4) ▸
       at 3 2 (Toff302 ∷ Sw01 ∷ []) (wl0110 c4) ▸
       at 4 2 (CCZ023 ∷ Sw01 ∷ []) (sym (wl0003 c4)) ▸
       at 5 2 (Bx2-31 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·30⟩ c4) ▸
       at 0 6 (Bx3-201 ∷ []) (refl) ▸ done


-- nat 0 BOX(2;3410): 8 steps
lem-nat-0-BOX⟨2·3410⟩ : WsL → ⟪ (Sw01 ∷ Bx2-3410 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3401 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·3410⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx2-3410 ∷ []) (Bx2-3401 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff234 ∷ Bx3-210 ∷ Toff234 ∷ CCZ234 ∷ Bx3-210 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 1 2 (Toff234 ∷ Sw01 ∷ []) (c₂ (Swap) (Toff)) ▸
       at 2 2 (Bx3-201 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·210⟩ c4) ▸
       at 3 2 (Toff234 ∷ Sw01 ∷ []) (c₂ (Swap) (Toff)) ▸
       at 4 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 5 2 (Bx3-201 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·210⟩ c4) ▸
       at 0 6 (Bx2-3401 ∷ []) (refl) ▸ done


-- nat 0 BOX(2;10): 3 steps
lem-nat-0-BOX⟨2·10⟩ : WsL → ⟪ (Sw01 ∷ Bx2-10 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-01 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·10⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx2-10 ∷ []) (Bx2-01 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CZ01 ∷ []) (refl) ▸
       at 0 2 (CZ01 ∷ Sw01 ∷ []) (sym (wl0130 c4)) ▸
       at 0 1 (Bx2-01 ∷ []) (refl) ▸ done


-- nat 0 BOX(3;012): 8 steps
lem-nat-0-BOX⟨3·012⟩ : WsL → ⟪ (Sw01 ∷ Bx3-012 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-102 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·012⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx3-012 ∷ []) (Bx3-102 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff301 ∷ Bx0-32 ∷ Toff301 ∷ CCZ013 ∷ Bx0-32 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw01 ∷ []) (sym (wl0100 c4)) ▸
       at 1 2 (Toff301 ∷ Sw01 ∷ []) (wl0115 c4) ▸
       at 2 2 (Bx1-32 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·32⟩ c4) ▸
       at 3 2 (Toff301 ∷ Sw01 ∷ []) (wl0115 c4) ▸
       at 4 2 (CCZ013 ∷ Sw01 ∷ []) (sym (wl0100 c4)) ▸
       at 5 2 (Bx1-32 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·32⟩ c4) ▸
       at 0 6 (Bx3-102 ∷ []) (refl) ▸ done


-- nat 0 BOX(0;3412): 8 steps
lem-nat-0-BOX⟨0·3412⟩ : WsL → ⟪ (Sw01 ∷ Bx0-3412 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3402 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·3412⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-3412 ∷ []) (Bx1-3402 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff034 ∷ Bx3-012 ∷ Toff034 ∷ CCZ034 ∷ Bx3-012 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4) ▸
       at 1 2 (Toff134 ∷ Sw01 ∷ []) (lem-nat-0-TOFF034 c4) ▸
       at 2 2 (Bx3-102 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·012⟩ c4) ▸
       at 3 2 (Toff134 ∷ Sw01 ∷ []) (lem-nat-0-TOFF034 c4) ▸
       at 4 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4) ▸
       at 5 2 (Bx3-102 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·012⟩ c4) ▸
       at 0 6 (Bx1-3402 ∷ []) (refl) ▸ done


-- nat 1 BOX(3;102): 8 steps
lem-nat-1-BOX⟨3·102⟩ : WsL → ⟪ (Sw12 ∷ Bx3-102 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-201 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·102⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-102 ∷ []) (Bx3-201 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff301 ∷ Bx1-32 ∷ Toff301 ∷ CCZ013 ∷ Bx1-32 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 1 2 (Toff302 ∷ Sw12 ∷ []) (lem-nat-1-TOFF301 c4) ▸
       at 2 2 (Bx2-31 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·32⟩ c4) ▸
       at 3 2 (Toff302 ∷ Sw12 ∷ []) (lem-nat-1-TOFF301 c4) ▸
       at 4 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 5 2 (Bx2-31 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·32⟩ c4) ▸
       at 0 6 (Bx3-201 ∷ []) (refl) ▸ done


-- nat 1 BOX(1;3402): 8 steps
lem-nat-1-BOX⟨1·3402⟩ : WsL → ⟪ (Sw12 ∷ Bx1-3402 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3401 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·3402⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx1-3402 ∷ []) (Bx2-3401 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff134 ∷ Bx3-102 ∷ Toff134 ∷ CCZ134 ∷ Bx3-102 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw12 ∷ []) (sym (wl0084 c4)) ▸
       at 1 2 (Toff234 ∷ Sw12 ∷ []) (wl0136 c4) ▸
       at 2 2 (Bx3-201 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·102⟩ c4) ▸
       at 3 2 (Toff234 ∷ Sw12 ∷ []) (wl0136 c4) ▸
       at 4 2 (CCZ234 ∷ Sw12 ∷ []) (sym (wl0084 c4)) ▸
       at 5 2 (Bx3-201 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·102⟩ c4) ▸
       at 0 6 (Bx2-3401 ∷ []) (refl) ▸ done


-- nat 0 BOX(3;201): 8 steps
lem-nat-0-BOX⟨3·201⟩ : WsL → ⟪ (Sw01 ∷ Bx3-201 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-210 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·201⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx3-201 ∷ []) (Bx3-210 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff302 ∷ Bx2-31 ∷ Toff302 ∷ CCZ023 ∷ Bx2-31 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw01 ∷ []) (sym (wl0103 c4)) ▸
       at 1 2 (Toff312 ∷ Sw01 ∷ []) (wl0116 c4) ▸
       at 2 2 (Bx2-30 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·31⟩ c4) ▸
       at 3 2 (Toff312 ∷ Sw01 ∷ []) (wl0116 c4) ▸
       at 4 2 (CCZ123 ∷ Sw01 ∷ []) (sym (wl0103 c4)) ▸
       at 5 2 (Bx2-30 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·31⟩ c4) ▸
       at 0 6 (Bx3-210 ∷ []) (refl) ▸ done


-- nat 0 BOX(2;3401): 8 steps
lem-nat-0-BOX⟨2·3401⟩ : WsL → ⟪ (Sw01 ∷ Bx2-3401 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3410 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·3401⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx2-3401 ∷ []) (Bx2-3410 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff234 ∷ Bx3-201 ∷ Toff234 ∷ CCZ234 ∷ Bx3-201 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 1 2 (Toff234 ∷ Sw01 ∷ []) (c₂ (Swap) (Toff)) ▸
       at 2 2 (Bx3-210 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·201⟩ c4) ▸
       at 3 2 (Toff234 ∷ Sw01 ∷ []) (c₂ (Swap) (Toff)) ▸
       at 4 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 5 2 (Bx3-210 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·201⟩ c4) ▸
       at 0 6 (Bx2-3410 ∷ []) (refl) ▸ done


-- resp CSd04 at 2: 12 steps
lem-resp-CSd04-at-2 : WsL → ⟪ (CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CS14⁻ ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CSd04-at-2 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CS04⁻ ∷ []) (Sw12 ∷ Sw34 ∷ CS03⁻ ∷ Sw34 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 0 1 (Sw34 ∷ CS03⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 1 2 (Sw12 ∷ CS03⁻ ∷ []) (wl0023 c4) ▸
       at 0 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 1 3 (CS04⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 c4)) ▸
       at 1 1 (Sw34 ∷ CS03⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw12 ∷ Sw34 ∷ CS03⁻ ∷ Sw34 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw01 ∷ CS14⁻ ∷ Sw01 ∷ Sw12 ∷ [])
  b1 = at 3 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 2 2 (Sw01 ∷ CS13⁻ ∷ []) (wl0022 c4) ▸
       at 1 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 2 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 3 BOX(1;03): 3 steps
lem-nat-3-BOX⟨1·03⟩ : WsL → ⟪ (Sw34 ∷ Bx1-03 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-04 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨1·03⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx1-03 ∷ []) (Bx1-04 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CZ03 ∷ []) (refl) ▸
       at 0 2 (CZ04 ∷ Sw34 ∷ []) (lem-nat-3-CZ03 c4) ▸
       at 0 1 (Bx1-04 ∷ []) (refl) ▸ done


-- nat 3 BOX(1;04): 3 steps
lem-nat-3-BOX⟨1·04⟩ : WsL → ⟪ (Sw34 ∷ Bx1-04 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-03 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨1·04⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx1-04 ∷ []) (Bx1-03 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CZ04 ∷ []) (refl) ▸
       at 0 2 (CZ03 ∷ Sw34 ∷ []) (lem-nat-3-CZ04 c4) ▸
       at 0 1 (Bx1-03 ∷ []) (refl) ▸ done

