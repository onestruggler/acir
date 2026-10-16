{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.R016 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (WsL ; wl0001 ; wl0002 ; wl0003 ; wl0004 ; wl0006 ; wl0007 ; wl0008 ; wl0009 ; wl0010 ; wl0011 ; wl0012 ; wl0013 ; wl0014 ; wl0015 ; wl0016 ; wl0017 ; wl0018 ; wl0019 ; wl0020 ; wl0021 ; wl0025 ; wl0030 ; wl0034 ; wl0042 ; wl0046 ; wl0053 ; wl0057 ; wl0058 ; wl0061 ; wl0065 ; wl0067 ; wl0068 ; wl0078 ; wl0082 ; wl0084 ; wl0089 ; wl0090 ; wl0091 ; wl0093 ; wl0095 ; wl0103 ; wl0104 ; wl0108 ; wl0110 ; wl0111 ; wl0112 ; wl0116 ; wl0117 ; wl0121 ; wl0122 ; wl0124 ; wl0126 ; wl0132 ; wl0133 ; wl0136 ; wl0138 ; wl0139 ; wl0140 ; wl0143 ; wl0146 ; wl0159 ; wl0160 ; wl0161 ; wl0162 ; wl0163 ; wl0164 ; wl0165)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-nat-1-CCZ023 ; lem-nat-1-CCZ024 ; lem-nat-1-CCZ034 ; lem-nat-1-TOFF014 ; lem-nat-1-TOFF024 ; lem-nat-1-TOFF203 ; lem-nat-2-CCZ012 ; lem-nat-2-CCZ013 ; lem-nat-2-CCZ024 ; lem-nat-2-CCZ034 ; lem-nat-2-TOFF024 ; lem-nat-2-TOFF034 ; lem-nat-2-TOFF102 ; lem-nat-2-TOFF103 ; lem-nat-3-CCZ024)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-0-CCZ024 ; lem-nat-0-CCZ124 ; lem-nat-1-CCZ013 ; lem-nat-1-CCZ014 ; lem-nat-1-TOFF103 ; lem-nat-1-TOFF301 ; lem-nat-1-TOFF302 ; lem-nat-2-CCZ124 ; lem-nat-2-CCZ134 ; lem-nat-2-TOFF304 ; lem-nat-3-CCZ023 ; lem-nat-3-TOFF203 ; lem-nat-3-TOFF204)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-0-CCZ034 ; lem-nat-0-CCZ134)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-0-TOFF204 ; lem-nat-0-TOFF214 ; lem-nat-3-TOFF023 ; lem-nat-3-TOFF214)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-0-TOFF024 ; lem-nat-1-TOFF401 ; lem-nat-2-CCZ014 ; lem-nat-2-TOFF214 ; lem-nat-3-CCZ123 ; lem-nat-3-CCZ124)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-1-CZ02 ; lem-nat-2-CS13 ; lem-nat-2-CSd13 ; lem-nat-2-CZ12 ; lem-nat-2-CZ13 ; lem-nat-2-TOFF314)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-0-BOX⟨2·01⟩ ; lem-nat-0-TOFF134 ; lem-nat-1-BOX⟨2·10⟩ ; lem-nat-2-BOX⟨0·42⟩ ; lem-nat-2-BOX⟨0·43⟩ ; lem-nat-2-TOFF124 ; lem-nat-2-TOFF403)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-nat-0-BOX⟨0·3142⟩ ; lem-nat-0-TOFF034 ; lem-nat-1-TOFF034 ; lem-nat-1-TOFF403 ; lem-nat-3-TOFF024)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-1-TOFF402 ; lem-nat-2-TOFF401)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-nat-1-BOX⟨1·30⟩ ; lem-nat-1-BOX⟨2·30⟩ ; lem-nat-3-TOFF213)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-nat-0-BOX⟨1·0432⟩)
open import Examples.Groups.Clifford+CS.Five.D.R012 using (lem-nat-0-BOX⟨2·10⟩ ; lem-nat-2-BOX⟨1·32⟩ ; lem-nat-3-BOX⟨1·23⟩ ; lem-nat-3-BOX⟨1·24⟩)
open import Examples.Groups.Clifford+CS.Five.D.R013 using (lem-nat-2-BOX⟨1·23⟩)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-nat-1-BOX⟨0·31⟩ ; lem-nat-1-BOX⟨0·32⟩ ; lem-nat-1-BOX⟨0·3241⟩)
open import Examples.Groups.Clifford+CS.Five.D.R015 using (lem-nat-0-BOX⟨0·31⟩ ; lem-nat-0-BOX⟨1·30⟩ ; lem-nat-0-BOX⟨1·3240⟩ ; lem-nat-1-BOX⟨0·42⟩ ; lem-nat-1-BOX⟨3·14⟩ ; lem-nat-1-BOX⟨3·24⟩)
-- nat 1 BOX(0;41): 3 steps
lem-nat-1-BOX⟨0·41⟩ : WsL → ⟪ (Sw12 ∷ Bx0-41 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-42 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·41⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-41 ∷ []) (Bx0-42 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ14 ∷ []) (refl) ▸
       at 0 2 (CZ24 ∷ Sw12 ∷ []) (sym (wl0089 c4)) ▸
       at 0 1 (Bx0-42 ∷ []) (refl) ▸ done


-- nat 1 BOX(4;031): 8 steps
lem-nat-1-BOX⟨4·031⟩ : WsL → ⟪ (Sw12 ∷ Bx4-031 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-032 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·031⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx4-031 ∷ []) (Bx4-032 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff403 ∷ Bx0-41 ∷ Toff403 ∷ CCZ034 ∷ Bx0-41 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 1 2 (Toff403 ∷ Sw12 ∷ []) (lem-nat-1-TOFF403 c4) ▸
       at 2 2 (Bx0-42 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·41⟩ c4) ▸
       at 3 2 (Toff403 ∷ Sw12 ∷ []) (lem-nat-1-TOFF403 c4) ▸
       at 4 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 5 2 (Bx0-42 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·41⟩ c4) ▸
       at 0 6 (Bx4-032 ∷ []) (refl) ▸ done


-- nat 1 BOX(0;4231): 8 steps
lem-nat-1-BOX⟨0·4231⟩ : WsL → ⟪ (Sw12 ∷ Bx0-4231 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4132 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·4231⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-4231 ∷ []) (Bx0-4132 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff024 ∷ Bx4-031 ∷ Toff024 ∷ CCZ024 ∷ Bx4-031 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 1 2 (Toff014 ∷ Sw12 ∷ []) (lem-nat-1-TOFF024 c4) ▸
       at 2 2 (Bx4-032 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·031⟩ c4) ▸
       at 3 2 (Toff014 ∷ Sw12 ∷ []) (lem-nat-1-TOFF024 c4) ▸
       at 4 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 5 2 (Bx4-032 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·031⟩ c4) ▸
       at 0 6 (Bx0-4132 ∷ []) (refl) ▸ done


-- nat 1 BOX(4;023): 8 steps
lem-nat-1-BOX⟨4·023⟩ : WsL → ⟪ (Sw12 ∷ Bx4-023 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-013 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·023⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx4-023 ∷ []) (Bx4-013 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff402 ∷ Bx0-43 ∷ Toff402 ∷ CCZ024 ∷ Bx0-43 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 1 2 (Toff401 ∷ Sw12 ∷ []) (lem-nat-1-TOFF402 c4) ▸
       at 2 2 (Bx0-43 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CZ)) ▸
       at 3 2 (Toff401 ∷ Sw12 ∷ []) (lem-nat-1-TOFF402 c4) ▸
       at 4 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 5 2 (Bx0-43 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CZ)) ▸
       at 0 6 (Bx4-013 ∷ []) (refl) ▸ done


-- nat 1 BOX(0;4123): 8 steps
lem-nat-1-BOX⟨0·4123⟩ : WsL → ⟪ (Sw12 ∷ Bx0-4123 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4213 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·4123⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-4123 ∷ []) (Bx0-4213 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff014 ∷ Bx4-023 ∷ Toff014 ∷ CCZ014 ∷ Bx4-023 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 1 2 (Toff024 ∷ Sw12 ∷ []) (lem-nat-1-TOFF014 c4) ▸
       at 2 2 (Bx4-013 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·023⟩ c4) ▸
       at 3 2 (Toff024 ∷ Sw12 ∷ []) (lem-nat-1-TOFF014 c4) ▸
       at 4 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 5 2 (Bx4-013 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·023⟩ c4) ▸
       at 0 6 (Bx0-4213 ∷ []) (refl) ▸ done


-- nat 2 BOX(4;013): 8 steps
lem-nat-2-BOX⟨4·013⟩ : WsL → ⟪ (Sw23 ∷ Bx4-013 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-012 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·013⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx4-013 ∷ []) (Bx4-012 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff401 ∷ Bx0-43 ∷ Toff401 ∷ CCZ014 ∷ Bx0-43 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 1 2 (Toff401 ∷ Sw23 ∷ []) (lem-nat-2-TOFF401 c4) ▸
       at 2 2 (Bx0-42 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·43⟩ c4) ▸
       at 3 2 (Toff401 ∷ Sw23 ∷ []) (lem-nat-2-TOFF401 c4) ▸
       at 4 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 5 2 (Bx0-42 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·43⟩ c4) ▸
       at 0 6 (Bx4-012 ∷ []) (refl) ▸ done


-- nat 2 BOX(0;4213): 8 steps
lem-nat-2-BOX⟨0·4213⟩ : WsL → ⟪ (Sw23 ∷ Bx0-4213 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4312 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·4213⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-4213 ∷ []) (Bx0-4312 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff024 ∷ Bx4-013 ∷ Toff024 ∷ CCZ024 ∷ Bx4-013 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 1 2 (Toff034 ∷ Sw23 ∷ []) (lem-nat-2-TOFF024 c4) ▸
       at 2 2 (Bx4-012 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·013⟩ c4) ▸
       at 3 2 (Toff034 ∷ Sw23 ∷ []) (lem-nat-2-TOFF024 c4) ▸
       at 4 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 5 2 (Bx4-012 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·013⟩ c4) ▸
       at 0 6 (Bx0-4312 ∷ []) (refl) ▸ done


-- nat 1 BOX(4;012): 8 steps
lem-nat-1-BOX⟨4·012⟩ : WsL → ⟪ (Sw12 ∷ Bx4-012 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-021 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·012⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx4-012 ∷ []) (Bx4-021 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff401 ∷ Bx0-42 ∷ Toff401 ∷ CCZ014 ∷ Bx0-42 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 1 2 (Toff402 ∷ Sw12 ∷ []) (lem-nat-1-TOFF401 c4) ▸
       at 2 2 (Bx0-41 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·42⟩ c4) ▸
       at 3 2 (Toff402 ∷ Sw12 ∷ []) (lem-nat-1-TOFF401 c4) ▸
       at 4 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 5 2 (Bx0-41 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·42⟩ c4) ▸
       at 0 6 (Bx4-021 ∷ []) (refl) ▸ done


-- nat 1 BOX(0;4312): 8 steps
lem-nat-1-BOX⟨0·4312⟩ : WsL → ⟪ (Sw12 ∷ Bx0-4312 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4321 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·4312⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-4312 ∷ []) (Bx0-4321 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff034 ∷ Bx4-012 ∷ Toff034 ∷ CCZ034 ∷ Bx4-012 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 1 2 (Toff034 ∷ Sw12 ∷ []) (lem-nat-1-TOFF034 c4) ▸
       at 2 2 (Bx4-021 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·012⟩ c4) ▸
       at 3 2 (Toff034 ∷ Sw12 ∷ []) (lem-nat-1-TOFF034 c4) ▸
       at 4 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 5 2 (Bx4-021 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·012⟩ c4) ▸
       at 0 6 (Bx0-4321 ∷ []) (refl) ▸ done


-- nat 2 BOX(4;012): 8 steps
lem-nat-2-BOX⟨4·012⟩ : WsL → ⟪ (Sw23 ∷ Bx4-012 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-013 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·012⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx4-012 ∷ []) (Bx4-013 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff401 ∷ Bx0-42 ∷ Toff401 ∷ CCZ014 ∷ Bx0-42 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 1 2 (Toff401 ∷ Sw23 ∷ []) (lem-nat-2-TOFF401 c4) ▸
       at 2 2 (Bx0-43 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·42⟩ c4) ▸
       at 3 2 (Toff401 ∷ Sw23 ∷ []) (lem-nat-2-TOFF401 c4) ▸
       at 4 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 5 2 (Bx0-43 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·42⟩ c4) ▸
       at 0 6 (Bx4-013 ∷ []) (refl) ▸ done


-- nat 2 BOX(0;4312): 8 steps
lem-nat-2-BOX⟨0·4312⟩ : WsL → ⟪ (Sw23 ∷ Bx0-4312 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4213 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·4312⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-4312 ∷ []) (Bx0-4213 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff034 ∷ Bx4-012 ∷ Toff034 ∷ CCZ034 ∷ Bx4-012 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 1 2 (Toff024 ∷ Sw23 ∷ []) (lem-nat-2-TOFF034 c4) ▸
       at 2 2 (Bx4-013 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·012⟩ c4) ▸
       at 3 2 (Toff024 ∷ Sw23 ∷ []) (lem-nat-2-TOFF034 c4) ▸
       at 4 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 5 2 (Bx4-013 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·012⟩ c4) ▸
       at 0 6 (Bx0-4213 ∷ []) (refl) ▸ done


-- nat 1 BOX(4;021): 8 steps
lem-nat-1-BOX⟨4·021⟩ : WsL → ⟪ (Sw12 ∷ Bx4-021 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-012 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·021⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx4-021 ∷ []) (Bx4-012 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff402 ∷ Bx0-41 ∷ Toff402 ∷ CCZ024 ∷ Bx0-41 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 1 2 (Toff401 ∷ Sw12 ∷ []) (lem-nat-1-TOFF402 c4) ▸
       at 2 2 (Bx0-42 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·41⟩ c4) ▸
       at 3 2 (Toff401 ∷ Sw12 ∷ []) (lem-nat-1-TOFF402 c4) ▸
       at 4 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 5 2 (Bx0-42 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·41⟩ c4) ▸
       at 0 6 (Bx4-012 ∷ []) (refl) ▸ done


-- nat 1 BOX(0;4321): 8 steps
lem-nat-1-BOX⟨0·4321⟩ : WsL → ⟪ (Sw12 ∷ Bx0-4321 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4312 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·4321⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-4321 ∷ []) (Bx0-4312 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff034 ∷ Bx4-021 ∷ Toff034 ∷ CCZ034 ∷ Bx4-021 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 1 2 (Toff034 ∷ Sw12 ∷ []) (lem-nat-1-TOFF034 c4) ▸
       at 2 2 (Bx4-012 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·021⟩ c4) ▸
       at 3 2 (Toff034 ∷ Sw12 ∷ []) (lem-nat-1-TOFF034 c4) ▸
       at 4 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 5 2 (Bx4-012 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·021⟩ c4) ▸
       at 0 6 (Bx0-4312 ∷ []) (refl) ▸ done


-- nat 2 BOX(0;41): 3 steps
lem-nat-2-BOX⟨0·41⟩ : WsL → ⟪ (Sw23 ∷ Bx0-41 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-41 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·41⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-41 ∷ []) (Bx0-41 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ14 ∷ []) (refl) ▸
       at 0 2 (CZ14 ∷ Sw23 ∷ []) (sym (wl0042 c4)) ▸
       at 0 1 (Bx0-41 ∷ []) (refl) ▸ done


-- nat 2 BOX(4;031): 8 steps
lem-nat-2-BOX⟨4·031⟩ : WsL → ⟪ (Sw23 ∷ Bx4-031 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-021 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·031⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx4-031 ∷ []) (Bx4-021 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff403 ∷ Bx0-41 ∷ Toff403 ∷ CCZ034 ∷ Bx0-41 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 1 2 (Toff402 ∷ Sw23 ∷ []) (lem-nat-2-TOFF403 c4) ▸
       at 2 2 (Bx0-41 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·41⟩ c4) ▸
       at 3 2 (Toff402 ∷ Sw23 ∷ []) (lem-nat-2-TOFF403 c4) ▸
       at 4 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 5 2 (Bx0-41 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·41⟩ c4) ▸
       at 0 6 (Bx4-021 ∷ []) (refl) ▸ done


-- nat 2 BOX(0;4231): 8 steps
lem-nat-2-BOX⟨0·4231⟩ : WsL → ⟪ (Sw23 ∷ Bx0-4231 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4321 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·4231⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-4231 ∷ []) (Bx0-4321 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff024 ∷ Bx4-031 ∷ Toff024 ∷ CCZ024 ∷ Bx4-031 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 1 2 (Toff034 ∷ Sw23 ∷ []) (lem-nat-2-TOFF024 c4) ▸
       at 2 2 (Bx4-021 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·031⟩ c4) ▸
       at 3 2 (Toff034 ∷ Sw23 ∷ []) (lem-nat-2-TOFF024 c4) ▸
       at 4 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 5 2 (Bx4-021 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·031⟩ c4) ▸
       at 0 6 (Bx0-4321 ∷ []) (refl) ▸ done


-- resp CX40 at 3: 20 steps
lem-resp-CX40-at-3 : WsL → ⟪ (CX40 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ CX41 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-CX40-at-3 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX40 ∷ []) (Sw23 ∷ CX40 ∷ Sw23 ∷ [])
  b0 = at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 0 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (wl0013 c4) ▸
       at 4 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 3 2 (Sw34 ∷ CX10 ∷ []) (c₂ (CX₁₀) (Swap ↑)) ▸
       at 2 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 0 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (sym (wl0013 c4)) ▸
       at 1 7 (CX40 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ CX40 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ CX30 ∷ Sw34 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b1 = at 2 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 1 1 (Sw34 ∷ CX30 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 2 2 (Sw12 ∷ CX30 ∷ []) (wl0124 c4) ▸
       at 1 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 2 3 (CX40 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 c4)) ▸
       at 2 1 (Sw34 ∷ CX30 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ CX30 ∷ Sw34 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ CX41 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b2 = at 4 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 3 2 (Sw01 ∷ CX31 ∷ []) (wl0122 c4) ▸
       at 2 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 3 3 (CX41 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 1 BOX(1;304): 8 steps
lem-nat-1-BOX⟨1·304⟩ : WsL → ⟪ (Sw12 ∷ Bx1-304 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-304 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·304⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx1-304 ∷ []) (Bx2-304 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff103 ∷ Bx3-14 ∷ Toff103 ∷ CCZ013 ∷ Bx3-14 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 1 2 (Toff203 ∷ Sw12 ∷ []) (lem-nat-1-TOFF103 c4) ▸
       at 2 2 (Bx3-24 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·14⟩ c4) ▸
       at 3 2 (Toff203 ∷ Sw12 ∷ []) (lem-nat-1-TOFF103 c4) ▸
       at 4 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 5 2 (Bx3-24 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·14⟩ c4) ▸
       at 0 6 (Bx2-304 ∷ []) (refl) ▸ done


-- nat 1 BOX(3;1204): 8 steps
lem-nat-1-BOX⟨3·1204⟩ : WsL → ⟪ (Sw12 ∷ Bx3-1204 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2104 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·1204⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-1204 ∷ []) (Bx3-2104 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff312 ∷ Bx1-304 ∷ Toff312 ∷ CCZ123 ∷ Bx1-304 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw12 ∷ []) (sym (wl0111 c4)) ▸
       at 1 2 (Toff312 ∷ Sw12 ∷ []) (wl0143 c4) ▸
       at 2 2 (Bx2-304 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·304⟩ c4) ▸
       at 3 2 (Toff312 ∷ Sw12 ∷ []) (wl0143 c4) ▸
       at 4 2 (CCZ123 ∷ Sw12 ∷ []) (sym (wl0111 c4)) ▸
       at 5 2 (Bx2-304 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·304⟩ c4) ▸
       at 0 6 (Bx3-2104 ∷ []) (refl) ▸ done


-- nat 0 BOX(2;304): 8 steps
lem-nat-0-BOX⟨2·304⟩ : WsL → ⟪ (Sw01 ∷ Bx2-304 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-314 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·304⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx2-304 ∷ []) (Bx2-314 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff203 ∷ Bx3-24 ∷ Toff203 ∷ CCZ023 ∷ Bx3-24 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw01 ∷ []) (sym (wl0103 c4)) ▸
       at 1 2 (Toff213 ∷ Sw01 ∷ []) (wl0104 c4) ▸
       at 2 2 (Bx3-24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CZ • Swap ↑)) ▸
       at 3 2 (Toff213 ∷ Sw01 ∷ []) (wl0104 c4) ▸
       at 4 2 (CCZ123 ∷ Sw01 ∷ []) (sym (wl0103 c4)) ▸
       at 5 2 (Bx3-24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CZ • Swap ↑)) ▸
       at 0 6 (Bx2-314 ∷ []) (refl) ▸ done


-- nat 0 BOX(3;2104): 8 steps
lem-nat-0-BOX⟨3·2104⟩ : WsL → ⟪ (Sw01 ∷ Bx3-2104 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2014 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·2104⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx3-2104 ∷ []) (Bx3-2014 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff312 ∷ Bx2-304 ∷ Toff312 ∷ CCZ123 ∷ Bx2-304 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw01 ∷ []) (sym (wl0003 c4)) ▸
       at 1 2 (Toff302 ∷ Sw01 ∷ []) (wl0110 c4) ▸
       at 2 2 (Bx2-314 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·304⟩ c4) ▸
       at 3 2 (Toff302 ∷ Sw01 ∷ []) (wl0110 c4) ▸
       at 4 2 (CCZ023 ∷ Sw01 ∷ []) (sym (wl0003 c4)) ▸
       at 5 2 (Bx2-314 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·304⟩ c4) ▸
       at 0 6 (Bx3-2014 ∷ []) (refl) ▸ done


-- nat 0 BOX(2;314): 8 steps
lem-nat-0-BOX⟨2·314⟩ : WsL → ⟪ (Sw01 ∷ Bx2-314 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-304 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·314⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx2-314 ∷ []) (Bx2-304 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff213 ∷ Bx3-24 ∷ Toff213 ∷ CCZ123 ∷ Bx3-24 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw01 ∷ []) (sym (wl0003 c4)) ▸
       at 1 2 (Toff203 ∷ Sw01 ∷ []) (wl0004 c4) ▸
       at 2 2 (Bx3-24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CZ • Swap ↑)) ▸
       at 3 2 (Toff203 ∷ Sw01 ∷ []) (wl0004 c4) ▸
       at 4 2 (CCZ023 ∷ Sw01 ∷ []) (sym (wl0003 c4)) ▸
       at 5 2 (Bx3-24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CZ • Swap ↑)) ▸
       at 0 6 (Bx2-304 ∷ []) (refl) ▸ done


-- nat 0 BOX(3;2014): 8 steps
lem-nat-0-BOX⟨3·2014⟩ : WsL → ⟪ (Sw01 ∷ Bx3-2014 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2104 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·2014⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx3-2014 ∷ []) (Bx3-2104 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff302 ∷ Bx2-314 ∷ Toff302 ∷ CCZ023 ∷ Bx2-314 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw01 ∷ []) (sym (wl0103 c4)) ▸
       at 1 2 (Toff312 ∷ Sw01 ∷ []) (wl0116 c4) ▸
       at 2 2 (Bx2-304 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·314⟩ c4) ▸
       at 3 2 (Toff312 ∷ Sw01 ∷ []) (wl0116 c4) ▸
       at 4 2 (CCZ123 ∷ Sw01 ∷ []) (sym (wl0103 c4)) ▸
       at 5 2 (Bx2-304 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·314⟩ c4) ▸
       at 0 6 (Bx3-2104 ∷ []) (refl) ▸ done


-- nat 1 BOX(2;304): 8 steps
lem-nat-1-BOX⟨2·304⟩ : WsL → ⟪ (Sw12 ∷ Bx2-304 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-304 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·304⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx2-304 ∷ []) (Bx1-304 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff203 ∷ Bx3-24 ∷ Toff203 ∷ CCZ023 ∷ Bx3-24 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 1 2 (Toff103 ∷ Sw12 ∷ []) (lem-nat-1-TOFF203 c4) ▸
       at 2 2 (Bx3-14 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·24⟩ c4) ▸
       at 3 2 (Toff103 ∷ Sw12 ∷ []) (lem-nat-1-TOFF203 c4) ▸
       at 4 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 5 2 (Bx3-14 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·24⟩ c4) ▸
       at 0 6 (Bx1-304 ∷ []) (refl) ▸ done


-- nat 1 BOX(3;2104): 8 steps
lem-nat-1-BOX⟨3·2104⟩ : WsL → ⟪ (Sw12 ∷ Bx3-2104 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1204 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·2104⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-2104 ∷ []) (Bx3-1204 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff312 ∷ Bx2-304 ∷ Toff312 ∷ CCZ123 ∷ Bx2-304 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw12 ∷ []) (sym (wl0111 c4)) ▸
       at 1 2 (Toff312 ∷ Sw12 ∷ []) (wl0143 c4) ▸
       at 2 2 (Bx1-304 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·304⟩ c4) ▸
       at 3 2 (Toff312 ∷ Sw12 ∷ []) (wl0143 c4) ▸
       at 4 2 (CCZ123 ∷ Sw12 ∷ []) (sym (wl0111 c4)) ▸
       at 5 2 (Bx1-304 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·304⟩ c4) ▸
       at 0 6 (Bx3-1204 ∷ []) (refl) ▸ done


-- nat 1 BOX(3;012): 8 steps
lem-nat-1-BOX⟨3·012⟩ : WsL → ⟪ (Sw12 ∷ Bx3-012 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-021 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·012⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-012 ∷ []) (Bx3-021 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff301 ∷ Bx0-32 ∷ Toff301 ∷ CCZ013 ∷ Bx0-32 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 1 2 (Toff302 ∷ Sw12 ∷ []) (lem-nat-1-TOFF301 c4) ▸
       at 2 2 (Bx0-31 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·32⟩ c4) ▸
       at 3 2 (Toff302 ∷ Sw12 ∷ []) (lem-nat-1-TOFF301 c4) ▸
       at 4 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 5 2 (Bx0-31 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·32⟩ c4) ▸
       at 0 6 (Bx3-021 ∷ []) (refl) ▸ done


-- nat 1 BOX(0;3412): 8 steps
lem-nat-1-BOX⟨0·3412⟩ : WsL → ⟪ (Sw12 ∷ Bx0-3412 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3421 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·3412⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-3412 ∷ []) (Bx0-3421 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff034 ∷ Bx3-012 ∷ Toff034 ∷ CCZ034 ∷ Bx3-012 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 1 2 (Toff034 ∷ Sw12 ∷ []) (lem-nat-1-TOFF034 c4) ▸
       at 2 2 (Bx3-021 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·012⟩ c4) ▸
       at 3 2 (Toff034 ∷ Sw12 ∷ []) (lem-nat-1-TOFF034 c4) ▸
       at 4 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 5 2 (Bx3-021 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·012⟩ c4) ▸
       at 0 6 (Bx0-3421 ∷ []) (refl) ▸ done


-- nat 1 BOX(3;120): 8 steps
lem-nat-1-BOX⟨3·120⟩ : WsL → ⟪ (Sw12 ∷ Bx3-120 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-210 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·120⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-120 ∷ []) (Bx3-210 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff312 ∷ Bx1-30 ∷ Toff312 ∷ CCZ123 ∷ Bx1-30 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw12 ∷ []) (sym (wl0111 c4)) ▸
       at 1 2 (Toff312 ∷ Sw12 ∷ []) (wl0143 c4) ▸
       at 2 2 (Bx2-30 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·30⟩ c4) ▸
       at 3 2 (Toff312 ∷ Sw12 ∷ []) (wl0143 c4) ▸
       at 4 2 (CCZ123 ∷ Sw12 ∷ []) (sym (wl0111 c4)) ▸
       at 5 2 (Bx2-30 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·30⟩ c4) ▸
       at 0 6 (Bx3-210 ∷ []) (refl) ▸ done


-- nat 1 BOX(1;3420): 8 steps
lem-nat-1-BOX⟨1·3420⟩ : WsL → ⟪ (Sw12 ∷ Bx1-3420 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3410 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·3420⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx1-3420 ∷ []) (Bx2-3410 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff134 ∷ Bx3-120 ∷ Toff134 ∷ CCZ134 ∷ Bx3-120 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw12 ∷ []) (sym (wl0084 c4)) ▸
       at 1 2 (Toff234 ∷ Sw12 ∷ []) (wl0136 c4) ▸
       at 2 2 (Bx3-210 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·120⟩ c4) ▸
       at 3 2 (Toff234 ∷ Sw12 ∷ []) (wl0136 c4) ▸
       at 4 2 (CCZ234 ∷ Sw12 ∷ []) (sym (wl0084 c4)) ▸
       at 5 2 (Bx3-210 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·120⟩ c4) ▸
       at 0 6 (Bx2-3410 ∷ []) (refl) ▸ done


-- nat 1 BOX(3;210): 8 steps
lem-nat-1-BOX⟨3·210⟩ : WsL → ⟪ (Sw12 ∷ Bx3-210 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-120 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·210⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-210 ∷ []) (Bx3-120 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff312 ∷ Bx2-30 ∷ Toff312 ∷ CCZ123 ∷ Bx2-30 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw12 ∷ []) (sym (wl0111 c4)) ▸
       at 1 2 (Toff312 ∷ Sw12 ∷ []) (wl0143 c4) ▸
       at 2 2 (Bx1-30 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·30⟩ c4) ▸
       at 3 2 (Toff312 ∷ Sw12 ∷ []) (wl0143 c4) ▸
       at 4 2 (CCZ123 ∷ Sw12 ∷ []) (sym (wl0111 c4)) ▸
       at 5 2 (Bx1-30 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·30⟩ c4) ▸
       at 0 6 (Bx3-120 ∷ []) (refl) ▸ done


-- nat 1 BOX(2;3410): 8 steps
lem-nat-1-BOX⟨2·3410⟩ : WsL → ⟪ (Sw12 ∷ Bx2-3410 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3420 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·3410⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx2-3410 ∷ []) (Bx1-3420 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff234 ∷ Bx3-210 ∷ Toff234 ∷ CCZ234 ∷ Bx3-210 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0034 c4)) ▸
       at 1 2 (Toff134 ∷ Sw12 ∷ []) (wl0140 c4) ▸
       at 2 2 (Bx3-120 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·210⟩ c4) ▸
       at 3 2 (Toff134 ∷ Sw12 ∷ []) (wl0140 c4) ▸
       at 4 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0034 c4)) ▸
       at 5 2 (Bx3-120 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·210⟩ c4) ▸
       at 0 6 (Bx1-3420 ∷ []) (refl) ▸ done


-- nat 0 BOX(3;021): 8 steps
lem-nat-0-BOX⟨3·021⟩ : WsL → ⟪ (Sw01 ∷ Bx3-021 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-120 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·021⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx3-021 ∷ []) (Bx3-120 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff302 ∷ Bx0-31 ∷ Toff302 ∷ CCZ023 ∷ Bx0-31 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw01 ∷ []) (sym (wl0103 c4)) ▸
       at 1 2 (Toff312 ∷ Sw01 ∷ []) (wl0116 c4) ▸
       at 2 2 (Bx1-30 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·31⟩ c4) ▸
       at 3 2 (Toff312 ∷ Sw01 ∷ []) (wl0116 c4) ▸
       at 4 2 (CCZ123 ∷ Sw01 ∷ []) (sym (wl0103 c4)) ▸
       at 5 2 (Bx1-30 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·31⟩ c4) ▸
       at 0 6 (Bx3-120 ∷ []) (refl) ▸ done


-- nat 0 BOX(0;3421): 8 steps
lem-nat-0-BOX⟨0·3421⟩ : WsL → ⟪ (Sw01 ∷ Bx0-3421 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3420 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·3421⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-3421 ∷ []) (Bx1-3420 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff034 ∷ Bx3-021 ∷ Toff034 ∷ CCZ034 ∷ Bx3-021 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4) ▸
       at 1 2 (Toff134 ∷ Sw01 ∷ []) (lem-nat-0-TOFF034 c4) ▸
       at 2 2 (Bx3-120 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·021⟩ c4) ▸
       at 3 2 (Toff134 ∷ Sw01 ∷ []) (lem-nat-0-TOFF034 c4) ▸
       at 4 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4) ▸
       at 5 2 (Bx3-120 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·021⟩ c4) ▸
       at 0 6 (Bx1-3420 ∷ []) (refl) ▸ done


-- nat 0 BOX(3;120): 8 steps
lem-nat-0-BOX⟨3·120⟩ : WsL → ⟪ (Sw01 ∷ Bx3-120 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-021 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·120⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx3-120 ∷ []) (Bx3-021 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff312 ∷ Bx1-30 ∷ Toff312 ∷ CCZ123 ∷ Bx1-30 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw01 ∷ []) (sym (wl0003 c4)) ▸
       at 1 2 (Toff302 ∷ Sw01 ∷ []) (wl0110 c4) ▸
       at 2 2 (Bx0-31 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·30⟩ c4) ▸
       at 3 2 (Toff302 ∷ Sw01 ∷ []) (wl0110 c4) ▸
       at 4 2 (CCZ023 ∷ Sw01 ∷ []) (sym (wl0003 c4)) ▸
       at 5 2 (Bx0-31 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·30⟩ c4) ▸
       at 0 6 (Bx3-021 ∷ []) (refl) ▸ done


-- nat 0 BOX(1;3420): 8 steps
lem-nat-0-BOX⟨1·3420⟩ : WsL → ⟪ (Sw01 ∷ Bx1-3420 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3421 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·3420⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-3420 ∷ []) (Bx0-3421 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff134 ∷ Bx3-120 ∷ Toff134 ∷ CCZ134 ∷ Bx3-120 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 1 2 (Toff034 ∷ Sw01 ∷ []) (lem-nat-0-TOFF134 c4) ▸
       at 2 2 (Bx3-021 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·120⟩ c4) ▸
       at 3 2 (Toff034 ∷ Sw01 ∷ []) (lem-nat-0-TOFF134 c4) ▸
       at 4 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 5 2 (Bx3-021 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·120⟩ c4) ▸
       at 0 6 (Bx0-3421 ∷ []) (refl) ▸ done


-- nat 1 BOX(3;021): 8 steps
lem-nat-1-BOX⟨3·021⟩ : WsL → ⟪ (Sw12 ∷ Bx3-021 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-012 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·021⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-021 ∷ []) (Bx3-012 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff302 ∷ Bx0-31 ∷ Toff302 ∷ CCZ023 ∷ Bx0-31 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 1 2 (Toff301 ∷ Sw12 ∷ []) (lem-nat-1-TOFF302 c4) ▸
       at 2 2 (Bx0-32 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·31⟩ c4) ▸
       at 3 2 (Toff301 ∷ Sw12 ∷ []) (lem-nat-1-TOFF302 c4) ▸
       at 4 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 5 2 (Bx0-32 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·31⟩ c4) ▸
       at 0 6 (Bx3-012 ∷ []) (refl) ▸ done


-- nat 1 BOX(0;3421): 8 steps
lem-nat-1-BOX⟨0·3421⟩ : WsL → ⟪ (Sw12 ∷ Bx0-3421 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3412 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·3421⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-3421 ∷ []) (Bx0-3412 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff034 ∷ Bx3-021 ∷ Toff034 ∷ CCZ034 ∷ Bx3-021 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 1 2 (Toff034 ∷ Sw12 ∷ []) (lem-nat-1-TOFF034 c4) ▸
       at 2 2 (Bx3-012 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·021⟩ c4) ▸
       at 3 2 (Toff034 ∷ Sw12 ∷ []) (lem-nat-1-TOFF034 c4) ▸
       at 4 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 5 2 (Bx3-012 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·021⟩ c4) ▸
       at 0 6 (Bx0-3412 ∷ []) (refl) ▸ done


-- nat 0 SBOX(1;0;2;3): 3 steps
lem-nat-0-SBOX⟨1·0·2·3⟩ : WsL → ⟪ (Sw01 ∷ Sb1-0-2-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-2-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨1·0·2·3⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb1-0-2-3 ∷ []) (Sb0-1-2-3 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS02 ∷ []) (refl) ▸
       at 0 2 (CS12 ∷ Sw01 ∷ []) (sym (wl0138 c4)) ▸
       at 0 1 (Sb0-1-2-3 ∷ []) (refl) ▸ done


-- nat 0 SBOXd(1;0;2;3): 3 steps
lem-nat-0-SBOXd⟨1·0·2·3⟩ : WsL → ⟪ (Sw01 ∷ Sb⁻1-0-2-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-2-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨1·0·2·3⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻1-0-2-3 ∷ []) (Sb⁻0-1-2-3 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS02⁻ ∷ []) (refl) ▸
       at 0 2 (CS12⁻ ∷ Sw01 ∷ []) (sym (wl0139 c4)) ▸
       at 0 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸ done


-- nat 0 SBOX(1;0;43;2): 7 steps
lem-nat-0-SBOX⟨1·0·43·2⟩ : WsL → ⟪ (Sw01 ∷ Sb1-0-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-43-2 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨1·0·43·2⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb1-0-43-2 ∷ []) (Sb0-1-43-2 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (refl) ▸
       at 0 2 (Bx0-1432 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0432⟩ c4) ▸
       at 1 2 (Toff234 ∷ Sw01 ∷ []) (c₂ (Swap) (Toff)) ▸
       at 2 2 (Sb0-1-2-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·2·3⟩ c4) ▸
       at 3 2 (Toff234 ∷ Sw01 ∷ []) (c₂ (Swap) (Toff)) ▸
       at 4 2 (Sb⁻0-1-2-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·2·3⟩ c4) ▸
       at 0 5 (Sb0-1-43-2 ∷ []) (refl) ▸ done


-- resp TOFF403 at 2: 236 steps
lem-resp-TOFF403-at-2 : WsL → ⟪ (Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ Toff413 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-TOFF403-at-2 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (run b29)))))))))))))))))))))))))))))
  where
  b0 : Chain (Toff403 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ K3 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 0 1 (Sw23 ∷ Toff402 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (Sw12 ∷ Toff401 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ Toff301 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (K3 ∷ Sw23 ∷ []) (sym (wl0057 c4)) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸ done

  b1 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ K3 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ Sw23 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ [])
  b1 = at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 6 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K3 ∷ Sw23 ∷ []) (sym (wl0057 c4)) ▸ done

  b2 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ Sw23 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ []) (Sw23 ∷ Sw12 ∷ K4 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ Sw34 ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ [])
  b2 = at 10 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 11 2 [] (wl0006 c4) ▸
       at 2 2 (K4 ∷ Sw34 ∷ []) (sym (wl0067 c4)) ▸
       at 5 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 3 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 5 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b3 : Chain (Sw23 ∷ Sw12 ∷ K4 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ Sw34 ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ []) (Sw23 ∷ K4 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K4 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ [])
  b3 = at 6 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 9 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 7 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K4 ∷ Sw34 ∷ []) (sym (wl0067 c4)) ▸
       at 9 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 10 2 [] (wl0007 c4) ▸
       at 1 2 (K4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K ↑)) ▸
       at 2 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0008 c4)) ▸ done

  b4 : Chain (Sw23 ∷ K4 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K4 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ []) (Sw23 ∷ K4 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ CS03 ∷ Sw12 ∷ Sw34 ∷ K4 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ [])
  b4 = at 5 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 3 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS24⁻ ∷ Sw12 ∷ []) (sym (wl0009 c4)) ▸
       at 7 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 5 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 7 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 c4)) ▸ done

  b5 : Chain (Sw23 ∷ K4 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ CS03 ∷ Sw12 ∷ Sw34 ∷ K4 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ []) (K4 ∷ CS34 ∷ Sw23 ∷ CX02 ∷ Sw23 ∷ Sw23 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K4 ∷ ι ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ [])
  b5 = at 8 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 6 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K ↑)) ▸
       at 8 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 9 2 [] (wl0001 c4) ▸
       at 0 2 (K4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K)) ▸
       at 1 2 (CS34 ∷ Sw23 ∷ []) (sym (wl0011 c4)) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸ done

  b6 : Chain (K4 ∷ CS34 ∷ Sw23 ∷ CX02 ∷ Sw23 ∷ Sw23 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K4 ∷ ι ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ []) (K4 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ K4 ∷ ι ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ [])
  b6 = at 2 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS34⁻ ∷ Sw23 ∷ []) (sym (wl0012 c4)) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 4 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (wl0013 c4) ▸
       at 7 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 8 2 (CS01 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸ done

  b7 : Chain (K4 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ K4 ∷ ι ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ []) (K4 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ Sw12 ∷ K4 ∷ ι ∷ Sw12 ∷ [])
  b7 = at 9 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 10 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (sym (wl0013 c4)) ▸
       at 5 7 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K)) ▸
       at 7 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 8 2 [] (wl0006 c4) ▸
       at 7 2 (Sw12 ∷ ι ∷ []) (c₁ (iI) (Swap)) ▸
       at 6 2 (Sw12 ∷ K4 ∷ []) (sym (c₃ (Swap ↑) (K ↑))) ▸ done

  b8 : Chain (K4 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ Sw12 ∷ K4 ∷ ι ∷ Sw12 ∷ []) (K4 ∷ CS34 ∷ Sw12 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K4 ∷ ι ∷ Sw12 ∷ [])
  b8 = at 5 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 6 2 (Sw12 ∷ CS03 ∷ []) (wl0010 c4) ▸
       at 5 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 6 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw12 ∷ CX03 ∷ []) (wl0014 c4) ▸
       at 3 2 (Sw12 ∷ CS34⁻ ∷ []) (sym (c₃ (Swap ↑) (CS • CS • CS))) ▸
       at 2 2 (Sw12 ∷ CX03 ∷ []) (wl0014 c4) ▸ done

  b9 : Chain (K4 ∷ CS34 ∷ Sw12 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K4 ∷ ι ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ K4 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ Sw23 ∷ CX03 ∷ CS04 ∷ K4 ∷ ι ∷ Sw12 ∷ [])
  b9 = at 1 2 (Sw12 ∷ CS34 ∷ []) (sym (c₃ (Swap ↑) (CS))) ▸
       at 0 2 (Sw12 ∷ K4 ∷ []) (sym (c₃ (Swap ↑) (K ↑))) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 2 2 (K4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K)) ▸
       at 3 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0015 c4)) ▸
       at 5 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0006 c4) ▸
       at 5 2 (CS24⁻ ∷ Sw23 ∷ []) (sym (wl0016 c4)) ▸ done

  b10 : Chain (Sw12 ∷ Sw23 ∷ K4 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ Sw23 ∷ CX03 ∷ CS04 ∷ K4 ∷ ι ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ K4 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw23 ∷ K4 ∷ ι ∷ Sw12 ∷ [])
  b10 = at 7 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0006 c4) ▸
       at 8 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (wl0013 c4) ▸
       at 9 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 10 2 (CS01 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸
       at 11 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 12 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (sym (wl0013 c4)) ▸ done

  b11 : Chain (Sw12 ∷ Sw23 ∷ K4 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw23 ∷ K4 ∷ ι ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ K4 ∷ CS14 ∷ CX01 ∷ Sw12 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K4 ∷ ι ∷ Sw23 ∷ Sw12 ∷ [])
  b11 = at 7 7 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K)) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 3 2 (K4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K ↑)) ▸
       at 4 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0017 c4)) ▸
       at 6 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0001 c4) ▸ done

  b12 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ K4 ∷ CS14 ∷ CX01 ∷ Sw12 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K4 ∷ ι ∷ Sw23 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ K4 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw12 ∷ K4 ∷ ι ∷ Sw23 ∷ Sw12 ∷ [])
  b12 = at 6 2 (CS14⁻ ∷ Sw12 ∷ []) (sym (wl0018 c4)) ▸
       at 8 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0001 c4) ▸
       at 9 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 9 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 c4)) ▸
       at 10 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 8 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸ done

  b13 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ K4 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw12 ∷ K4 ∷ ι ∷ Sw23 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K3 ∷ CS13 ∷ CX01 ∷ Sw34 ∷ Sw34 ∷ CS13⁻ ∷ Sw34 ∷ CX01 ∷ CS04 ∷ K4 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ [])
  b13 = at 9 2 (K4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K ↑)) ▸
       at 10 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 3 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 4 2 (K3 ∷ Sw34 ∷ []) (sym (wl0068 c4)) ▸
       at 6 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0007 c4) ▸
       at 6 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 8 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b14 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K3 ∷ CS13 ∷ CX01 ∷ Sw34 ∷ Sw34 ∷ CS13⁻ ∷ Sw34 ∷ CX01 ∷ CS04 ∷ K4 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K2 ∷ Sw23 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ [])
  b14 = at 7 2 [] (wl0007 c4) ▸
       at 8 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 10 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (wl0007 c4) ▸
       at 10 2 (K3 ∷ Sw34 ∷ []) (sym (wl0068 c4)) ▸
       at 11 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 5 2 (K2 ∷ Sw23 ∷ []) (sym (wl0058 c4)) ▸ done

  b15 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K2 ∷ Sw23 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ [])
  b15 = at 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0006 c4) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 9 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0006 c4) ▸
       at 9 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (wl0006 c4) ▸ done

  b16 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (Sw12 ∷ Toff403 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ [])
  b16 = at 11 2 (K2 ∷ Sw23 ∷ []) (sym (wl0058 c4)) ▸
       at 12 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 5 8 (Toff201 ∷ []) (by-assoc Eq.refl) ▸
       at 4 3 (Toff301 ∷ []) (by-assoc Eq.refl) ▸
       at 3 3 (Toff401 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (Toff402 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff403 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 c4)) ▸ done

  b17 : Chain (Sw12 ∷ Toff403 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K3 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ [])
  b17 = at 1 1 (Sw23 ∷ Toff402 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw12 ∷ Toff401 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw34 ∷ Toff301 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (K3 ∷ Sw23 ∷ []) (sym (wl0057 c4)) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 5 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b18 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K3 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ [])
  b18 = at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 7 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 9 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (K3 ∷ Sw23 ∷ []) (sym (wl0057 c4)) ▸
       at 11 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸ done

  b19 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ K4 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ [])
  b19 = at 12 2 [] (wl0006 c4) ▸
       at 3 2 (K4 ∷ Sw34 ∷ []) (sym (wl0067 c4)) ▸
       at 6 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 4 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 6 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸ done

  b20 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ K4 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ K4 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K4 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ [])
  b20 = at 10 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 8 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K4 ∷ Sw34 ∷ []) (sym (wl0067 c4)) ▸
       at 10 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 11 2 [] (wl0007 c4) ▸
       at 2 2 (K4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K ↑)) ▸
       at 3 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0008 c4)) ▸
       at 6 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸ done

  b21 : Chain (Sw12 ∷ Sw23 ∷ K4 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K4 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ K4 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ K4 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ [])
  b21 = at 4 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS24⁻ ∷ Sw12 ∷ []) (sym (wl0009 c4)) ▸
       at 8 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 6 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 8 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 c4)) ▸
       at 9 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸ done

  b22 : Chain (Sw12 ∷ Sw23 ∷ K4 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ K4 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ K4 ∷ CS34 ∷ CX03 ∷ Sw23 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K4 ∷ ι ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ [])
  b22 = at 7 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K ↑)) ▸
       at 9 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 10 2 [] (wl0001 c4) ▸
       at 1 2 (K4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K)) ▸
       at 2 2 (CS34 ∷ Sw23 ∷ []) (sym (wl0011 c4)) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 3 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸ done

  b23 : Chain (Sw12 ∷ K4 ∷ CS34 ∷ CX03 ∷ Sw23 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K4 ∷ ι ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ K4 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Sw34 ∷ K4 ∷ ι ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ [])
  b23 = at 4 2 (CS34⁻ ∷ Sw23 ∷ []) (sym (wl0012 c4)) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 5 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (wl0013 c4) ▸
       at 8 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 9 2 (CS01 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸
       at 10 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸ done

  b24 : Chain (Sw12 ∷ K4 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Sw34 ∷ K4 ∷ ι ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ K4 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw01 ∷ K4 ∷ ι ∷ Sw01 ∷ Sw12 ∷ [])
  b24 = at 11 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (sym (wl0013 c4)) ▸
       at 6 7 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K)) ▸
       at 8 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 9 2 [] (wl0006 c4) ▸
       at 8 2 (Sw01 ∷ ι ∷ []) (sym (wl0030 c4)) ▸
       at 7 2 (Sw01 ∷ K4 ∷ []) (sym (c₂ (Swap) (K ↑ ↑))) ▸
       at 6 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b25 : Chain (Sw12 ∷ K4 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw01 ∷ K4 ∷ ι ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ K4 ∷ Sw01 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K4 ∷ ι ∷ Sw01 ∷ Sw12 ∷ [])
  b25 = at 8 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 7 2 (Sw01 ∷ CS13 ∷ []) (wl0019 c4) ▸
       at 6 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 7 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw01 ∷ CX13 ∷ []) (wl0020 c4) ▸
       at 4 2 (Sw01 ∷ CS34⁻ ∷ []) (sym (c₂ (Swap) ((CS • CS • CS) ↑))) ▸
       at 3 2 (Sw01 ∷ CX13 ∷ []) (wl0020 c4) ▸
       at 2 2 (Sw01 ∷ CS34 ∷ []) (sym (c₂ (Swap) (CS ↑))) ▸ done

  b26 : Chain (Sw12 ∷ K4 ∷ Sw01 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K4 ∷ ι ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw01 ∷ Sw23 ∷ K4 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ Sw23 ∷ Sw23 ∷ CX12 ∷ Sw23 ∷ CS14 ∷ K4 ∷ ι ∷ Sw01 ∷ Sw12 ∷ [])
  b26 = at 1 2 (Sw01 ∷ K4 ∷ []) (sym (c₂ (Swap) (K ↑ ↑))) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 3 2 (K4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K)) ▸
       at 4 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0015 c4)) ▸
       at 6 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0006 c4) ▸
       at 6 2 (CS24⁻ ∷ Sw23 ∷ []) (sym (wl0016 c4)) ▸
       at 8 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b27 : Chain (Sw12 ∷ Sw01 ∷ Sw23 ∷ K4 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ Sw23 ∷ Sw23 ∷ CX12 ∷ Sw23 ∷ CS14 ∷ K4 ∷ ι ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw34 ∷ K3 ∷ CS23 ∷ Sw34 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K4 ∷ ι ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ [])
  b27 = at 7 2 [] (wl0006 c4) ▸
       at 8 2 (CS14 ∷ Sw23 ∷ []) (sym (wl0021 c4)) ▸
       at 9 2 (K4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K)) ▸
       at 10 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 3 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 4 2 (K3 ∷ Sw34 ∷ []) (sym (wl0068 c4)) ▸
       at 6 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0007 c4) ▸ done

  b28 : Chain (Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw34 ∷ K3 ∷ CS23 ∷ Sw34 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K4 ∷ ι ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw34 ∷ K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ [])
  b28 = at 6 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 8 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0007 c4) ▸
       at 8 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 10 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (wl0007 c4) ▸
       at 10 2 (K3 ∷ Sw34 ∷ []) (sym (wl0068 c4)) ▸
       at 11 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸ done

  b29 : Chain (Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw34 ∷ K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw01 ∷ Toff413 ∷ Sw01 ∷ Sw12 ∷ [])
  b29 = at 4 8 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) (wl0082 c4) ▸
       at 4 8 (Toff312 ∷ []) (by-assoc Eq.refl) ▸
       at 3 3 (Toff412 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (Toff413 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 1 CK20: 2 steps
lem-nat-1-CK20 : WsL → ⟪ (Sw12 ∷ CK20 ∷ []) ⟫ʷ ≈ ⟪ (CK10 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-CK20 c4 = run b0
  where
  b0 : Chain (Sw12 ∷ CK20 ∷ []) (CK10 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0001 c4) ▸ done


-- nat 1 CK10: 2 steps
lem-nat-1-CK10 : WsL → ⟪ (Sw12 ∷ CK10 ∷ []) ⟫ʷ ≈ ⟪ (CK20 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-CK10 c4 = run b0
  where
  b0 : Chain (Sw12 ∷ CK10 ∷ []) (CK20 ∷ Sw12 ∷ [])
  b0 = at 2 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 0 3 (CK20 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 2 CK30: 2 steps
lem-nat-2-CK30 : WsL → ⟪ (Sw23 ∷ CK30 ∷ []) ⟫ʷ ≈ ⟪ (CK20 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-CK30 c4 = run b0
  where
  b0 : Chain (Sw23 ∷ CK30 ∷ []) (CK20 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0006 c4) ▸ done


-- nat 2 CK20: 2 steps
lem-nat-2-CK20 : WsL → ⟪ (Sw23 ∷ CK20 ∷ []) ⟫ʷ ≈ ⟪ (CK30 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-CK20 c4 = run b0
  where
  b0 : Chain (Sw23 ∷ CK20 ∷ []) (CK30 ∷ Sw23 ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 0 3 (CK30 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 3 CK40: 2 steps
lem-nat-3-CK40 : WsL → ⟪ (Sw34 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK30 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-CK40 c4 = run b0
  where
  b0 : Chain (Sw34 ∷ CK40 ∷ []) (CK30 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0007 c4) ▸ done


-- nat 3 CK30: 2 steps
lem-nat-3-CK30 : WsL → ⟪ (Sw34 ∷ CK30 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-CK30 c4 = run b0
  where
  b0 : Chain (Sw34 ∷ CK30 ∷ []) (CK40 ∷ Sw34 ∷ [])
  b0 = at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 0 3 (CK40 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 2 CK40: 7 steps
lem-nat-2-CK40 : WsL → ⟪ (Sw23 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-CK40 c4 = run b0
  where
  b0 : Chain (Sw23 ∷ CK40 ∷ []) (CK40 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (wl0013 c4) ▸
       at 2 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 3 2 (CK10 ∷ Sw34 ∷ []) (sym (c₂ (CK₁₀) (Swap ↑))) ▸
       at 4 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 5 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (sym (wl0013 c4)) ▸
       at 0 7 (CK40 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 1 CK40: 5 steps
lem-nat-1-CK40 : WsL → ⟪ (Sw12 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-CK40 c4 = run b0
  where
  b0 : Chain (Sw12 ∷ CK40 ∷ []) (CK40 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 1 2 (CK30 ∷ Sw12 ∷ []) (sym (wl0159 c4)) ▸
       at 2 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 0 3 (CK40 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 CK41: 5 steps
lem-nat-0-CK41 : WsL → ⟪ (Sw01 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-CK41 c4 = run b0
  where
  b0 : Chain (Sw01 ∷ CK41 ∷ []) (CK40 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Sw34 ∷ CK31 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 1 2 (CK30 ∷ Sw01 ∷ []) (sym (wl0117 c4)) ▸
       at 2 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 0 3 (CK40 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 CK40: 5 steps
lem-nat-0-CK40 : WsL → ⟪ (Sw01 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-CK40 c4 = run b0
  where
  b0 : Chain (Sw01 ∷ CK40 ∷ []) (CK41 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 1 2 (CK31 ∷ Sw01 ∷ []) (sym (wl0161 c4)) ▸
       at 2 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 0 3 (CK41 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 2 BOX(0;31): 3 steps
lem-nat-2-BOX⟨0·31⟩ : WsL → ⟪ (Sw23 ∷ Bx0-31 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-21 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·31⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-31 ∷ []) (Bx0-21 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ13 ∷ []) (refl) ▸
       at 0 2 (CZ12 ∷ Sw23 ∷ []) (lem-nat-2-CZ13 c4) ▸
       at 0 1 (Bx0-21 ∷ []) (refl) ▸ done


-- nat 2 BOX(3;041): 8 steps
lem-nat-2-BOX⟨3·041⟩ : WsL → ⟪ (Sw23 ∷ Bx3-041 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-041 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·041⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx3-041 ∷ []) (Bx2-041 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff304 ∷ Bx0-31 ∷ Toff304 ∷ CCZ034 ∷ Bx0-31 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 1 2 (Toff204 ∷ Sw23 ∷ []) (lem-nat-2-TOFF304 c4) ▸
       at 2 2 (Bx0-21 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·31⟩ c4) ▸
       at 3 2 (Toff204 ∷ Sw23 ∷ []) (lem-nat-2-TOFF304 c4) ▸
       at 4 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 5 2 (Bx0-21 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·31⟩ c4) ▸
       at 0 6 (Bx2-041 ∷ []) (refl) ▸ done


-- nat 2 BOX(0;3241): 8 steps
lem-nat-2-BOX⟨0·3241⟩ : WsL → ⟪ (Sw23 ∷ Bx0-3241 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2341 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·3241⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-3241 ∷ []) (Bx0-2341 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff023 ∷ Bx3-041 ∷ Toff023 ∷ CCZ023 ∷ Bx3-041 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw23 ∷ []) (sym (wl0065 c4)) ▸
       at 1 2 (Toff023 ∷ Sw23 ∷ []) (wl0093 c4) ▸
       at 2 2 (Bx2-041 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·041⟩ c4) ▸
       at 3 2 (Toff023 ∷ Sw23 ∷ []) (wl0093 c4) ▸
       at 4 2 (CCZ023 ∷ Sw23 ∷ []) (sym (wl0065 c4)) ▸
       at 5 2 (Bx2-041 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·041⟩ c4) ▸
       at 0 6 (Bx0-2341 ∷ []) (refl) ▸ done


-- nat 2 SBOX(0;3;1;4): 3 steps
lem-nat-2-SBOX⟨0·3·1·4⟩ : WsL → ⟪ (Sw23 ∷ Sb0-3-1-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-1-4 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨0·3·1·4⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb0-3-1-4 ∷ []) (Sb0-2-1-4 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS13 ∷ []) (refl) ▸
       at 0 2 (CS12 ∷ Sw23 ∷ []) (lem-nat-2-CS13 c4) ▸
       at 0 1 (Sb0-2-1-4 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(0;3;1;4): 3 steps
lem-nat-2-SBOXd⟨0·3·1·4⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻0-3-1-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-2-1-4 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨0·3·1·4⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻0-3-1-4 ∷ []) (Sb⁻0-2-1-4 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS13⁻ ∷ []) (refl) ▸
       at 0 2 (CS12⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd13 c4) ▸
       at 0 1 (Sb⁻0-2-1-4 ∷ []) (refl) ▸ done


-- nat 2 SBOX(0;3;24;1): 7 steps
lem-nat-2-SBOX⟨0·3·24·1⟩ : WsL → ⟪ (Sw23 ∷ Sb0-3-24-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-34-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨0·3·24·1⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb0-3-24-1 ∷ []) (Sb0-2-34-1 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx0-3241 ∷ Toff124 ∷ Sb0-3-1-4 ∷ Toff124 ∷ Sb⁻0-3-1-4 ∷ []) (refl) ▸
       at 0 2 (Bx0-2341 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3241⟩ c4) ▸
       at 1 2 (Toff134 ∷ Sw23 ∷ []) (lem-nat-2-TOFF124 c4) ▸
       at 2 2 (Sb0-2-1-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·3·1·4⟩ c4) ▸
       at 3 2 (Toff134 ∷ Sw23 ∷ []) (lem-nat-2-TOFF124 c4) ▸
       at 4 2 (Sb⁻0-2-1-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·3·1·4⟩ c4) ▸
       at 0 5 (Sb0-2-34-1 ∷ []) (refl) ▸ done


-- nat 0 SBOX(1;3;0;4): 3 steps
lem-nat-0-SBOX⟨1·3·0·4⟩ : WsL → ⟪ (Sw01 ∷ Sb1-3-0-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-3-1-4 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨1·3·0·4⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb1-3-0-4 ∷ []) (Sb0-3-1-4 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS03 ∷ []) (refl) ▸
       at 0 2 (CS13 ∷ Sw01 ∷ []) (sym (wl0061 c4)) ▸
       at 0 1 (Sb0-3-1-4 ∷ []) (refl) ▸ done


-- nat 0 SBOXd(1;3;0;4): 3 steps
lem-nat-0-SBOXd⟨1·3·0·4⟩ : WsL → ⟪ (Sw01 ∷ Sb⁻1-3-0-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-3-1-4 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨1·3·0·4⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻1-3-0-4 ∷ []) (Sb⁻0-3-1-4 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS03⁻ ∷ []) (refl) ▸
       at 0 2 (CS13⁻ ∷ Sw01 ∷ []) (sym (wl0121 c4)) ▸
       at 0 1 (Sb⁻0-3-1-4 ∷ []) (refl) ▸ done


-- nat 0 SBOX(1;3;24;0): 7 steps
lem-nat-0-SBOX⟨1·3·24·0⟩ : WsL → ⟪ (Sw01 ∷ Sb1-3-24-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-3-24-1 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨1·3·24·0⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb1-3-24-0 ∷ []) (Sb0-3-24-1 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx1-3240 ∷ Toff024 ∷ Sb1-3-0-4 ∷ Toff024 ∷ Sb⁻1-3-0-4 ∷ []) (refl) ▸
       at 0 2 (Bx0-3241 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·3240⟩ c4) ▸
       at 1 2 (Toff124 ∷ Sw01 ∷ []) (lem-nat-0-TOFF024 c4) ▸
       at 2 2 (Sb0-3-1-4 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·3·0·4⟩ c4) ▸
       at 3 2 (Toff124 ∷ Sw01 ∷ []) (lem-nat-0-TOFF024 c4) ▸
       at 4 2 (Sb⁻0-3-1-4 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·3·0·4⟩ c4) ▸
       at 0 5 (Sb0-3-24-1 ∷ []) (refl) ▸ done


-- nat 1 SBOX(0;3;1;4): 3 steps
lem-nat-1-SBOX⟨0·3·1·4⟩ : WsL → ⟪ (Sw12 ∷ Sb0-3-1-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-3-2-4 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨0·3·1·4⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb0-3-1-4 ∷ []) (Sb0-3-2-4 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS13 ∷ []) (refl) ▸
       at 0 2 (CS23 ∷ Sw12 ∷ []) (sym (wl0025 c4)) ▸
       at 0 1 (Sb0-3-2-4 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(0;3;1;4): 3 steps
lem-nat-1-SBOXd⟨0·3·1·4⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻0-3-1-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-3-2-4 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨0·3·1·4⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻0-3-1-4 ∷ []) (Sb⁻0-3-2-4 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS13⁻ ∷ []) (refl) ▸
       at 0 2 (CS23⁻ ∷ Sw12 ∷ []) (sym (wl0046 c4)) ▸
       at 0 1 (Sb⁻0-3-2-4 ∷ []) (refl) ▸ done


-- nat 1 SBOX(0;3;24;1): 7 steps
lem-nat-1-SBOX⟨0·3·24·1⟩ : WsL → ⟪ (Sw12 ∷ Sb0-3-24-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-3-14-2 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨0·3·24·1⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb0-3-24-1 ∷ []) (Sb0-3-14-2 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx0-3241 ∷ Toff124 ∷ Sb0-3-1-4 ∷ Toff124 ∷ Sb⁻0-3-1-4 ∷ []) (refl) ▸
       at 0 2 (Bx0-3142 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·3241⟩ c4) ▸
       at 1 2 (Toff214 ∷ Sw12 ∷ []) (wl0095 c4) ▸
       at 2 2 (Sb0-3-2-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·3·1·4⟩ c4) ▸
       at 3 2 (Toff214 ∷ Sw12 ∷ []) (wl0095 c4) ▸
       at 4 2 (Sb⁻0-3-2-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨0·3·1·4⟩ c4) ▸
       at 0 5 (Sb0-3-14-2 ∷ []) (refl) ▸ done


-- nat 0 SBOX(0;3;2;4): 2 steps
lem-nat-0-SBOX⟨0·3·2·4⟩ : WsL → ⟪ (Sw01 ∷ Sb0-3-2-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-3-2-4 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨0·3·2·4⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb0-3-2-4 ∷ []) (Sb1-3-2-4 ∷ Sw01 ∷ [])
  b0 = at 0 2 (Sb0-3-2-4 ∷ Sw01 ∷ []) (c₂ (Swap) (CS)) ▸
       at 0 1 (Sb1-3-2-4 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 SBOXd(0;3;2;4): 2 steps
lem-nat-0-SBOXd⟨0·3·2·4⟩ : WsL → ⟪ (Sw01 ∷ Sb⁻0-3-2-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-3-2-4 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨0·3·2·4⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻0-3-2-4 ∷ []) (Sb⁻1-3-2-4 ∷ Sw01 ∷ [])
  b0 = at 0 2 (Sb⁻0-3-2-4 ∷ Sw01 ∷ []) (c₂ (Swap) (CS • CS • CS)) ▸
       at 0 1 (Sb⁻1-3-2-4 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 SBOX(0;3;14;2): 7 steps
lem-nat-0-SBOX⟨0·3·14·2⟩ : WsL → ⟪ (Sw01 ∷ Sb0-3-14-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-3-04-2 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨0·3·14·2⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb0-3-14-2 ∷ []) (Sb1-3-04-2 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx0-3142 ∷ Toff214 ∷ Sb0-3-2-4 ∷ Toff214 ∷ Sb⁻0-3-2-4 ∷ []) (refl) ▸
       at 0 2 (Bx1-3042 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·3142⟩ c4) ▸
       at 1 2 (Toff204 ∷ Sw01 ∷ []) (lem-nat-0-TOFF214 c4) ▸
       at 2 2 (Sb1-3-2-4 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·3·2·4⟩ c4) ▸
       at 3 2 (Toff204 ∷ Sw01 ∷ []) (lem-nat-0-TOFF214 c4) ▸
       at 4 2 (Sb⁻1-3-2-4 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨0·3·2·4⟩ c4) ▸
       at 0 5 (Sb1-3-04-2 ∷ []) (refl) ▸ done


-- nat 3 BOX(2;143): 8 steps
lem-nat-3-BOX⟨2·143⟩ : WsL → ⟪ (Sw34 ∷ Bx2-143 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-134 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨2·143⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx2-143 ∷ []) (Bx2-134 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff214 ∷ Bx1-23 ∷ Toff214 ∷ CCZ124 ∷ Bx1-23 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw34 ∷ []) (lem-nat-3-CCZ124 c4) ▸
       at 1 2 (Toff213 ∷ Sw34 ∷ []) (lem-nat-3-TOFF214 c4) ▸
       at 2 2 (Bx1-24 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·23⟩ c4) ▸
       at 3 2 (Toff213 ∷ Sw34 ∷ []) (lem-nat-3-TOFF214 c4) ▸
       at 4 2 (CCZ123 ∷ Sw34 ∷ []) (lem-nat-3-CCZ124 c4) ▸
       at 5 2 (Bx1-24 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·23⟩ c4) ▸
       at 0 6 (Bx2-134 ∷ []) (refl) ▸ done


-- nat 3 BOX(1;2043): 8 steps
lem-nat-3-BOX⟨1·2043⟩ : WsL → ⟪ (Sw34 ∷ Bx1-2043 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2034 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨1·2043⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx1-2043 ∷ []) (Bx1-2034 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff102 ∷ Bx2-143 ∷ Toff102 ∷ CCZ012 ∷ Bx2-143 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 1 2 (Toff102 ∷ Sw34 ∷ []) (sym (c₃ (K ↑ • CCZ • K ↑ • iI) (Swap))) ▸
       at 2 2 (Bx2-134 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·143⟩ c4) ▸
       at 3 2 (Toff102 ∷ Sw34 ∷ []) (sym (c₃ (K ↑ • CCZ • K ↑ • iI) (Swap))) ▸
       at 4 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 5 2 (Bx2-134 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·143⟩ c4) ▸
       at 0 6 (Bx1-2034 ∷ []) (refl) ▸ done


-- nat 3 BOX(2;134): 8 steps
lem-nat-3-BOX⟨2·134⟩ : WsL → ⟪ (Sw34 ∷ Bx2-134 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-143 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨2·134⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx2-134 ∷ []) (Bx2-143 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff213 ∷ Bx1-24 ∷ Toff213 ∷ CCZ123 ∷ Bx1-24 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw34 ∷ []) (lem-nat-3-CCZ123 c4) ▸
       at 1 2 (Toff214 ∷ Sw34 ∷ []) (lem-nat-3-TOFF213 c4) ▸
       at 2 2 (Bx1-23 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·24⟩ c4) ▸
       at 3 2 (Toff214 ∷ Sw34 ∷ []) (lem-nat-3-TOFF213 c4) ▸
       at 4 2 (CCZ124 ∷ Sw34 ∷ []) (lem-nat-3-CCZ123 c4) ▸
       at 5 2 (Bx1-23 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·24⟩ c4) ▸
       at 0 6 (Bx2-143 ∷ []) (refl) ▸ done


-- nat 3 BOX(1;2034): 8 steps
lem-nat-3-BOX⟨1·2034⟩ : WsL → ⟪ (Sw34 ∷ Bx1-2034 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2043 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨1·2034⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx1-2034 ∷ []) (Bx1-2043 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff102 ∷ Bx2-134 ∷ Toff102 ∷ CCZ012 ∷ Bx2-134 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 1 2 (Toff102 ∷ Sw34 ∷ []) (sym (c₃ (K ↑ • CCZ • K ↑ • iI) (Swap))) ▸
       at 2 2 (Bx2-143 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·134⟩ c4) ▸
       at 3 2 (Toff102 ∷ Sw34 ∷ []) (sym (c₃ (K ↑ • CCZ • K ↑ • iI) (Swap))) ▸
       at 4 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 5 2 (Bx2-143 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·134⟩ c4) ▸
       at 0 6 (Bx1-2043 ∷ []) (refl) ▸ done


-- nat 2 BOX(3;142): 8 steps
lem-nat-2-BOX⟨3·142⟩ : WsL → ⟪ (Sw23 ∷ Bx3-142 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-143 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·142⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx3-142 ∷ []) (Bx2-143 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff314 ∷ Bx1-32 ∷ Toff314 ∷ CCZ134 ∷ Bx1-32 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 1 2 (Toff214 ∷ Sw23 ∷ []) (lem-nat-2-TOFF314 c4) ▸
       at 2 2 (Bx1-23 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·32⟩ c4) ▸
       at 3 2 (Toff214 ∷ Sw23 ∷ []) (lem-nat-2-TOFF314 c4) ▸
       at 4 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 5 2 (Bx1-23 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·32⟩ c4) ▸
       at 0 6 (Bx2-143 ∷ []) (refl) ▸ done


-- nat 2 BOX(1;3042): 8 steps
lem-nat-2-BOX⟨1·3042⟩ : WsL → ⟪ (Sw23 ∷ Bx1-3042 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2043 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·3042⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx1-3042 ∷ []) (Bx1-2043 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff103 ∷ Bx3-142 ∷ Toff103 ∷ CCZ013 ∷ Bx3-142 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 1 2 (Toff102 ∷ Sw23 ∷ []) (lem-nat-2-TOFF103 c4) ▸
       at 2 2 (Bx2-143 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·142⟩ c4) ▸
       at 3 2 (Toff102 ∷ Sw23 ∷ []) (lem-nat-2-TOFF103 c4) ▸
       at 4 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 5 2 (Bx2-143 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·142⟩ c4) ▸
       at 0 6 (Bx1-2043 ∷ []) (refl) ▸ done


-- nat 2 BOX(2;143): 8 steps
lem-nat-2-BOX⟨2·143⟩ : WsL → ⟪ (Sw23 ∷ Bx2-143 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-142 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·143⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx2-143 ∷ []) (Bx3-142 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff214 ∷ Bx1-23 ∷ Toff214 ∷ CCZ124 ∷ Bx1-23 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 1 2 (Toff314 ∷ Sw23 ∷ []) (lem-nat-2-TOFF214 c4) ▸
       at 2 2 (Bx1-32 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·23⟩ c4) ▸
       at 3 2 (Toff314 ∷ Sw23 ∷ []) (lem-nat-2-TOFF214 c4) ▸
       at 4 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 5 2 (Bx1-32 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·23⟩ c4) ▸
       at 0 6 (Bx3-142 ∷ []) (refl) ▸ done


-- nat 2 BOX(1;2043): 8 steps
lem-nat-2-BOX⟨1·2043⟩ : WsL → ⟪ (Sw23 ∷ Bx1-2043 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3042 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·2043⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx1-2043 ∷ []) (Bx1-3042 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff102 ∷ Bx2-143 ∷ Toff102 ∷ CCZ012 ∷ Bx2-143 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 1 2 (Toff103 ∷ Sw23 ∷ []) (lem-nat-2-TOFF102 c4) ▸
       at 2 2 (Bx3-142 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·143⟩ c4) ▸
       at 3 2 (Toff103 ∷ Sw23 ∷ []) (lem-nat-2-TOFF102 c4) ▸
       at 4 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 5 2 (Bx3-142 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·143⟩ c4) ▸
       at 0 6 (Bx1-3042 ∷ []) (refl) ▸ done


-- nat 2 BOX(0;21): 3 steps
lem-nat-2-BOX⟨0·21⟩ : WsL → ⟪ (Sw23 ∷ Bx0-21 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-31 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·21⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-21 ∷ []) (Bx0-31 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ12 ∷ []) (refl) ▸
       at 0 2 (CZ13 ∷ Sw23 ∷ []) (lem-nat-2-CZ12 c4) ▸
       at 0 1 (Bx0-31 ∷ []) (refl) ▸ done


-- nat 2 BOX(2;031): 8 steps
lem-nat-2-BOX⟨2·031⟩ : WsL → ⟪ (Sw23 ∷ Bx2-031 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-021 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·031⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx2-031 ∷ []) (Bx3-021 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff203 ∷ Bx0-21 ∷ Toff203 ∷ CCZ023 ∷ Bx0-21 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw23 ∷ []) (sym (wl0065 c4)) ▸
       at 1 2 (Toff302 ∷ Sw23 ∷ []) (wl0090 c4) ▸
       at 2 2 (Bx0-31 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·21⟩ c4) ▸
       at 3 2 (Toff302 ∷ Sw23 ∷ []) (wl0090 c4) ▸
       at 4 2 (CCZ023 ∷ Sw23 ∷ []) (sym (wl0065 c4)) ▸
       at 5 2 (Bx0-31 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·21⟩ c4) ▸
       at 0 6 (Bx3-021 ∷ []) (refl) ▸ done


-- nat 2 BOX(0;2431): 8 steps
lem-nat-2-BOX⟨0·2431⟩ : WsL → ⟪ (Sw23 ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3421 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·2431⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-2431 ∷ []) (Bx0-3421 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff024 ∷ Bx2-031 ∷ Toff024 ∷ CCZ024 ∷ Bx2-031 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 1 2 (Toff034 ∷ Sw23 ∷ []) (lem-nat-2-TOFF024 c4) ▸
       at 2 2 (Bx3-021 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·031⟩ c4) ▸
       at 3 2 (Toff034 ∷ Sw23 ∷ []) (lem-nat-2-TOFF024 c4) ▸
       at 4 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 5 2 (Bx3-021 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·031⟩ c4) ▸
       at 0 6 (Bx0-3421 ∷ []) (refl) ▸ done


-- resp CCZ023 at 1: 2 steps
lem-resp-CCZ023-at-1 : WsL → ⟪ (CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CCZ023-at-1 c4 = run b0
  where
  b0 : Chain (CCZ023 ∷ []) (Sw01 ∷ CCZ123 ∷ Sw01 ∷ [])
  b0 = at 1 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 c4)) ▸
       at 0 2 (Sw01 ∷ CCZ123 ∷ []) (wl0003 c4) ▸ done


-- nat 0 BOX(1;230): 8 steps
lem-nat-0-BOX⟨1·230⟩ : WsL → ⟪ (Sw01 ∷ Bx1-230 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-231 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·230⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-230 ∷ []) (Bx0-231 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff123 ∷ Bx2-10 ∷ Toff123 ∷ CCZ123 ∷ Bx2-10 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw01 ∷ []) (sym (wl0003 c4)) ▸
       at 1 2 (Toff023 ∷ Sw01 ∷ []) (wl0053 c4) ▸
       at 2 2 (Bx2-01 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·10⟩ c4) ▸
       at 3 2 (Toff023 ∷ Sw01 ∷ []) (wl0053 c4) ▸
       at 4 2 (CCZ023 ∷ Sw01 ∷ []) (sym (wl0003 c4)) ▸
       at 5 2 (Bx2-01 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·10⟩ c4) ▸
       at 0 6 (Bx0-231 ∷ []) (refl) ▸ done


-- nat 0 BOX(2;1430): 8 steps
lem-nat-0-BOX⟨2·1430⟩ : WsL → ⟪ (Sw01 ∷ Bx2-1430 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0431 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·1430⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx2-1430 ∷ []) (Bx2-0431 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff214 ∷ Bx1-230 ∷ Toff214 ∷ CCZ124 ∷ Bx1-230 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 1 2 (Toff204 ∷ Sw01 ∷ []) (lem-nat-0-TOFF214 c4) ▸
       at 2 2 (Bx0-231 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·230⟩ c4) ▸
       at 3 2 (Toff204 ∷ Sw01 ∷ []) (lem-nat-0-TOFF214 c4) ▸
       at 4 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 5 2 (Bx0-231 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·230⟩ c4) ▸
       at 0 6 (Bx2-0431 ∷ []) (refl) ▸ done


-- nat 0 BOX(0;231): 8 steps
lem-nat-0-BOX⟨0·231⟩ : WsL → ⟪ (Sw01 ∷ Bx0-231 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-230 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·231⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-231 ∷ []) (Bx1-230 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff023 ∷ Bx2-01 ∷ Toff023 ∷ CCZ023 ∷ Bx2-01 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw01 ∷ []) (sym (wl0103 c4)) ▸
       at 1 2 (Toff123 ∷ Sw01 ∷ []) (wl0108 c4) ▸
       at 2 2 (Bx2-10 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·01⟩ c4) ▸
       at 3 2 (Toff123 ∷ Sw01 ∷ []) (wl0108 c4) ▸
       at 4 2 (CCZ123 ∷ Sw01 ∷ []) (sym (wl0103 c4)) ▸
       at 5 2 (Bx2-10 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·01⟩ c4) ▸
       at 0 6 (Bx1-230 ∷ []) (refl) ▸ done


-- nat 0 BOX(2;0431): 8 steps
lem-nat-0-BOX⟨2·0431⟩ : WsL → ⟪ (Sw01 ∷ Bx2-0431 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1430 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·0431⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx2-0431 ∷ []) (Bx2-1430 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff204 ∷ Bx0-231 ∷ Toff204 ∷ CCZ024 ∷ Bx0-231 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 1 2 (Toff214 ∷ Sw01 ∷ []) (lem-nat-0-TOFF204 c4) ▸
       at 2 2 (Bx1-230 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·231⟩ c4) ▸
       at 3 2 (Toff214 ∷ Sw01 ∷ []) (lem-nat-0-TOFF204 c4) ▸
       at 4 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 5 2 (Bx1-230 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·231⟩ c4) ▸
       at 0 6 (Bx2-1430 ∷ []) (refl) ▸ done


-- nat 1 BOX(1;20): 3 steps
lem-nat-1-BOX⟨1·20⟩ : WsL → ⟪ (Sw12 ∷ Bx1-20 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-10 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·20⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx1-20 ∷ []) (Bx2-10 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ02 ∷ []) (refl) ▸
       at 0 2 (CZ01 ∷ Sw12 ∷ []) (lem-nat-1-CZ02 c4) ▸
       at 0 1 (Bx2-10 ∷ []) (refl) ▸ done


-- nat 1 BOX(2;130): 8 steps
lem-nat-1-BOX⟨2·130⟩ : WsL → ⟪ (Sw12 ∷ Bx2-130 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-230 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·130⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx2-130 ∷ []) (Bx1-230 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff213 ∷ Bx1-20 ∷ Toff213 ∷ CCZ123 ∷ Bx1-20 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw12 ∷ []) (sym (wl0111 c4)) ▸
       at 1 2 (Toff123 ∷ Sw12 ∷ []) (wl0112 c4) ▸
       at 2 2 (Bx2-10 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·20⟩ c4) ▸
       at 3 2 (Toff123 ∷ Sw12 ∷ []) (wl0112 c4) ▸
       at 4 2 (CCZ123 ∷ Sw12 ∷ []) (sym (wl0111 c4)) ▸
       at 5 2 (Bx2-10 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·20⟩ c4) ▸
       at 0 6 (Bx1-230 ∷ []) (refl) ▸ done


-- nat 1 BOX(1;2430): 8 steps
lem-nat-1-BOX⟨1·2430⟩ : WsL → ⟪ (Sw12 ∷ Bx1-2430 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1430 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·2430⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx1-2430 ∷ []) (Bx2-1430 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff124 ∷ Bx2-130 ∷ Toff124 ∷ CCZ124 ∷ Bx2-130 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw12 ∷ []) (sym (wl0078 c4)) ▸
       at 1 2 (Toff214 ∷ Sw12 ∷ []) (wl0095 c4) ▸
       at 2 2 (Bx1-230 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·130⟩ c4) ▸
       at 3 2 (Toff214 ∷ Sw12 ∷ []) (wl0095 c4) ▸
       at 4 2 (CCZ124 ∷ Sw12 ∷ []) (sym (wl0078 c4)) ▸
       at 5 2 (Bx1-230 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·130⟩ c4) ▸
       at 0 6 (Bx2-1430 ∷ []) (refl) ▸ done


-- nat 1 BOX(1;230): 8 steps
lem-nat-1-BOX⟨1·230⟩ : WsL → ⟪ (Sw12 ∷ Bx1-230 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-130 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·230⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx1-230 ∷ []) (Bx2-130 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff123 ∷ Bx2-10 ∷ Toff123 ∷ CCZ123 ∷ Bx2-10 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw12 ∷ []) (sym (wl0111 c4)) ▸
       at 1 2 (Toff213 ∷ Sw12 ∷ []) (wl0146 c4) ▸
       at 2 2 (Bx1-20 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·10⟩ c4) ▸
       at 3 2 (Toff213 ∷ Sw12 ∷ []) (wl0146 c4) ▸
       at 4 2 (CCZ123 ∷ Sw12 ∷ []) (sym (wl0111 c4)) ▸
       at 5 2 (Bx1-20 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·10⟩ c4) ▸
       at 0 6 (Bx2-130 ∷ []) (refl) ▸ done


-- nat 1 BOX(2;1430): 8 steps
lem-nat-1-BOX⟨2·1430⟩ : WsL → ⟪ (Sw12 ∷ Bx2-1430 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2430 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·1430⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx2-1430 ∷ []) (Bx1-2430 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff214 ∷ Bx1-230 ∷ Toff214 ∷ CCZ124 ∷ Bx1-230 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw12 ∷ []) (sym (wl0078 c4)) ▸
       at 1 2 (Toff124 ∷ Sw12 ∷ []) (wl0126 c4) ▸
       at 2 2 (Bx2-130 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·230⟩ c4) ▸
       at 3 2 (Toff124 ∷ Sw12 ∷ []) (wl0126 c4) ▸
       at 4 2 (CCZ124 ∷ Sw12 ∷ []) (sym (wl0078 c4)) ▸
       at 5 2 (Bx2-130 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·230⟩ c4) ▸
       at 0 6 (Bx1-2430 ∷ []) (refl) ▸ done


-- comm CCZ123 CS04: 13 steps
lem-comm-CCZ123-CS04 : WsL → ⟪ (CCZ123 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ CCZ123 ∷ []) ⟫ʷ
lem-comm-CCZ123-CS04 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ123 ∷ CS04 ∷ []) (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ CCZ134 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 1 3 (CCZ124 ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 2 3 (CCZ134 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw12 ∷ CCZ234 ∷ []) (wl0034 c4) ▸
       at 3 2 (CS01 ∷ CCZ234 ∷ []) (sym (c₂ (CS) (CCZ))) ▸
       at 4 2 (Sw12 ∷ CCZ134 ∷ []) (wl0084 c4) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ CCZ134 ∷ Sw23 ∷ Sw34 ∷ []) (CS04 ∷ CCZ123 ∷ [])
  b1 = at 5 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0006 c4) ▸
       at 6 1 (Sw34 ∷ CCZ123 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0007 c4) ▸
       at 0 7 (CS04 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CCZ013 CS24: 15 steps
lem-comm-CCZ013-CS24 : WsL → ⟪ (CCZ013 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CCZ013 ∷ []) ⟫ʷ
lem-comm-CCZ013-CS24 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ013 ∷ CS24 ∷ []) (Sw34 ∷ Sw34 ∷ Sw23 ∷ CS34 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 1 3 (CCZ014 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 5 3 (CS24 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS34 ∷ Sw23 ∷ []) (sym (wl0011 c4)) ▸
       at 3 2 (CS34 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CS)) ▸ done

  b1 : Chain (Sw34 ∷ Sw34 ∷ Sw23 ∷ CS34 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ []) (CS24 ∷ CCZ013 ∷ [])
  b1 = at 2 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0015 c4)) ▸
       at 2 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (wl0007 c4) ▸
       at 2 5 (CCZ014 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ CCZ013 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0007 c4) ▸
       at 0 3 (CS24 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CK40 CCZ123: 13 steps
lem-comm-CK40-CCZ123 : WsL → ⟪ (CK40 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CK40 ∷ []) ⟫ʷ
lem-comm-CK40-CCZ123 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CK40 ∷ CCZ123 ∷ []) (Sw34 ∷ Sw23 ∷ CCZ134 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 0 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 6 3 (CCZ124 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 5 3 (CCZ134 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CCZ234 ∷ Sw12 ∷ []) (sym (wl0084 c4)) ▸
       at 3 2 (CCZ234 ∷ CK10 ∷ []) (c₂ (CK₁₀) (CCZ)) ▸
       at 2 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0034 c4)) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ CCZ134 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (CCZ123 ∷ CK40 ∷ [])
  b1 = at 2 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (wl0006 c4) ▸
       at 1 1 (Sw34 ∷ CCZ123 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0007 c4) ▸
       at 1 7 (CK40 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CCZ123 CK40: 13 steps
lem-comm-CCZ123-CK40 : WsL → ⟪ (CCZ123 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ CCZ123 ∷ []) ⟫ʷ
lem-comm-CCZ123-CK40 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ123 ∷ CK40 ∷ []) (Sw34 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ CCZ134 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 1 3 (CCZ124 ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 2 3 (CCZ134 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw12 ∷ CCZ234 ∷ []) (wl0034 c4) ▸
       at 3 2 (CK10 ∷ CCZ234 ∷ []) (sym (c₂ (CK₁₀) (CCZ))) ▸
       at 4 2 (Sw12 ∷ CCZ134 ∷ []) (wl0084 c4) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ CCZ134 ∷ Sw23 ∷ Sw34 ∷ []) (CK40 ∷ CCZ123 ∷ [])
  b1 = at 5 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0006 c4) ▸
       at 6 1 (Sw34 ∷ CCZ123 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0007 c4) ▸
       at 0 7 (CK40 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp CK40 at 3: 20 steps
lem-resp-CK40-at-3 : WsL → ⟪ (CK40 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-CK40-at-3 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CK40 ∷ []) (Sw23 ∷ CK40 ∷ Sw23 ∷ [])
  b0 = at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 0 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (wl0013 c4) ▸
       at 4 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 3 2 (Sw34 ∷ CK10 ∷ []) (c₂ (CK₁₀) (Swap ↑)) ▸
       at 2 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 0 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (sym (wl0013 c4)) ▸
       at 1 7 (CK40 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ CK40 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ CK30 ∷ Sw34 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b1 = at 2 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 1 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 2 2 (Sw12 ∷ CK30 ∷ []) (wl0159 c4) ▸
       at 1 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 2 3 (CK40 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 c4)) ▸
       at 2 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ CK30 ∷ Sw34 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b2 = at 4 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 3 2 (Sw01 ∷ CK31 ∷ []) (wl0117 c4) ▸
       at 2 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 3 3 (CK41 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CK41 TOFF203: 7 steps
lem-comm-CK41-TOFF203 : WsL → ⟪ (CK41 ∷ Toff203 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ CK41 ∷ []) ⟫ʷ
lem-comm-CK41-TOFF203 c4 = run b0
  where
  b0 : Chain (CK41 ∷ Toff203 ∷ []) (Toff203 ∷ CK41 ∷ [])
  b0 = at 1 1 (Sw12 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw12 ∷ CK42 ∷ []) (wl0160 c4) ▸
       at 1 2 (Sw23 ∷ CK43 ∷ []) (wl0162 c4) ▸
       at 2 2 (Toff102 ∷ CK43 ∷ []) (sym (c₃ (K ↑ • CCZ • K ↑ • iI) (CK₁₀))) ▸
       at 3 2 (Sw23 ∷ CK42 ∷ []) (wl0163 c4) ▸
       at 4 2 (Sw12 ∷ CK41 ∷ []) (wl0164 c4) ▸
       at 0 5 (Toff203 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp CK41 at 3: 6 steps
lem-resp-CK41-at-3 : WsL → ⟪ (CK41 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ CK42 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-CK41-at-3 c4 = run b0
  where
  b0 : Chain (CK41 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ CK42 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 0 2 (Sw23 ∷ CK41 ∷ []) (wl0165 c4) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 1 2 (Sw12 ∷ CK42 ∷ []) (wl0160 c4) ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 c4)) ▸
       at 2 2 (Sw01 ∷ CK42 ∷ []) (sym (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑))) ▸ done


-- comm CK41 CCZ023: 7 steps
lem-comm-CK41-CCZ023 : WsL → ⟪ (CK41 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ CK41 ∷ []) ⟫ʷ
lem-comm-CK41-CCZ023 c4 = run b0
  where
  b0 : Chain (CK41 ∷ CCZ023 ∷ []) (CCZ023 ∷ CK41 ∷ [])
  b0 = at 1 1 (Sw12 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw12 ∷ CK42 ∷ []) (wl0160 c4) ▸
       at 1 2 (Sw23 ∷ CK43 ∷ []) (wl0162 c4) ▸
       at 2 2 (CCZ012 ∷ CK43 ∷ []) (sym (c₃ (CCZ) (CK₁₀))) ▸
       at 3 2 (Sw23 ∷ CK42 ∷ []) (wl0163 c4) ▸
       at 4 2 (Sw12 ∷ CK41 ∷ []) (wl0164 c4) ▸
       at 0 5 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CK41 TOFF023: 7 steps
lem-comm-CK41-TOFF023 : WsL → ⟪ (CK41 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CK41 ∷ []) ⟫ʷ
lem-comm-CK41-TOFF023 c4 = run b0
  where
  b0 : Chain (CK41 ∷ Toff023 ∷ []) (Toff023 ∷ CK41 ∷ [])
  b0 = at 1 1 (Sw12 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw12 ∷ CK42 ∷ []) (wl0160 c4) ▸
       at 1 2 (Sw23 ∷ CK43 ∷ []) (wl0162 c4) ▸
       at 2 2 (Toff012 ∷ CK43 ∷ []) (sym (c₃ (Toff) (CK₁₀))) ▸
       at 3 2 (Sw23 ∷ CK42 ∷ []) (wl0163 c4) ▸
       at 4 2 (Sw12 ∷ CK41 ∷ []) (wl0164 c4) ▸
       at 0 5 (Toff023 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CCZ013 CK42: 15 steps
lem-comm-CCZ013-CK42 : WsL → ⟪ (CCZ013 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ CCZ013 ∷ []) ⟫ʷ
lem-comm-CCZ013-CK42 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ013 ∷ CK42 ∷ []) (Sw34 ∷ Sw34 ∷ Sw23 ∷ CK43 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ CK32 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 1 3 (CCZ014 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 5 3 (CK42 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CK43 ∷ Sw23 ∷ []) (sym (wl0163 c4)) ▸
       at 3 2 (CK43 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CK₁₀)) ▸ done

  b1 : Chain (Sw34 ∷ Sw34 ∷ Sw23 ∷ CK43 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ []) (CK42 ∷ CCZ013 ∷ [])
  b1 = at 2 2 (CK42 ∷ Sw23 ∷ []) (sym (wl0162 c4)) ▸
       at 2 1 (Sw34 ∷ CK32 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (wl0007 c4) ▸
       at 2 5 (CCZ014 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ CCZ013 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0007 c4) ▸
       at 0 3 (CK42 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CK42 TOFF013: 5 steps
lem-comm-CK42-TOFF013 : WsL → ⟪ (CK42 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CK42 ∷ []) ⟫ʷ
lem-comm-CK42-TOFF013 c4 = run b0
  where
  b0 : Chain (CK42 ∷ Toff013 ∷ []) (Toff013 ∷ CK42 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw23 ∷ CK43 ∷ []) (wl0162 c4) ▸
       at 1 2 (Toff012 ∷ CK43 ∷ []) (sym (c₃ (Toff) (CK₁₀))) ▸
       at 2 2 (Sw23 ∷ CK42 ∷ []) (wl0163 c4) ▸
       at 0 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CK42 CCZ013: 5 steps
lem-comm-CK42-CCZ013 : WsL → ⟪ (CK42 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ CK42 ∷ []) ⟫ʷ
lem-comm-CK42-CCZ013 c4 = run b0
  where
  b0 : Chain (CK42 ∷ CCZ013 ∷ []) (CCZ013 ∷ CK42 ∷ [])
  b0 = at 1 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw23 ∷ CK43 ∷ []) (wl0162 c4) ▸
       at 1 2 (CCZ012 ∷ CK43 ∷ []) (sym (c₃ (CCZ) (CK₁₀))) ▸
       at 2 2 (Sw23 ∷ CK42 ∷ []) (wl0163 c4) ▸
       at 0 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp TOFF413 at 2: 4 steps
lem-resp-TOFF413-at-2 : WsL → ⟪ (Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ Toff423 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-TOFF413-at-2 c4 = run b0
  where
  b0 : Chain (Toff413 ∷ []) (Sw12 ∷ Sw01 ∷ Toff423 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 0 2 (Sw12 ∷ Toff423 ∷ []) (sym (wl0091 c4)) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 c4)) ▸
       at 1 2 (Sw01 ∷ Toff423 ∷ []) (sym (c₂ (Swap) (Toffᵗ))) ▸ done


-- nat 0 SBOX(2;0;1;3): 3 steps
lem-nat-0-SBOX⟨2·0·1·3⟩ : WsL → ⟪ (Sw01 ∷ Sb2-0-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-1-0-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨2·0·1·3⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb2-0-1-3 ∷ []) (Sb2-1-0-3 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS01 ∷ []) (refl) ▸
       at 0 2 (CS01 ∷ Sw01 ∷ []) (sym (wl0132 c4)) ▸
       at 0 1 (Sb2-1-0-3 ∷ []) (refl) ▸ done


-- nat 0 SBOXd(2;0;1;3): 3 steps
lem-nat-0-SBOXd⟨2·0·1·3⟩ : WsL → ⟪ (Sw01 ∷ Sb⁻2-0-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-1-0-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨2·0·1·3⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻2-0-1-3 ∷ []) (Sb⁻2-1-0-3 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS01⁻ ∷ []) (refl) ▸
       at 0 2 (CS01⁻ ∷ Sw01 ∷ []) (sym (wl0133 c4)) ▸
       at 0 1 (Sb⁻2-1-0-3 ∷ []) (refl) ▸ done


-- nat 3 BOX(2;031): 8 steps
lem-nat-3-BOX⟨2·031⟩ : WsL → ⟪ (Sw34 ∷ Bx2-031 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-041 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨2·031⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx2-031 ∷ []) (Bx2-041 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff203 ∷ Bx0-21 ∷ Toff203 ∷ CCZ023 ∷ Bx0-21 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw34 ∷ []) (lem-nat-3-CCZ023 c4) ▸
       at 1 2 (Toff204 ∷ Sw34 ∷ []) (lem-nat-3-TOFF203 c4) ▸
       at 2 2 (Bx0-21 ∷ Sw34 ∷ []) (sym (c₃ (CZ ↑) (Swap))) ▸
       at 3 2 (Toff204 ∷ Sw34 ∷ []) (lem-nat-3-TOFF203 c4) ▸
       at 4 2 (CCZ024 ∷ Sw34 ∷ []) (lem-nat-3-CCZ023 c4) ▸
       at 5 2 (Bx0-21 ∷ Sw34 ∷ []) (sym (c₃ (CZ ↑) (Swap))) ▸
       at 0 6 (Bx2-041 ∷ []) (refl) ▸ done


-- nat 3 BOX(0;2431): 8 steps
lem-nat-3-BOX⟨0·2431⟩ : WsL → ⟪ (Sw34 ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2341 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·2431⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx0-2431 ∷ []) (Bx0-2341 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff024 ∷ Bx2-031 ∷ Toff024 ∷ CCZ024 ∷ Bx2-031 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 c4) ▸
       at 1 2 (Toff023 ∷ Sw34 ∷ []) (lem-nat-3-TOFF024 c4) ▸
       at 2 2 (Bx2-041 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·031⟩ c4) ▸
       at 3 2 (Toff023 ∷ Sw34 ∷ []) (lem-nat-3-TOFF024 c4) ▸
       at 4 2 (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 c4) ▸
       at 5 2 (Bx2-041 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·031⟩ c4) ▸
       at 0 6 (Bx0-2341 ∷ []) (refl) ▸ done


-- nat 3 BOX(2;041): 8 steps
lem-nat-3-BOX⟨2·041⟩ : WsL → ⟪ (Sw34 ∷ Bx2-041 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-031 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨2·041⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx2-041 ∷ []) (Bx2-031 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff204 ∷ Bx0-21 ∷ Toff204 ∷ CCZ024 ∷ Bx0-21 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 c4) ▸
       at 1 2 (Toff203 ∷ Sw34 ∷ []) (lem-nat-3-TOFF204 c4) ▸
       at 2 2 (Bx0-21 ∷ Sw34 ∷ []) (sym (c₃ (CZ ↑) (Swap))) ▸
       at 3 2 (Toff203 ∷ Sw34 ∷ []) (lem-nat-3-TOFF204 c4) ▸
       at 4 2 (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 c4) ▸
       at 5 2 (Bx0-21 ∷ Sw34 ∷ []) (sym (c₃ (CZ ↑) (Swap))) ▸
       at 0 6 (Bx2-031 ∷ []) (refl) ▸ done


-- nat 3 BOX(0;2341): 8 steps
lem-nat-3-BOX⟨0·2341⟩ : WsL → ⟪ (Sw34 ∷ Bx0-2341 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·2341⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx0-2341 ∷ []) (Bx0-2431 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff023 ∷ Bx2-041 ∷ Toff023 ∷ CCZ023 ∷ Bx2-041 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw34 ∷ []) (lem-nat-3-CCZ023 c4) ▸
       at 1 2 (Toff024 ∷ Sw34 ∷ []) (lem-nat-3-TOFF023 c4) ▸
       at 2 2 (Bx2-031 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·041⟩ c4) ▸
       at 3 2 (Toff024 ∷ Sw34 ∷ []) (lem-nat-3-TOFF023 c4) ▸
       at 4 2 (CCZ024 ∷ Sw34 ∷ []) (lem-nat-3-CCZ023 c4) ▸
       at 5 2 (Bx2-031 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·041⟩ c4) ▸
       at 0 6 (Bx0-2431 ∷ []) (refl) ▸ done

