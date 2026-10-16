{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.R017 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (WsL ; wl0001 ; wl0002 ; wl0003 ; wl0004 ; wl0006 ; wl0007 ; wl0008 ; wl0009 ; wl0010 ; wl0011 ; wl0012 ; wl0013 ; wl0014 ; wl0015 ; wl0016 ; wl0017 ; wl0018 ; wl0019 ; wl0020 ; wl0021 ; wl0024 ; wl0025 ; wl0030 ; wl0034 ; wl0039 ; wl0040 ; wl0043 ; wl0046 ; wl0048 ; wl0055 ; wl0056 ; wl0057 ; wl0058 ; wl0059 ; wl0062 ; wl0065 ; wl0066 ; wl0067 ; wl0068 ; wl0086 ; wl0090 ; wl0093 ; wl0095 ; wl0103 ; wl0110 ; wl0113 ; wl0114 ; wl0116 ; wl0122 ; wl0127 ; wl0128 ; wl0132 ; wl0133 ; wl0134 ; wl0135 ; wl0140 ; wl0144 ; wl0151 ; wl0155 ; wl0166)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-nat-1-CCZ024 ; lem-nat-2-CCZ012 ; lem-nat-2-CCZ013 ; lem-nat-2-CCZ024 ; lem-nat-2-CCZ034 ; lem-nat-2-TOFF024 ; lem-nat-2-TOFF034 ; lem-nat-2-TOFF102 ; lem-nat-2-TOFF103 ; lem-nat-3-CCZ014 ; lem-nat-3-CCZ024 ; lem-nat-3-CCZ034 ; lem-nat-3-TOFF014)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-0-CCZ024 ; lem-nat-0-CCZ124 ; lem-nat-2-CCZ124 ; lem-nat-2-CCZ134 ; lem-nat-2-TOFF204 ; lem-nat-2-TOFF304 ; lem-nat-3-CCZ013 ; lem-nat-3-CCZ023 ; lem-nat-3-TOFF402)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-0-CCZ034 ; lem-nat-0-CCZ134 ; lem-nat-0-TOFF412 ; lem-nat-1-TOFF104 ; lem-nat-3-BOX⟨0·32⟩)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-0-TOFF204 ; lem-nat-3-TOFF301 ; lem-nat-3-TOFF302)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-2-BOX⟨2·0413⟩ ; lem-nat-2-BOX⟨3·0412⟩ ; lem-nat-2-CCZ014 ; lem-nat-2-TOFF214)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-1-CS01 ; lem-nat-2-CS12 ; lem-nat-2-CS13 ; lem-nat-2-CSd12 ; lem-nat-2-CSd13 ; lem-nat-2-CZ12 ; lem-nat-2-CZ13 ; lem-nat-2-TOFF314 ; lem-nat-3-CZ24)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-0-TOFF134 ; lem-nat-2-CS02 ; lem-nat-2-CSd02 ; lem-nat-2-TOFF124 ; lem-nat-3-CS23 ; lem-nat-3-CS24)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-nat-0-TOFF034 ; lem-nat-1-CSd01 ; lem-nat-1-TOFF034 ; lem-nat-3-TOFF401)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-1-TOFF402 ; lem-nat-2-CS03 ; lem-nat-2-CSd03 ; lem-nat-2-TOFF401)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-nat-3-TOFF034)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-nat-2-TOFF134)
open import Examples.Groups.Clifford+CS.Five.D.R012 using (lem-nat-2-BOX⟨3·21⟩ ; lem-nat-3-CSd24)
open import Examples.Groups.Clifford+CS.Five.D.R013 using (lem-nat-3-CSd23)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-nat-1-BOX⟨3·0421⟩ ; lem-nat-1-BOX⟨4·21⟩)
open import Examples.Groups.Clifford+CS.Five.D.R015 using (lem-nat-0-BOX⟨3·01⟩ ; lem-nat-0-BOX⟨3·10⟩ ; lem-nat-1-BOX⟨3·2401⟩ ; lem-nat-2-BOX⟨2·13⟩ ; lem-nat-2-BOX⟨2·31⟩)
open import Examples.Groups.Clifford+CS.Five.D.R016 using (lem-nat-0-BOX⟨2·0431⟩ ; lem-nat-0-SBOX⟨2·0·1·3⟩ ; lem-nat-0-SBOXd⟨2·0·1·3⟩ ; lem-nat-1-BOX⟨2·1430⟩ ; lem-nat-2-BOX⟨0·21⟩ ; lem-nat-2-BOX⟨0·31⟩)
-- nat 2 BOX(3;021): 8 steps
lem-nat-2-BOX⟨3·021⟩ : WsL → ⟪ (Sw23 ∷ Bx3-021 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-031 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·021⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx3-021 ∷ []) (Bx2-031 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff302 ∷ Bx0-31 ∷ Toff302 ∷ CCZ023 ∷ Bx0-31 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw23 ∷ []) (sym (wl0065 c4)) ▸
       at 1 2 (Toff203 ∷ Sw23 ∷ []) (wl0066 c4) ▸
       at 2 2 (Bx0-21 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·31⟩ c4) ▸
       at 3 2 (Toff203 ∷ Sw23 ∷ []) (wl0066 c4) ▸
       at 4 2 (CCZ023 ∷ Sw23 ∷ []) (sym (wl0065 c4)) ▸
       at 5 2 (Bx0-21 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·31⟩ c4) ▸
       at 0 6 (Bx2-031 ∷ []) (refl) ▸ done


-- nat 2 BOX(0;3421): 8 steps
lem-nat-2-BOX⟨0·3421⟩ : WsL → ⟪ (Sw23 ∷ Bx0-3421 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·3421⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-3421 ∷ []) (Bx0-2431 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff034 ∷ Bx3-021 ∷ Toff034 ∷ CCZ034 ∷ Bx3-021 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 1 2 (Toff024 ∷ Sw23 ∷ []) (lem-nat-2-TOFF034 c4) ▸
       at 2 2 (Bx2-031 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·021⟩ c4) ▸
       at 3 2 (Toff024 ∷ Sw23 ∷ []) (lem-nat-2-TOFF034 c4) ▸
       at 4 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 5 2 (Bx2-031 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·021⟩ c4) ▸
       at 0 6 (Bx0-2431 ∷ []) (refl) ▸ done


-- nat 2 SBOX(1;2;4;0): 3 steps
lem-nat-2-SBOX⟨1·2·4·0⟩ : WsL → ⟪ (Sw23 ∷ Sb1-2-4-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-3-4-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨1·2·4·0⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb1-2-4-0 ∷ []) (Sb1-3-4-0 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS24 ∷ []) (refl) ▸
       at 0 2 (CS34 ∷ Sw23 ∷ []) (sym (wl0011 c4)) ▸
       at 0 1 (Sb1-3-4-0 ∷ []) (refl) ▸ done


-- nat 2 SBOX(1;3;4;0): 3 steps
lem-nat-2-SBOX⟨1·3·4·0⟩ : WsL → ⟪ (Sw23 ∷ Sb1-3-4-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-4-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨1·3·4·0⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb1-3-4-0 ∷ []) (Sb1-2-4-0 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS34 ∷ []) (refl) ▸
       at 0 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0015 c4)) ▸
       at 0 1 (Sb1-2-4-0 ∷ []) (refl) ▸ done


-- nat 3 SBOX(1;2;3;0): 3 steps
lem-nat-3-SBOX⟨1·2·3·0⟩ : WsL → ⟪ (Sw34 ∷ Sb1-2-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-4-0 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨1·2·3·0⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb1-2-3-0 ∷ []) (Sb1-2-4-0 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS23 ∷ []) (refl) ▸
       at 0 2 (CS24 ∷ Sw34 ∷ []) (lem-nat-3-CS23 c4) ▸
       at 0 1 (Sb1-2-4-0 ∷ []) (refl) ▸ done


-- nat 3 SBOX(1;2;4;0): 3 steps
lem-nat-3-SBOX⟨1·2·4·0⟩ : WsL → ⟪ (Sw34 ∷ Sb1-2-4-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-3-0 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨1·2·4·0⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb1-2-4-0 ∷ []) (Sb1-2-3-0 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS24 ∷ []) (refl) ▸
       at 0 2 (CS23 ∷ Sw34 ∷ []) (lem-nat-3-CS24 c4) ▸
       at 0 1 (Sb1-2-3-0 ∷ []) (refl) ▸ done


-- nat 1 SBOX(0;1;3;2): 3 steps
lem-nat-1-SBOX⟨0·1·3·2⟩ : WsL → ⟪ (Sw12 ∷ Sb0-1-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-3-1 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨0·1·3·2⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb0-1-3-2 ∷ []) (Sb0-2-3-1 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS13 ∷ []) (refl) ▸
       at 0 2 (CS23 ∷ Sw12 ∷ []) (sym (wl0025 c4)) ▸
       at 0 1 (Sb0-2-3-1 ∷ []) (refl) ▸ done


-- nat 1 SBOX(0;2;3;1): 3 steps
lem-nat-1-SBOX⟨0·2·3·1⟩ : WsL → ⟪ (Sw12 ∷ Sb0-2-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-3-2 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨0·2·3·1⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb0-2-3-1 ∷ []) (Sb0-1-3-2 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS23 ∷ []) (refl) ▸
       at 0 2 (CS13 ∷ Sw12 ∷ []) (sym (wl0024 c4)) ▸
       at 0 1 (Sb0-1-3-2 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(1;2;4;0): 3 steps
lem-nat-2-SBOXd⟨1·2·4·0⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻1-2-4-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-3-4-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨1·2·4·0⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻1-2-4-0 ∷ []) (Sb⁻1-3-4-0 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS24⁻ ∷ []) (refl) ▸
       at 0 2 (CS34⁻ ∷ Sw23 ∷ []) (sym (wl0012 c4)) ▸
       at 0 1 (Sb⁻1-3-4-0 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(1;3;4;0): 3 steps
lem-nat-2-SBOXd⟨1·3·4·0⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻1-3-4-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-2-4-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨1·3·4·0⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻1-3-4-0 ∷ []) (Sb⁻1-2-4-0 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS34⁻ ∷ []) (refl) ▸
       at 0 2 (CS24⁻ ∷ Sw23 ∷ []) (sym (wl0016 c4)) ▸
       at 0 1 (Sb⁻1-2-4-0 ∷ []) (refl) ▸ done


-- nat 3 SBOXd(1;2;3;0): 3 steps
lem-nat-3-SBOXd⟨1·2·3·0⟩ : WsL → ⟪ (Sw34 ∷ Sb⁻1-2-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-2-4-0 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨1·2·3·0⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb⁻1-2-3-0 ∷ []) (Sb⁻1-2-4-0 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS23⁻ ∷ []) (refl) ▸
       at 0 2 (CS24⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd23 c4) ▸
       at 0 1 (Sb⁻1-2-4-0 ∷ []) (refl) ▸ done


-- nat 3 SBOXd(1;2;4;0): 3 steps
lem-nat-3-SBOXd⟨1·2·4·0⟩ : WsL → ⟪ (Sw34 ∷ Sb⁻1-2-4-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-2-3-0 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨1·2·4·0⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb⁻1-2-4-0 ∷ []) (Sb⁻1-2-3-0 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS24⁻ ∷ []) (refl) ▸
       at 0 2 (CS23⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd24 c4) ▸
       at 0 1 (Sb⁻1-2-3-0 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(0;1;3;2): 3 steps
lem-nat-1-SBOXd⟨0·1·3·2⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻0-1-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-2-3-1 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨0·1·3·2⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻0-1-3-2 ∷ []) (Sb⁻0-2-3-1 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS13⁻ ∷ []) (refl) ▸
       at 0 2 (CS23⁻ ∷ Sw12 ∷ []) (sym (wl0046 c4)) ▸
       at 0 1 (Sb⁻0-2-3-1 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(0;2;3;1): 3 steps
lem-nat-1-SBOXd⟨0·2·3·1⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻0-2-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-3-2 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨0·2·3·1⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻0-2-3-1 ∷ []) (Sb⁻0-1-3-2 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS23⁻ ∷ []) (refl) ▸
       at 0 2 (CS13⁻ ∷ Sw12 ∷ []) (sym (wl0043 c4)) ▸
       at 0 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸ done


-- resp TOFF203 at 1: 2 steps
lem-resp-TOFF203-at-1 : WsL → ⟪ (Toff203 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Toff213 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-TOFF203-at-1 c4 = run b0
  where
  b0 : Chain (Toff203 ∷ []) (Sw01 ∷ Toff213 ∷ Sw01 ∷ [])
  b0 = at 1 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 c4)) ▸
       at 0 2 (Sw01 ∷ Toff213 ∷ []) (sym (wl0004 c4)) ▸ done


-- resp CX14 at 2: 4 steps
lem-resp-CX14-at-2 : WsL → ⟪ (CX14 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CX24 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CX14-at-2 c4 = run b0
  where
  b0 : Chain (CX14 ∷ []) (Sw12 ∷ Sw01 ∷ CX24 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 0 2 (Sw12 ∷ CX24 ∷ []) (wl0055 c4) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 c4)) ▸
       at 1 2 (Sw01 ∷ CX24 ∷ []) (sym (c₂ (Swap) (Swap ↑ • CX₀₁ • Swap ↑))) ▸ done


-- nat 1 SBOX(3;0;1;2): 3 steps
lem-nat-1-SBOX⟨3·0·1·2⟩ : WsL → ⟪ (Sw12 ∷ Sb3-0-1-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-2-1 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨3·0·1·2⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb3-0-1-2 ∷ []) (Sb3-0-2-1 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS01 ∷ []) (refl) ▸
       at 0 2 (CS02 ∷ Sw12 ∷ []) (lem-nat-1-CS01 c4) ▸
       at 0 1 (Sb3-0-2-1 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(3;0;1;2): 3 steps
lem-nat-1-SBOXd⟨3·0·1·2⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻3-0-1-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻3-0-2-1 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨3·0·1·2⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻3-0-1-2 ∷ []) (Sb⁻3-0-2-1 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS01⁻ ∷ []) (refl) ▸
       at 0 2 (CS02⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd01 c4) ▸
       at 0 1 (Sb⁻3-0-2-1 ∷ []) (refl) ▸ done


-- nat 1 SBOX(3;0;42;1): 7 steps
lem-nat-1-SBOX⟨3·0·42·1⟩ : WsL → ⟪ (Sw12 ∷ Sb3-0-42-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-41-2 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨3·0·42·1⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb3-0-42-1 ∷ []) (Sb3-0-41-2 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx3-0421 ∷ Toff124 ∷ Sb3-0-1-2 ∷ Toff124 ∷ Sb⁻3-0-1-2 ∷ []) (refl) ▸
       at 0 2 (Bx3-0412 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0421⟩ c4) ▸
       at 1 2 (Toff214 ∷ Sw12 ∷ []) (wl0095 c4) ▸
       at 2 2 (Sb3-0-2-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·1·2⟩ c4) ▸
       at 3 2 (Toff214 ∷ Sw12 ∷ []) (wl0095 c4) ▸
       at 4 2 (Sb⁻3-0-2-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨3·0·1·2⟩ c4) ▸
       at 0 5 (Sb3-0-41-2 ∷ []) (refl) ▸ done


-- nat 2 SBOX(2;0;3;1): 3 steps
lem-nat-2-SBOX⟨2·0·3·1⟩ : WsL → ⟪ (Sw23 ∷ Sb2-0-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-2-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨2·0·3·1⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb2-0-3-1 ∷ []) (Sb3-0-2-1 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS03 ∷ []) (refl) ▸
       at 0 2 (CS02 ∷ Sw23 ∷ []) (lem-nat-2-CS03 c4) ▸
       at 0 1 (Sb3-0-2-1 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(2;0;3;1): 3 steps
lem-nat-2-SBOXd⟨2·0·3·1⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻2-0-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻3-0-2-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨2·0·3·1⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻2-0-3-1 ∷ []) (Sb⁻3-0-2-1 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS03⁻ ∷ []) (refl) ▸
       at 0 2 (CS02⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd03 c4) ▸
       at 0 1 (Sb⁻3-0-2-1 ∷ []) (refl) ▸ done


-- nat 2 SBOX(2;0;41;3): 7 steps
lem-nat-2-SBOX⟨2·0·41·3⟩ : WsL → ⟪ (Sw23 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-41-2 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨2·0·41·3⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb2-0-41-3 ∷ []) (Sb3-0-41-2 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 0 2 (Bx3-0412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0413⟩ c4) ▸
       at 1 2 (Toff214 ∷ Sw23 ∷ []) (lem-nat-2-TOFF314 c4) ▸
       at 2 2 (Sb3-0-2-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨2·0·3·1⟩ c4) ▸
       at 3 2 (Toff214 ∷ Sw23 ∷ []) (lem-nat-2-TOFF314 c4) ▸
       at 4 2 (Sb⁻3-0-2-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨2·0·3·1⟩ c4) ▸
       at 0 5 (Sb3-0-41-2 ∷ []) (refl) ▸ done


-- nat 2 SBOX(3;0;2;1): 3 steps
lem-nat-2-SBOX⟨3·0·2·1⟩ : WsL → ⟪ (Sw23 ∷ Sb3-0-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-3-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨3·0·2·1⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb3-0-2-1 ∷ []) (Sb2-0-3-1 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS02 ∷ []) (refl) ▸
       at 0 2 (CS03 ∷ Sw23 ∷ []) (lem-nat-2-CS02 c4) ▸
       at 0 1 (Sb2-0-3-1 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(3;0;2;1): 3 steps
lem-nat-2-SBOXd⟨3·0·2·1⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻3-0-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-0-3-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨3·0·2·1⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻3-0-2-1 ∷ []) (Sb⁻2-0-3-1 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS02⁻ ∷ []) (refl) ▸
       at 0 2 (CS03⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd02 c4) ▸
       at 0 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸ done


-- nat 2 SBOX(3;0;41;2): 7 steps
lem-nat-2-SBOX⟨3·0·41·2⟩ : WsL → ⟪ (Sw23 ∷ Sb3-0-41-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨3·0·41·2⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb3-0-41-2 ∷ []) (Sb2-0-41-3 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (refl) ▸
       at 0 2 (Bx2-0413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0412⟩ c4) ▸
       at 1 2 (Toff314 ∷ Sw23 ∷ []) (lem-nat-2-TOFF214 c4) ▸
       at 2 2 (Sb2-0-3-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·0·2·1⟩ c4) ▸
       at 3 2 (Toff314 ∷ Sw23 ∷ []) (lem-nat-2-TOFF214 c4) ▸
       at 4 2 (Sb⁻2-0-3-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨3·0·2·1⟩ c4) ▸
       at 0 5 (Sb2-0-41-3 ∷ []) (refl) ▸ done


-- nat 2 BOX(4;13): 3 steps
lem-nat-2-BOX⟨4·13⟩ : WsL → ⟪ (Sw23 ∷ Bx4-13 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-12 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·13⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx4-13 ∷ []) (Bx4-12 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ13 ∷ []) (refl) ▸
       at 0 2 (CZ12 ∷ Sw23 ∷ []) (lem-nat-2-CZ13 c4) ▸
       at 0 1 (Bx4-12 ∷ []) (refl) ▸ done


-- nat 2 BOX(1;423): 8 steps
lem-nat-2-BOX⟨1·423⟩ : WsL → ⟪ (Sw23 ∷ Bx1-423 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-432 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·423⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx1-423 ∷ []) (Bx1-432 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff124 ∷ Bx4-13 ∷ Toff124 ∷ CCZ124 ∷ Bx4-13 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 1 2 (Toff134 ∷ Sw23 ∷ []) (lem-nat-2-TOFF124 c4) ▸
       at 2 2 (Bx4-12 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·13⟩ c4) ▸
       at 3 2 (Toff134 ∷ Sw23 ∷ []) (lem-nat-2-TOFF124 c4) ▸
       at 4 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 5 2 (Bx4-12 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·13⟩ c4) ▸
       at 0 6 (Bx1-432 ∷ []) (refl) ▸ done


-- nat 2 BOX(4;1023): 8 steps
lem-nat-2-BOX⟨4·1023⟩ : WsL → ⟪ (Sw23 ∷ Bx4-1023 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1032 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·1023⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx4-1023 ∷ []) (Bx4-1032 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff401 ∷ Bx1-423 ∷ Toff401 ∷ CCZ014 ∷ Bx1-423 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 1 2 (Toff401 ∷ Sw23 ∷ []) (lem-nat-2-TOFF401 c4) ▸
       at 2 2 (Bx1-432 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·423⟩ c4) ▸
       at 3 2 (Toff401 ∷ Sw23 ∷ []) (lem-nat-2-TOFF401 c4) ▸
       at 4 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 5 2 (Bx1-432 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·423⟩ c4) ▸
       at 0 6 (Bx4-1032 ∷ []) (refl) ▸ done


-- nat 1 BOX(2;431): 8 steps
lem-nat-1-BOX⟨2·431⟩ : WsL → ⟪ (Sw12 ∷ Bx2-431 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-432 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·431⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx2-431 ∷ []) (Bx1-432 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff234 ∷ Bx4-21 ∷ Toff234 ∷ CCZ234 ∷ Bx4-21 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0034 c4)) ▸
       at 1 2 (Toff134 ∷ Sw12 ∷ []) (wl0140 c4) ▸
       at 2 2 (Bx4-12 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·21⟩ c4) ▸
       at 3 2 (Toff134 ∷ Sw12 ∷ []) (wl0140 c4) ▸
       at 4 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0034 c4)) ▸
       at 5 2 (Bx4-12 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·21⟩ c4) ▸
       at 0 6 (Bx1-432 ∷ []) (refl) ▸ done


-- nat 1 BOX(4;2031): 8 steps
lem-nat-1-BOX⟨4·2031⟩ : WsL → ⟪ (Sw12 ∷ Bx4-2031 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1032 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·2031⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx4-2031 ∷ []) (Bx4-1032 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff402 ∷ Bx2-431 ∷ Toff402 ∷ CCZ024 ∷ Bx2-431 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 1 2 (Toff401 ∷ Sw12 ∷ []) (lem-nat-1-TOFF402 c4) ▸
       at 2 2 (Bx1-432 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·431⟩ c4) ▸
       at 3 2 (Toff401 ∷ Sw12 ∷ []) (lem-nat-1-TOFF402 c4) ▸
       at 4 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 5 2 (Bx1-432 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·431⟩ c4) ▸
       at 0 6 (Bx4-1032 ∷ []) (refl) ▸ done


-- nat 3 TOFF403: 144 steps
lem-nat-3-TOFF403 : WsL → ⟪ (Sw34 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-TOFF403 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (run b17)))))))))))))))))
  where
  b0 : Chain (Sw34 ∷ Toff403 ∷ []) (Sw34 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K3 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Toff402 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw12 ∷ Toff401 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw34 ∷ Toff301 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (K3 ∷ Sw23 ∷ []) (sym (wl0057 c4)) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 5 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K3 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b1 = at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 7 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 9 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (K3 ∷ Sw23 ∷ []) (sym (wl0057 c4)) ▸
       at 11 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸ done

  b2 : Chain (Sw34 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ Sw12 ∷ K4 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b2 = at 12 2 [] (wl0006 c4) ▸
       at 3 2 (K4 ∷ Sw34 ∷ []) (sym (wl0067 c4)) ▸
       at 6 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 4 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 6 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸ done

  b3 : Chain (Sw34 ∷ Sw23 ∷ Sw12 ∷ K4 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ K4 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K4 ∷ ι ∷ Sw12 ∷ Sw23 ∷ [])
  b3 = at 10 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 8 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K4 ∷ Sw34 ∷ []) (sym (wl0067 c4)) ▸
       at 10 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 11 2 [] (wl0007 c4) ▸
       at 2 2 (K4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K ↑)) ▸
       at 3 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0008 c4)) ▸
       at 6 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸ done

  b4 : Chain (Sw34 ∷ Sw23 ∷ K4 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K4 ∷ ι ∷ Sw12 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ K4 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ K4 ∷ ι ∷ Sw12 ∷ Sw23 ∷ [])
  b4 = at 4 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS24⁻ ∷ Sw12 ∷ []) (sym (wl0009 c4)) ▸
       at 8 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 6 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 8 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 c4)) ▸
       at 9 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸ done

  b5 : Chain (Sw34 ∷ Sw23 ∷ K4 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ K4 ∷ ι ∷ Sw12 ∷ Sw23 ∷ []) (Sw34 ∷ K4 ∷ CS34 ∷ CX03 ∷ Sw23 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K4 ∷ ι ∷ Sw23 ∷ [])
  b5 = at 7 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K ↑)) ▸
       at 9 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 10 2 [] (wl0001 c4) ▸
       at 1 2 (K4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K)) ▸
       at 2 2 (CS34 ∷ Sw23 ∷ []) (sym (wl0011 c4)) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 3 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸ done

  b6 : Chain (Sw34 ∷ K4 ∷ CS34 ∷ CX03 ∷ Sw23 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K4 ∷ ι ∷ Sw23 ∷ []) (Sw34 ∷ K4 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Sw34 ∷ K4 ∷ ι ∷ Sw23 ∷ [])
  b6 = at 4 2 (CS34⁻ ∷ Sw23 ∷ []) (sym (wl0012 c4)) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 5 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (wl0013 c4) ▸
       at 8 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 9 2 (CS01 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸
       at 10 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸ done

  b7 : Chain (Sw34 ∷ K4 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Sw34 ∷ K4 ∷ ι ∷ Sw23 ∷ []) (K3 ∷ CS34 ∷ Sw34 ∷ CX03 ∷ Sw34 ∷ Sw34 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K4 ∷ ι ∷ [])
  b7 = at 11 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (sym (wl0013 c4)) ▸
       at 6 7 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K)) ▸
       at 8 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 9 2 [] (wl0006 c4) ▸
       at 0 2 (K3 ∷ Sw34 ∷ []) (sym (wl0068 c4)) ▸
       at 1 2 (CS34 ∷ Sw34 ∷ []) (sym (wl0039 c4)) ▸
       at 4 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸ done

  b8 : Chain (K3 ∷ CS34 ∷ Sw34 ∷ CX03 ∷ Sw34 ∷ Sw34 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K4 ∷ ι ∷ []) (K3 ∷ CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ K3 ∷ ι ∷ Sw34 ∷ [])
  b8 = at 2 3 (CX04 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS34⁻ ∷ Sw34 ∷ []) (sym (wl0040 c4)) ▸
       at 6 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 4 3 (CX04 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0007 c4) ▸
       at 6 2 (K3 ∷ Sw34 ∷ []) (sym (wl0068 c4)) ▸
       at 7 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸ done

  b9 : Chain (K3 ∷ CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ K3 ∷ ι ∷ Sw34 ∷ []) (Sw23 ∷ K2 ∷ CS24 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Sw34 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ K3 ∷ ι ∷ Sw34 ∷ [])
  b9 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 1 2 (K2 ∷ Sw23 ∷ []) (sym (wl0058 c4)) ▸
       at 2 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0015 c4)) ▸
       at 4 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (wl0013 c4) ▸
       at 5 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 6 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 7 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸ done

  b10 : Chain (Sw23 ∷ K2 ∷ CS24 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Sw34 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ K3 ∷ ι ∷ Sw34 ∷ []) (Sw23 ∷ K2 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Sw34 ∷ CS03 ∷ K3 ∷ ι ∷ Sw34 ∷ [])
  b10 = at 8 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (sym (wl0013 c4)) ▸
       at 3 7 (CX04 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS24⁻ ∷ Sw23 ∷ []) (sym (wl0016 c4)) ▸
       at 6 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (wl0013 c4) ▸
       at 7 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 8 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 9 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸ done

  b11 : Chain (Sw23 ∷ K2 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Sw34 ∷ CS03 ∷ K3 ∷ ι ∷ Sw34 ∷ []) (Sw23 ∷ Sw12 ∷ K1 ∷ Sw12 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw34 ∷ [])
  b11 = at 10 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (sym (wl0013 c4)) ▸
       at 5 7 (CX04 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0006 c4) ▸
       at 7 2 (K2 ∷ Sw23 ∷ []) (sym (wl0058 c4)) ▸
       at 8 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 2 2 (K1 ∷ Sw12 ∷ []) (sym (wl0062 c4)) ▸ done

  b12 : Chain (Sw23 ∷ Sw12 ∷ K1 ∷ Sw12 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw34 ∷ []) (Sw23 ∷ Sw12 ∷ K1 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ Sw12 ∷ Sw34 ∷ CX03 ∷ Sw34 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw34 ∷ [])
  b12 = at 3 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0017 c4)) ▸
       at 5 1 (Sw34 ∷ CX03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 5 2 (CX03 ∷ Sw12 ∷ []) (sym (wl0014 c4)) ▸
       at 6 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 4 3 (CX04 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS14⁻ ∷ Sw12 ∷ []) (sym (wl0018 c4)) ▸
       at 7 1 (Sw34 ∷ CX03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b13 : Chain (Sw23 ∷ Sw12 ∷ K1 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ Sw12 ∷ Sw34 ∷ CX03 ∷ Sw34 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw34 ∷ []) (Sw23 ∷ Sw12 ∷ K1 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ [])
  b13 = at 6 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 7 2 (CX03 ∷ Sw12 ∷ []) (sym (wl0014 c4)) ▸
       at 8 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 6 3 (CX04 ∷ []) (by-assoc Eq.refl) ▸
       at 8 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0001 c4) ▸
       at 8 2 (K1 ∷ Sw12 ∷ []) (sym (wl0062 c4)) ▸
       at 9 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸ done

  b14 : Chain (Sw23 ∷ Sw12 ∷ K1 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ CX03 ∷ CS13⁻ ∷ Sw34 ∷ CX04 ∷ CS01 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ [])
  b14 = at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 3 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 5 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0007 c4) ▸
       at 6 1 (Sw34 ∷ CX03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0007 c4) ▸
       at 7 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0007 c4) ▸ done

  b15 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ CX03 ∷ CS13⁻ ∷ Sw34 ∷ CX04 ∷ CS01 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K1 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ [])
  b15 = at 8 1 (Sw34 ∷ CX03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0007 c4) ▸
       at 8 2 (CS01 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸
       at 9 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 10 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 4 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b16 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K1 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K1 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ Sw23 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ [])
  b16 = at 5 2 [] (wl0006 c4) ▸
       at 7 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0006 c4) ▸
       at 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0006 c4) ▸
       at 9 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0006 c4) ▸
       at 9 2 (CS01 ∷ Sw23 ∷ []) (sym (c₂ (CS) (Swap))) ▸ done

  b17 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K1 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ Sw23 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (Toff304 ∷ Sw34 ∷ [])
  b17 = at 10 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 11 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 4 8 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (sym (wl0166 c4)) ▸
       at 4 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸
       at 3 3 (Toff103 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (Toff104 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff204 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Toff304 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 2 BOX(4;12): 3 steps
lem-nat-2-BOX⟨4·12⟩ : WsL → ⟪ (Sw23 ∷ Bx4-12 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-13 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·12⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx4-12 ∷ []) (Bx4-13 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ12 ∷ []) (refl) ▸
       at 0 2 (CZ13 ∷ Sw23 ∷ []) (lem-nat-2-CZ12 c4) ▸
       at 0 1 (Bx4-13 ∷ []) (refl) ▸ done


-- nat 2 BOX(1;432): 8 steps
lem-nat-2-BOX⟨1·432⟩ : WsL → ⟪ (Sw23 ∷ Bx1-432 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-423 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·432⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx1-432 ∷ []) (Bx1-423 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff134 ∷ Bx4-12 ∷ Toff134 ∷ CCZ134 ∷ Bx4-12 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 1 2 (Toff124 ∷ Sw23 ∷ []) (lem-nat-2-TOFF134 c4) ▸
       at 2 2 (Bx4-13 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·12⟩ c4) ▸
       at 3 2 (Toff124 ∷ Sw23 ∷ []) (lem-nat-2-TOFF134 c4) ▸
       at 4 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 5 2 (Bx4-13 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·12⟩ c4) ▸
       at 0 6 (Bx1-423 ∷ []) (refl) ▸ done


-- nat 2 BOX(4;1032): 8 steps
lem-nat-2-BOX⟨4·1032⟩ : WsL → ⟪ (Sw23 ∷ Bx4-1032 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1023 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·1032⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx4-1032 ∷ []) (Bx4-1023 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff401 ∷ Bx1-432 ∷ Toff401 ∷ CCZ014 ∷ Bx1-432 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 1 2 (Toff401 ∷ Sw23 ∷ []) (lem-nat-2-TOFF401 c4) ▸
       at 2 2 (Bx1-423 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·432⟩ c4) ▸
       at 3 2 (Toff401 ∷ Sw23 ∷ []) (lem-nat-2-TOFF401 c4) ▸
       at 4 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 5 2 (Bx1-423 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·432⟩ c4) ▸
       at 0 6 (Bx4-1023 ∷ []) (refl) ▸ done


-- nat 0 SBOX(3;1;0;2): 3 steps
lem-nat-0-SBOX⟨3·1·0·2⟩ : WsL → ⟪ (Sw01 ∷ Sb3-1-0-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-1-2 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨3·1·0·2⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb3-1-0-2 ∷ []) (Sb3-0-1-2 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS01 ∷ []) (refl) ▸
       at 0 2 (CS01 ∷ Sw01 ∷ []) (sym (wl0132 c4)) ▸
       at 0 1 (Sb3-0-1-2 ∷ []) (refl) ▸ done


-- nat 0 SBOXd(3;1;0;2): 3 steps
lem-nat-0-SBOXd⟨3·1·0·2⟩ : WsL → ⟪ (Sw01 ∷ Sb⁻3-1-0-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻3-0-1-2 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨3·1·0·2⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻3-1-0-2 ∷ []) (Sb⁻3-0-1-2 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS01⁻ ∷ []) (refl) ▸
       at 0 2 (CS01⁻ ∷ Sw01 ∷ []) (sym (wl0133 c4)) ▸
       at 0 1 (Sb⁻3-0-1-2 ∷ []) (refl) ▸ done


-- resp TOFF304 at 2: 236 steps
lem-resp-TOFF304-at-2 : WsL → ⟪ (Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ Toff314 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-TOFF304-at-2 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (run b29)))))))))))))))))))))))))))))
  where
  b0 : Chain (Toff304 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 0 1 (Sw23 ∷ Toff204 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (Sw12 ∷ Toff104 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ Toff103 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸ done

  b1 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ Sw23 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ [])
  b1 = at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 6 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸ done

  b2 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ Sw23 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ []) (Sw23 ∷ Sw12 ∷ K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ Sw34 ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ [])
  b2 = at 10 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 11 2 [] (wl0006 c4) ▸
       at 2 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 5 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 3 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 5 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b3 : Chain (Sw23 ∷ Sw12 ∷ K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ Sw34 ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ []) (Sw23 ∷ K2 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ [])
  b3 = at 6 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 9 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 7 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 9 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 10 2 [] (wl0007 c4) ▸
       at 1 2 (K2 ∷ Sw12 ∷ []) (sym (wl0056 c4)) ▸
       at 2 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0008 c4)) ▸ done

  b4 : Chain (Sw23 ∷ K2 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ []) (Sw23 ∷ K2 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ CS03 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ [])
  b4 = at 5 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 3 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS24⁻ ∷ Sw12 ∷ []) (sym (wl0009 c4)) ▸
       at 7 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 5 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 7 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 c4)) ▸ done

  b5 : Chain (Sw23 ∷ K2 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ CS03 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ []) (K3 ∷ CS34 ∷ Sw23 ∷ CX02 ∷ Sw23 ∷ Sw23 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ [])
  b5 = at 8 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 6 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K2 ∷ Sw12 ∷ []) (sym (wl0056 c4)) ▸
       at 8 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 9 2 [] (wl0001 c4) ▸
       at 0 2 (K3 ∷ Sw23 ∷ []) (sym (wl0057 c4)) ▸
       at 1 2 (CS34 ∷ Sw23 ∷ []) (sym (wl0011 c4)) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸ done

  b6 : Chain (K3 ∷ CS34 ∷ Sw23 ∷ CX02 ∷ Sw23 ∷ Sw23 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ []) (K3 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ [])
  b6 = at 2 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS34⁻ ∷ Sw23 ∷ []) (sym (wl0012 c4)) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 4 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (wl0013 c4) ▸
       at 7 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 8 2 (CS01 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸ done

  b7 : Chain (K3 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ []) (K3 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ Sw12 ∷ K3 ∷ ι ∷ Sw12 ∷ [])
  b7 = at 9 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 10 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (sym (wl0013 c4)) ▸
       at 5 7 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K3 ∷ Sw23 ∷ []) (sym (wl0057 c4)) ▸
       at 7 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 8 2 [] (wl0006 c4) ▸
       at 7 2 (Sw12 ∷ ι ∷ []) (c₁ (iI) (Swap)) ▸
       at 6 2 (Sw12 ∷ K3 ∷ []) (sym (c₃ (Swap ↑) (K))) ▸ done

  b8 : Chain (K3 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ Sw12 ∷ K3 ∷ ι ∷ Sw12 ∷ []) (K3 ∷ CS34 ∷ Sw12 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K3 ∷ ι ∷ Sw12 ∷ [])
  b8 = at 5 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 6 2 (Sw12 ∷ CS03 ∷ []) (wl0010 c4) ▸
       at 5 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 6 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw12 ∷ CX03 ∷ []) (wl0014 c4) ▸
       at 3 2 (Sw12 ∷ CS34⁻ ∷ []) (sym (c₃ (Swap ↑) (CS • CS • CS))) ▸
       at 2 2 (Sw12 ∷ CX03 ∷ []) (wl0014 c4) ▸ done

  b9 : Chain (K3 ∷ CS34 ∷ Sw12 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K3 ∷ ι ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ K2 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ Sw23 ∷ CX03 ∷ CS04 ∷ K3 ∷ ι ∷ Sw12 ∷ [])
  b9 = at 1 2 (Sw12 ∷ CS34 ∷ []) (sym (c₃ (Swap ↑) (CS))) ▸
       at 0 2 (Sw12 ∷ K3 ∷ []) (sym (c₃ (Swap ↑) (K))) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 2 2 (K2 ∷ Sw23 ∷ []) (sym (wl0058 c4)) ▸
       at 3 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0015 c4)) ▸
       at 5 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0006 c4) ▸
       at 5 2 (CS24⁻ ∷ Sw23 ∷ []) (sym (wl0016 c4)) ▸ done

  b10 : Chain (Sw12 ∷ Sw23 ∷ K2 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ Sw23 ∷ CX03 ∷ CS04 ∷ K3 ∷ ι ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ K2 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw23 ∷ K3 ∷ ι ∷ Sw12 ∷ [])
  b10 = at 7 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0006 c4) ▸
       at 8 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (wl0013 c4) ▸
       at 9 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 10 2 (CS01 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸
       at 11 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 12 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (sym (wl0013 c4)) ▸ done

  b11 : Chain (Sw12 ∷ Sw23 ∷ K2 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw23 ∷ K3 ∷ ι ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ K1 ∷ CS14 ∷ CX01 ∷ Sw12 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw12 ∷ [])
  b11 = at 7 7 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K2 ∷ Sw23 ∷ []) (sym (wl0058 c4)) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 3 2 (K1 ∷ Sw12 ∷ []) (sym (wl0062 c4)) ▸
       at 4 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0017 c4)) ▸
       at 6 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0001 c4) ▸ done

  b12 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ K1 ∷ CS14 ∷ CX01 ∷ Sw12 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw12 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw12 ∷ [])
  b12 = at 6 2 (CS14⁻ ∷ Sw12 ∷ []) (sym (wl0018 c4)) ▸
       at 8 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0001 c4) ▸
       at 9 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 9 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 c4)) ▸
       at 10 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 8 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸ done

  b13 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw12 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ Sw34 ∷ Sw34 ∷ CS13⁻ ∷ Sw34 ∷ CX01 ∷ CS04 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ [])
  b13 = at 9 2 (K1 ∷ Sw12 ∷ []) (sym (wl0062 c4)) ▸
       at 10 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 3 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 4 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 6 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0007 c4) ▸
       at 6 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 8 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b14 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ Sw34 ∷ Sw34 ∷ CS13⁻ ∷ Sw34 ∷ CX01 ∷ CS04 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K1 ∷ Sw23 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ [])
  b14 = at 7 2 [] (wl0007 c4) ▸
       at 8 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 10 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (wl0007 c4) ▸
       at 10 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 11 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 5 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸ done

  b15 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K1 ∷ Sw23 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ [])
  b15 = at 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0006 c4) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 9 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0006 c4) ▸
       at 9 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (wl0006 c4) ▸ done

  b16 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (Sw12 ∷ Toff304 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ [])
  b16 = at 11 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 12 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 5 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸
       at 4 3 (Toff103 ∷ []) (by-assoc Eq.refl) ▸
       at 3 3 (Toff104 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (Toff204 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff304 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 c4)) ▸ done

  b17 : Chain (Sw12 ∷ Toff304 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ [])
  b17 = at 1 1 (Sw23 ∷ Toff204 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw12 ∷ Toff104 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw34 ∷ Toff103 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 5 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b18 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ [])
  b18 = at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 7 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 9 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 11 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸ done

  b19 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ [])
  b19 = at 12 2 [] (wl0006 c4) ▸
       at 3 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 6 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 4 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 6 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸ done

  b20 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ K2 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ [])
  b20 = at 10 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 8 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 10 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 11 2 [] (wl0007 c4) ▸
       at 2 2 (K2 ∷ Sw12 ∷ []) (sym (wl0056 c4)) ▸
       at 3 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0008 c4)) ▸
       at 6 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸ done

  b21 : Chain (Sw12 ∷ Sw23 ∷ K2 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ K2 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ [])
  b21 = at 4 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS24⁻ ∷ Sw12 ∷ []) (sym (wl0009 c4)) ▸
       at 8 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 6 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 8 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 c4)) ▸
       at 9 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸ done

  b22 : Chain (Sw12 ∷ Sw23 ∷ K2 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ K3 ∷ CS34 ∷ CX03 ∷ Sw23 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ [])
  b22 = at 7 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K2 ∷ Sw12 ∷ []) (sym (wl0056 c4)) ▸
       at 9 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 10 2 [] (wl0001 c4) ▸
       at 1 2 (K3 ∷ Sw23 ∷ []) (sym (wl0057 c4)) ▸
       at 2 2 (CS34 ∷ Sw23 ∷ []) (sym (wl0011 c4)) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 3 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸ done

  b23 : Chain (Sw12 ∷ K3 ∷ CS34 ∷ CX03 ∷ Sw23 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ K3 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Sw34 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ [])
  b23 = at 4 2 (CS34⁻ ∷ Sw23 ∷ []) (sym (wl0012 c4)) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 5 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (wl0013 c4) ▸
       at 8 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 9 2 (CS01 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸
       at 10 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸ done

  b24 : Chain (Sw12 ∷ K3 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Sw34 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ K3 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw01 ∷ K3 ∷ ι ∷ Sw01 ∷ Sw12 ∷ [])
  b24 = at 11 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (sym (wl0013 c4)) ▸
       at 6 7 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K3 ∷ Sw23 ∷ []) (sym (wl0057 c4)) ▸
       at 8 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 9 2 [] (wl0006 c4) ▸
       at 8 2 (Sw01 ∷ ι ∷ []) (sym (wl0030 c4)) ▸
       at 7 2 (Sw01 ∷ K3 ∷ []) (sym (c₂ (Swap) (K ↑))) ▸
       at 6 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b25 : Chain (Sw12 ∷ K3 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw01 ∷ K3 ∷ ι ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ K3 ∷ Sw01 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3 ∷ ι ∷ Sw01 ∷ Sw12 ∷ [])
  b25 = at 8 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 7 2 (Sw01 ∷ CS13 ∷ []) (wl0019 c4) ▸
       at 6 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 7 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw01 ∷ CX13 ∷ []) (wl0020 c4) ▸
       at 4 2 (Sw01 ∷ CS34⁻ ∷ []) (sym (c₂ (Swap) ((CS • CS • CS) ↑))) ▸
       at 3 2 (Sw01 ∷ CX13 ∷ []) (wl0020 c4) ▸
       at 2 2 (Sw01 ∷ CS34 ∷ []) (sym (c₂ (Swap) (CS ↑))) ▸ done

  b26 : Chain (Sw12 ∷ K3 ∷ Sw01 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3 ∷ ι ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw01 ∷ Sw23 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ Sw23 ∷ Sw23 ∷ CX12 ∷ Sw23 ∷ CS14 ∷ K3 ∷ ι ∷ Sw01 ∷ Sw12 ∷ [])
  b26 = at 1 2 (Sw01 ∷ K3 ∷ []) (sym (c₂ (Swap) (K ↑))) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 3 2 (K2 ∷ Sw23 ∷ []) (sym (wl0058 c4)) ▸
       at 4 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0015 c4)) ▸
       at 6 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0006 c4) ▸
       at 6 2 (CS24⁻ ∷ Sw23 ∷ []) (sym (wl0016 c4)) ▸
       at 8 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b27 : Chain (Sw12 ∷ Sw01 ∷ Sw23 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ Sw23 ∷ Sw23 ∷ CX12 ∷ Sw23 ∷ CS14 ∷ K3 ∷ ι ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw34 ∷ K2 ∷ CS23 ∷ Sw34 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ [])
  b27 = at 7 2 [] (wl0006 c4) ▸
       at 8 2 (CS14 ∷ Sw23 ∷ []) (sym (wl0021 c4)) ▸
       at 9 2 (K2 ∷ Sw23 ∷ []) (sym (wl0058 c4)) ▸
       at 10 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 3 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 4 2 (K2 ∷ Sw34 ∷ []) (sym (c₃ (K ↑ ↑) (Swap))) ▸
       at 6 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0007 c4) ▸ done

  b28 : Chain (Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw34 ∷ K2 ∷ CS23 ∷ Sw34 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw34 ∷ K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι ∷ Sw34 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ [])
  b28 = at 6 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 8 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0007 c4) ▸
       at 8 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 10 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (wl0007 c4) ▸
       at 10 2 (K2 ∷ Sw34 ∷ []) (sym (c₃ (K ↑ ↑) (Swap))) ▸
       at 11 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸ done

  b29 : Chain (Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw34 ∷ K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι ∷ Sw34 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw01 ∷ Toff314 ∷ Sw01 ∷ Sw12 ∷ [])
  b29 = at 4 8 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) (wl0059 c4) ▸
       at 4 8 (Toff213 ∷ []) (by-assoc Eq.refl) ▸
       at 3 3 (Toff214 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (Toff314 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp CX02 at 1: 2 steps
lem-resp-CX02-at-1 : WsL → ⟪ (CX02 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CX12 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CX02-at-1 c4 = run b0
  where
  b0 : Chain (CX02 ∷ []) (Sw01 ∷ CX12 ∷ Sw01 ∷ [])
  b0 = at 1 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 c4)) ▸
       at 0 2 (Sw01 ∷ CX12 ∷ []) (wl0048 c4) ▸ done


-- nat 2 BOX(3;12): 3 steps
lem-nat-2-BOX⟨3·12⟩ : WsL → ⟪ (Sw23 ∷ Bx3-12 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-13 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·12⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx3-12 ∷ []) (Bx2-13 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ12 ∷ []) (refl) ▸
       at 0 2 (CZ13 ∷ Sw23 ∷ []) (lem-nat-2-CZ12 c4) ▸
       at 0 1 (Bx2-13 ∷ []) (refl) ▸ done


-- nat 2 BOX(1;302): 8 steps
lem-nat-2-BOX⟨1·302⟩ : WsL → ⟪ (Sw23 ∷ Bx1-302 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-203 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·302⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx1-302 ∷ []) (Bx1-203 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff103 ∷ Bx3-12 ∷ Toff103 ∷ CCZ013 ∷ Bx3-12 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 1 2 (Toff102 ∷ Sw23 ∷ []) (lem-nat-2-TOFF103 c4) ▸
       at 2 2 (Bx2-13 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·12⟩ c4) ▸
       at 3 2 (Toff102 ∷ Sw23 ∷ []) (lem-nat-2-TOFF103 c4) ▸
       at 4 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 5 2 (Bx2-13 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·12⟩ c4) ▸
       at 0 6 (Bx1-203 ∷ []) (refl) ▸ done


-- nat 2 BOX(3;1402): 8 steps
lem-nat-2-BOX⟨3·1402⟩ : WsL → ⟪ (Sw23 ∷ Bx3-1402 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1403 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·1402⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx3-1402 ∷ []) (Bx2-1403 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff314 ∷ Bx1-302 ∷ Toff314 ∷ CCZ134 ∷ Bx1-302 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 1 2 (Toff214 ∷ Sw23 ∷ []) (lem-nat-2-TOFF314 c4) ▸
       at 2 2 (Bx1-203 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·302⟩ c4) ▸
       at 3 2 (Toff214 ∷ Sw23 ∷ []) (lem-nat-2-TOFF314 c4) ▸
       at 4 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 5 2 (Bx1-203 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·302⟩ c4) ▸
       at 0 6 (Bx2-1403 ∷ []) (refl) ▸ done


-- nat 2 BOX(1;203): 8 steps
lem-nat-2-BOX⟨1·203⟩ : WsL → ⟪ (Sw23 ∷ Bx1-203 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-302 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·203⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx1-203 ∷ []) (Bx1-302 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff102 ∷ Bx2-13 ∷ Toff102 ∷ CCZ012 ∷ Bx2-13 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 1 2 (Toff103 ∷ Sw23 ∷ []) (lem-nat-2-TOFF102 c4) ▸
       at 2 2 (Bx3-12 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·13⟩ c4) ▸
       at 3 2 (Toff103 ∷ Sw23 ∷ []) (lem-nat-2-TOFF102 c4) ▸
       at 4 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 5 2 (Bx3-12 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·13⟩ c4) ▸
       at 0 6 (Bx1-302 ∷ []) (refl) ▸ done


-- nat 2 BOX(2;1403): 8 steps
lem-nat-2-BOX⟨2·1403⟩ : WsL → ⟪ (Sw23 ∷ Bx2-1403 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1402 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·1403⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx2-1403 ∷ []) (Bx3-1402 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff214 ∷ Bx1-203 ∷ Toff214 ∷ CCZ124 ∷ Bx1-203 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 1 2 (Toff314 ∷ Sw23 ∷ []) (lem-nat-2-TOFF214 c4) ▸
       at 2 2 (Bx1-302 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·203⟩ c4) ▸
       at 3 2 (Toff314 ∷ Sw23 ∷ []) (lem-nat-2-TOFF214 c4) ▸
       at 4 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 5 2 (Bx1-302 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·203⟩ c4) ▸
       at 0 6 (Bx3-1402 ∷ []) (refl) ▸ done


-- nat 2 BOX(2;341): 8 steps
lem-nat-2-BOX⟨2·341⟩ : WsL → ⟪ (Sw23 ∷ Bx2-341 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-241 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·341⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx2-341 ∷ []) (Bx3-241 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff234 ∷ Bx3-21 ∷ Toff234 ∷ CCZ234 ∷ Bx3-21 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw23 ∷ []) (sym (wl0086 c4)) ▸
       at 1 2 (Toff324 ∷ Sw23 ∷ []) (wl0127 c4) ▸
       at 2 2 (Bx2-31 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·21⟩ c4) ▸
       at 3 2 (Toff324 ∷ Sw23 ∷ []) (wl0127 c4) ▸
       at 4 2 (CCZ234 ∷ Sw23 ∷ []) (sym (wl0086 c4)) ▸
       at 5 2 (Bx2-31 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·21⟩ c4) ▸
       at 0 6 (Bx3-241 ∷ []) (refl) ▸ done


-- nat 2 BOX(3;2041): 8 steps
lem-nat-2-BOX⟨3·2041⟩ : WsL → ⟪ (Sw23 ∷ Bx3-2041 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3041 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·2041⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx3-2041 ∷ []) (Bx2-3041 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff302 ∷ Bx2-341 ∷ Toff302 ∷ CCZ023 ∷ Bx2-341 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw23 ∷ []) (sym (wl0065 c4)) ▸
       at 1 2 (Toff203 ∷ Sw23 ∷ []) (wl0066 c4) ▸
       at 2 2 (Bx3-241 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·341⟩ c4) ▸
       at 3 2 (Toff203 ∷ Sw23 ∷ []) (wl0066 c4) ▸
       at 4 2 (CCZ023 ∷ Sw23 ∷ []) (sym (wl0065 c4)) ▸
       at 5 2 (Bx3-241 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·341⟩ c4) ▸
       at 0 6 (Bx2-3041 ∷ []) (refl) ▸ done


-- nat 2 BOX(3;241): 8 steps
lem-nat-2-BOX⟨3·241⟩ : WsL → ⟪ (Sw23 ∷ Bx3-241 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-341 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·241⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx3-241 ∷ []) (Bx2-341 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff324 ∷ Bx2-31 ∷ Toff324 ∷ CCZ234 ∷ Bx2-31 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw23 ∷ []) (sym (wl0086 c4)) ▸
       at 1 2 (Toff234 ∷ Sw23 ∷ []) (wl0144 c4) ▸
       at 2 2 (Bx3-21 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·31⟩ c4) ▸
       at 3 2 (Toff234 ∷ Sw23 ∷ []) (wl0144 c4) ▸
       at 4 2 (CCZ234 ∷ Sw23 ∷ []) (sym (wl0086 c4)) ▸
       at 5 2 (Bx3-21 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·31⟩ c4) ▸
       at 0 6 (Bx2-341 ∷ []) (refl) ▸ done


-- nat 2 BOX(2;3041): 8 steps
lem-nat-2-BOX⟨2·3041⟩ : WsL → ⟪ (Sw23 ∷ Bx2-3041 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2041 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·3041⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx2-3041 ∷ []) (Bx3-2041 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff203 ∷ Bx3-241 ∷ Toff203 ∷ CCZ023 ∷ Bx3-241 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw23 ∷ []) (sym (wl0065 c4)) ▸
       at 1 2 (Toff302 ∷ Sw23 ∷ []) (wl0090 c4) ▸
       at 2 2 (Bx2-341 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·241⟩ c4) ▸
       at 3 2 (Toff302 ∷ Sw23 ∷ []) (wl0090 c4) ▸
       at 4 2 (CCZ023 ∷ Sw23 ∷ []) (sym (wl0065 c4)) ▸
       at 5 2 (Bx2-341 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·241⟩ c4) ▸
       at 0 6 (Bx3-2041 ∷ []) (refl) ▸ done


-- nat 3 BOX(4;21): 2 steps
lem-nat-3-BOX⟨4·21⟩ : WsL → ⟪ (Sw34 ∷ Bx4-21 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-21 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨4·21⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx4-21 ∷ []) (Bx3-21 ∷ Sw34 ∷ [])
  b0 = at 0 2 (Bx4-21 ∷ Sw34 ∷ []) (sym (c₃ (CZ ↑) (Swap))) ▸
       at 0 1 (Bx3-21 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 3 BOX(2;431): 8 steps
lem-nat-3-BOX⟨2·431⟩ : WsL → ⟪ (Sw34 ∷ Bx2-431 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-341 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨2·431⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx2-431 ∷ []) (Bx2-341 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff234 ∷ Bx4-21 ∷ Toff234 ∷ CCZ234 ∷ Bx4-21 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw34 ∷ []) (sym (wl0155 c4)) ▸
       at 1 2 (Toff234 ∷ Sw34 ∷ []) (wl0128 c4) ▸
       at 2 2 (Bx3-21 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·21⟩ c4) ▸
       at 3 2 (Toff234 ∷ Sw34 ∷ []) (wl0128 c4) ▸
       at 4 2 (CCZ234 ∷ Sw34 ∷ []) (sym (wl0155 c4)) ▸
       at 5 2 (Bx3-21 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·21⟩ c4) ▸
       at 0 6 (Bx2-341 ∷ []) (refl) ▸ done


-- nat 3 BOX(4;2031): 8 steps
lem-nat-3-BOX⟨4·2031⟩ : WsL → ⟪ (Sw34 ∷ Bx4-2031 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2041 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨4·2031⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx4-2031 ∷ []) (Bx3-2041 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff402 ∷ Bx2-431 ∷ Toff402 ∷ CCZ024 ∷ Bx2-431 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 c4) ▸
       at 1 2 (Toff302 ∷ Sw34 ∷ []) (lem-nat-3-TOFF402 c4) ▸
       at 2 2 (Bx2-341 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·431⟩ c4) ▸
       at 3 2 (Toff302 ∷ Sw34 ∷ []) (lem-nat-3-TOFF402 c4) ▸
       at 4 2 (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 c4) ▸
       at 5 2 (Bx2-341 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·431⟩ c4) ▸
       at 0 6 (Bx3-2041 ∷ []) (refl) ▸ done


-- nat 3 BOX(3;21): 2 steps
lem-nat-3-BOX⟨3·21⟩ : WsL → ⟪ (Sw34 ∷ Bx3-21 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-21 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨3·21⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx3-21 ∷ []) (Bx4-21 ∷ Sw34 ∷ [])
  b0 = at 0 2 (Bx3-21 ∷ Sw34 ∷ []) (sym (c₃ (CZ ↑) (Swap))) ▸
       at 0 1 (Bx4-21 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 3 BOX(2;341): 8 steps
lem-nat-3-BOX⟨2·341⟩ : WsL → ⟪ (Sw34 ∷ Bx2-341 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-431 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨2·341⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx2-341 ∷ []) (Bx2-431 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff234 ∷ Bx3-21 ∷ Toff234 ∷ CCZ234 ∷ Bx3-21 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw34 ∷ []) (sym (wl0155 c4)) ▸
       at 1 2 (Toff234 ∷ Sw34 ∷ []) (wl0128 c4) ▸
       at 2 2 (Bx4-21 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·21⟩ c4) ▸
       at 3 2 (Toff234 ∷ Sw34 ∷ []) (wl0128 c4) ▸
       at 4 2 (CCZ234 ∷ Sw34 ∷ []) (sym (wl0155 c4)) ▸
       at 5 2 (Bx4-21 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·21⟩ c4) ▸
       at 0 6 (Bx2-431 ∷ []) (refl) ▸ done


-- nat 3 BOX(3;2041): 8 steps
lem-nat-3-BOX⟨3·2041⟩ : WsL → ⟪ (Sw34 ∷ Bx3-2041 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2031 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨3·2041⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx3-2041 ∷ []) (Bx4-2031 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff302 ∷ Bx2-341 ∷ Toff302 ∷ CCZ023 ∷ Bx2-341 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw34 ∷ []) (lem-nat-3-CCZ023 c4) ▸
       at 1 2 (Toff402 ∷ Sw34 ∷ []) (lem-nat-3-TOFF302 c4) ▸
       at 2 2 (Bx2-431 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·341⟩ c4) ▸
       at 3 2 (Toff402 ∷ Sw34 ∷ []) (lem-nat-3-TOFF302 c4) ▸
       at 4 2 (CCZ024 ∷ Sw34 ∷ []) (lem-nat-3-CCZ023 c4) ▸
       at 5 2 (Bx2-431 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·341⟩ c4) ▸
       at 0 6 (Bx4-2031 ∷ []) (refl) ▸ done


-- nat 2 SBOX(2;1;3;0): 3 steps
lem-nat-2-SBOX⟨2·1·3·0⟩ : WsL → ⟪ (Sw23 ∷ Sb2-1-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-1-2-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨2·1·3·0⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb2-1-3-0 ∷ []) (Sb3-1-2-0 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS13 ∷ []) (refl) ▸
       at 0 2 (CS12 ∷ Sw23 ∷ []) (lem-nat-2-CS13 c4) ▸
       at 0 1 (Sb3-1-2-0 ∷ []) (refl) ▸ done


-- nat 2 SBOX(3;1;2;0): 3 steps
lem-nat-2-SBOX⟨3·1·2·0⟩ : WsL → ⟪ (Sw23 ∷ Sb3-1-2-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-1-3-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨3·1·2·0⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb3-1-2-0 ∷ []) (Sb2-1-3-0 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS12 ∷ []) (refl) ▸
       at 0 2 (CS13 ∷ Sw23 ∷ []) (lem-nat-2-CS12 c4) ▸
       at 0 1 (Sb2-1-3-0 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(2;1;3;0): 3 steps
lem-nat-2-SBOXd⟨2·1·3·0⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻2-1-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻3-1-2-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨2·1·3·0⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻2-1-3-0 ∷ []) (Sb⁻3-1-2-0 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS13⁻ ∷ []) (refl) ▸
       at 0 2 (CS12⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd13 c4) ▸
       at 0 1 (Sb⁻3-1-2-0 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(3;1;2;0): 3 steps
lem-nat-2-SBOXd⟨3·1·2·0⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻3-1-2-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-1-3-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨3·1·2·0⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻3-1-2-0 ∷ []) (Sb⁻2-1-3-0 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS12⁻ ∷ []) (refl) ▸
       at 0 2 (CS13⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd12 c4) ▸
       at 0 1 (Sb⁻2-1-3-0 ∷ []) (refl) ▸ done


-- resp CX31 at 2: 4 steps
lem-resp-CX31-at-2 : WsL → ⟪ (CX31 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CX32 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CX31-at-2 c4 = run b0
  where
  b0 : Chain (CX31 ∷ []) (Sw12 ∷ Sw01 ∷ CX32 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 0 2 (Sw12 ∷ CX32 ∷ []) (wl0151 c4) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 c4)) ▸
       at 1 2 (Sw01 ∷ CX32 ∷ []) (sym (c₂ (Swap) (CX₁₀))) ▸ done


-- nat 0 SBOX(2;0;43;1): 7 steps
lem-nat-0-SBOX⟨2·0·43·1⟩ : WsL → ⟪ (Sw01 ∷ Sb2-0-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-1-43-0 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨2·0·43·1⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb2-0-43-1 ∷ []) (Sb2-1-43-0 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx2-0431 ∷ Toff134 ∷ Sb2-0-1-3 ∷ Toff134 ∷ Sb⁻2-0-1-3 ∷ []) (refl) ▸
       at 0 2 (Bx2-1430 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·0431⟩ c4) ▸
       at 1 2 (Toff034 ∷ Sw01 ∷ []) (lem-nat-0-TOFF134 c4) ▸
       at 2 2 (Sb2-1-0-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·0·1·3⟩ c4) ▸
       at 3 2 (Toff034 ∷ Sw01 ∷ []) (lem-nat-0-TOFF134 c4) ▸
       at 4 2 (Sb⁻2-1-0-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨2·0·1·3⟩ c4) ▸
       at 0 5 (Sb2-1-43-0 ∷ []) (refl) ▸ done


-- nat 1 SBOX(2;1;0;3): 3 steps
lem-nat-1-SBOX⟨2·1·0·3⟩ : WsL → ⟪ (Sw12 ∷ Sb2-1-0-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-0-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨2·1·0·3⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb2-1-0-3 ∷ []) (Sb1-2-0-3 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS01 ∷ []) (refl) ▸
       at 0 2 (CS02 ∷ Sw12 ∷ []) (lem-nat-1-CS01 c4) ▸
       at 0 1 (Sb1-2-0-3 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(2;1;0;3): 3 steps
lem-nat-1-SBOXd⟨2·1·0·3⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻2-1-0-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-2-0-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨2·1·0·3⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻2-1-0-3 ∷ []) (Sb⁻1-2-0-3 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS01⁻ ∷ []) (refl) ▸
       at 0 2 (CS02⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd01 c4) ▸
       at 0 1 (Sb⁻1-2-0-3 ∷ []) (refl) ▸ done


-- nat 1 SBOX(2;1;43;0): 7 steps
lem-nat-1-SBOX⟨2·1·43·0⟩ : WsL → ⟪ (Sw12 ∷ Sb2-1-43-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-43-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨2·1·43·0⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb2-1-43-0 ∷ []) (Sb1-2-43-0 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx2-1430 ∷ Toff034 ∷ Sb2-1-0-3 ∷ Toff034 ∷ Sb⁻2-1-0-3 ∷ []) (refl) ▸
       at 0 2 (Bx1-2430 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·1430⟩ c4) ▸
       at 1 2 (Toff034 ∷ Sw12 ∷ []) (lem-nat-1-TOFF034 c4) ▸
       at 2 2 (Sb1-2-0-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·1·0·3⟩ c4) ▸
       at 3 2 (Toff034 ∷ Sw12 ∷ []) (lem-nat-1-TOFF034 c4) ▸
       at 4 2 (Sb⁻1-2-0-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·1·0·3⟩ c4) ▸
       at 0 5 (Sb1-2-43-0 ∷ []) (refl) ▸ done


-- nat 2 BOX(2;10): 2 steps
lem-nat-2-BOX⟨2·10⟩ : WsL → ⟪ (Sw23 ∷ Bx2-10 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-10 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·10⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx2-10 ∷ []) (Bx3-10 ∷ Sw23 ∷ [])
  b0 = at 0 2 (Bx2-10 ∷ Sw23 ∷ []) (sym (c₂ (CZ) (Swap))) ▸
       at 0 1 (Bx3-10 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 2 BOX(1;230): 8 steps
lem-nat-2-BOX⟨1·230⟩ : WsL → ⟪ (Sw23 ∷ Bx1-230 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-320 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·230⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx1-230 ∷ []) (Bx1-320 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff123 ∷ Bx2-10 ∷ Toff123 ∷ CCZ123 ∷ Bx2-10 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw23 ∷ []) (sym (wl0113 c4)) ▸
       at 1 2 (Toff123 ∷ Sw23 ∷ []) (wl0114 c4) ▸
       at 2 2 (Bx3-10 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·10⟩ c4) ▸
       at 3 2 (Toff123 ∷ Sw23 ∷ []) (wl0114 c4) ▸
       at 4 2 (CCZ123 ∷ Sw23 ∷ []) (sym (wl0113 c4)) ▸
       at 5 2 (Bx3-10 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·10⟩ c4) ▸
       at 0 6 (Bx1-320 ∷ []) (refl) ▸ done


-- nat 2 BOX(2;1430): 8 steps
lem-nat-2-BOX⟨2·1430⟩ : WsL → ⟪ (Sw23 ∷ Bx2-1430 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1420 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·1430⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx2-1430 ∷ []) (Bx3-1420 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff214 ∷ Bx1-230 ∷ Toff214 ∷ CCZ124 ∷ Bx1-230 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 1 2 (Toff314 ∷ Sw23 ∷ []) (lem-nat-2-TOFF214 c4) ▸
       at 2 2 (Bx1-320 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·230⟩ c4) ▸
       at 3 2 (Toff314 ∷ Sw23 ∷ []) (lem-nat-2-TOFF214 c4) ▸
       at 4 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 5 2 (Bx1-320 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·230⟩ c4) ▸
       at 0 6 (Bx3-1420 ∷ []) (refl) ▸ done


-- nat 2 SBOX(2;1;0;3): 2 steps
lem-nat-2-SBOX⟨2·1·0·3⟩ : WsL → ⟪ (Sw23 ∷ Sb2-1-0-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-1-0-2 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨2·1·0·3⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb2-1-0-3 ∷ []) (Sb3-1-0-2 ∷ Sw23 ∷ [])
  b0 = at 0 2 (Sb2-1-0-3 ∷ Sw23 ∷ []) (sym (c₂ (CS) (Swap))) ▸
       at 0 1 (Sb3-1-0-2 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 2 SBOXd(2;1;0;3): 2 steps
lem-nat-2-SBOXd⟨2·1·0·3⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻2-1-0-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻3-1-0-2 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨2·1·0·3⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻2-1-0-3 ∷ []) (Sb⁻3-1-0-2 ∷ Sw23 ∷ [])
  b0 = at 0 2 (Sb⁻2-1-0-3 ∷ Sw23 ∷ []) (sym (c₂ (CS • CS • CS) (Swap))) ▸
       at 0 1 (Sb⁻3-1-0-2 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 2 SBOX(2;1;43;0): 7 steps
lem-nat-2-SBOX⟨2·1·43·0⟩ : WsL → ⟪ (Sw23 ∷ Sb2-1-43-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-1-42-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨2·1·43·0⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb2-1-43-0 ∷ []) (Sb3-1-42-0 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx2-1430 ∷ Toff034 ∷ Sb2-1-0-3 ∷ Toff034 ∷ Sb⁻2-1-0-3 ∷ []) (refl) ▸
       at 0 2 (Bx3-1420 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·1430⟩ c4) ▸
       at 1 2 (Toff024 ∷ Sw23 ∷ []) (lem-nat-2-TOFF034 c4) ▸
       at 2 2 (Sb3-1-0-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨2·1·0·3⟩ c4) ▸
       at 3 2 (Toff024 ∷ Sw23 ∷ []) (lem-nat-2-TOFF034 c4) ▸
       at 4 2 (Sb⁻3-1-0-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨2·1·0·3⟩ c4) ▸
       at 0 5 (Sb3-1-42-0 ∷ []) (refl) ▸ done


-- nat 2 BOX(3;10): 2 steps
lem-nat-2-BOX⟨3·10⟩ : WsL → ⟪ (Sw23 ∷ Bx3-10 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-10 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·10⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx3-10 ∷ []) (Bx2-10 ∷ Sw23 ∷ [])
  b0 = at 0 2 (Bx3-10 ∷ Sw23 ∷ []) (sym (c₂ (CZ) (Swap))) ▸
       at 0 1 (Bx2-10 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 2 BOX(1;320): 8 steps
lem-nat-2-BOX⟨1·320⟩ : WsL → ⟪ (Sw23 ∷ Bx1-320 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-230 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·320⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx1-320 ∷ []) (Bx1-230 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff123 ∷ Bx3-10 ∷ Toff123 ∷ CCZ123 ∷ Bx3-10 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw23 ∷ []) (sym (wl0113 c4)) ▸
       at 1 2 (Toff123 ∷ Sw23 ∷ []) (wl0114 c4) ▸
       at 2 2 (Bx2-10 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·10⟩ c4) ▸
       at 3 2 (Toff123 ∷ Sw23 ∷ []) (wl0114 c4) ▸
       at 4 2 (CCZ123 ∷ Sw23 ∷ []) (sym (wl0113 c4)) ▸
       at 5 2 (Bx2-10 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·10⟩ c4) ▸
       at 0 6 (Bx1-230 ∷ []) (refl) ▸ done


-- nat 2 BOX(3;1420): 8 steps
lem-nat-2-BOX⟨3·1420⟩ : WsL → ⟪ (Sw23 ∷ Bx3-1420 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1430 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·1420⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx3-1420 ∷ []) (Bx2-1430 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff314 ∷ Bx1-320 ∷ Toff314 ∷ CCZ134 ∷ Bx1-320 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 1 2 (Toff214 ∷ Sw23 ∷ []) (lem-nat-2-TOFF314 c4) ▸
       at 2 2 (Bx1-230 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·320⟩ c4) ▸
       at 3 2 (Toff214 ∷ Sw23 ∷ []) (lem-nat-2-TOFF314 c4) ▸
       at 4 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 5 2 (Bx1-230 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·320⟩ c4) ▸
       at 0 6 (Bx2-1430 ∷ []) (refl) ▸ done


-- nat 2 SBOX(3;1;0;2): 2 steps
lem-nat-2-SBOX⟨3·1·0·2⟩ : WsL → ⟪ (Sw23 ∷ Sb3-1-0-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-1-0-3 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨3·1·0·2⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb3-1-0-2 ∷ []) (Sb2-1-0-3 ∷ Sw23 ∷ [])
  b0 = at 0 2 (Sb3-1-0-2 ∷ Sw23 ∷ []) (sym (c₂ (CS) (Swap))) ▸
       at 0 1 (Sb2-1-0-3 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 2 SBOXd(3;1;0;2): 2 steps
lem-nat-2-SBOXd⟨3·1·0·2⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻3-1-0-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-1-0-3 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨3·1·0·2⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻3-1-0-2 ∷ []) (Sb⁻2-1-0-3 ∷ Sw23 ∷ [])
  b0 = at 0 2 (Sb⁻3-1-0-2 ∷ Sw23 ∷ []) (sym (c₂ (CS • CS • CS) (Swap))) ▸
       at 0 1 (Sb⁻2-1-0-3 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 2 SBOX(3;1;42;0): 7 steps
lem-nat-2-SBOX⟨3·1·42·0⟩ : WsL → ⟪ (Sw23 ∷ Sb3-1-42-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-1-43-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨3·1·42·0⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb3-1-42-0 ∷ []) (Sb2-1-43-0 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx3-1420 ∷ Toff024 ∷ Sb3-1-0-2 ∷ Toff024 ∷ Sb⁻3-1-0-2 ∷ []) (refl) ▸
       at 0 2 (Bx2-1430 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·1420⟩ c4) ▸
       at 1 2 (Toff034 ∷ Sw23 ∷ []) (lem-nat-2-TOFF024 c4) ▸
       at 2 2 (Sb2-1-0-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·1·0·2⟩ c4) ▸
       at 3 2 (Toff034 ∷ Sw23 ∷ []) (lem-nat-2-TOFF024 c4) ▸
       at 4 2 (Sb⁻2-1-0-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨3·1·0·2⟩ c4) ▸
       at 0 5 (Sb2-1-43-0 ∷ []) (refl) ▸ done


-- nat 0 BOX(2;403): 8 steps
lem-nat-0-BOX⟨2·403⟩ : WsL → ⟪ (Sw01 ∷ Bx2-403 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-413 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·403⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx2-403 ∷ []) (Bx2-413 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff204 ∷ Bx4-23 ∷ Toff204 ∷ CCZ024 ∷ Bx4-23 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 1 2 (Toff214 ∷ Sw01 ∷ []) (lem-nat-0-TOFF204 c4) ▸
       at 2 2 (Bx4-23 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ)) ▸
       at 3 2 (Toff214 ∷ Sw01 ∷ []) (lem-nat-0-TOFF204 c4) ▸
       at 4 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 5 2 (Bx4-23 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ)) ▸
       at 0 6 (Bx2-413 ∷ []) (refl) ▸ done


-- nat 0 BOX(4;2103): 8 steps
lem-nat-0-BOX⟨4·2103⟩ : WsL → ⟪ (Sw01 ∷ Bx4-2103 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2013 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·2103⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx4-2103 ∷ []) (Bx4-2013 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff412 ∷ Bx2-403 ∷ Toff412 ∷ CCZ124 ∷ Bx2-403 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 1 2 (Toff402 ∷ Sw01 ∷ []) (lem-nat-0-TOFF412 c4) ▸
       at 2 2 (Bx2-413 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·403⟩ c4) ▸
       at 3 2 (Toff402 ∷ Sw01 ∷ []) (lem-nat-0-TOFF412 c4) ▸
       at 4 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 5 2 (Bx2-413 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·403⟩ c4) ▸
       at 0 6 (Bx4-2013 ∷ []) (refl) ▸ done


-- nat 3 BOX(4;02): 2 steps
lem-nat-3-BOX⟨4·02⟩ : WsL → ⟪ (Sw34 ∷ Bx4-02 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-02 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨4·02⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx4-02 ∷ []) (Bx3-02 ∷ Sw34 ∷ [])
  b0 = at 0 2 (Bx4-02 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑ • CZ • Swap ↑) (Swap))) ▸
       at 0 1 (Bx3-02 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 3 BOX(0;412): 8 steps
lem-nat-3-BOX⟨0·412⟩ : WsL → ⟪ (Sw34 ∷ Bx0-412 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-312 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·412⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx0-412 ∷ []) (Bx0-312 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff014 ∷ Bx4-02 ∷ Toff014 ∷ CCZ014 ∷ Bx4-02 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4) ▸
       at 1 2 (Toff013 ∷ Sw34 ∷ []) (lem-nat-3-TOFF014 c4) ▸
       at 2 2 (Bx3-02 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·02⟩ c4) ▸
       at 3 2 (Toff013 ∷ Sw34 ∷ []) (lem-nat-3-TOFF014 c4) ▸
       at 4 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4) ▸
       at 5 2 (Bx3-02 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·02⟩ c4) ▸
       at 0 6 (Bx0-312 ∷ []) (refl) ▸ done


-- nat 3 BOX(4;0312): 8 steps
lem-nat-3-BOX⟨4·0312⟩ : WsL → ⟪ (Sw34 ∷ Bx4-0312 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨4·0312⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx4-0312 ∷ []) (Bx3-0412 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff403 ∷ Bx0-412 ∷ Toff403 ∷ CCZ034 ∷ Bx0-412 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw34 ∷ []) (lem-nat-3-CCZ034 c4) ▸
       at 1 2 (Toff304 ∷ Sw34 ∷ []) (lem-nat-3-TOFF403 c4) ▸
       at 2 2 (Bx0-312 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·412⟩ c4) ▸
       at 3 2 (Toff304 ∷ Sw34 ∷ []) (lem-nat-3-TOFF403 c4) ▸
       at 4 2 (CCZ034 ∷ Sw34 ∷ []) (lem-nat-3-CCZ034 c4) ▸
       at 5 2 (Bx0-312 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·412⟩ c4) ▸
       at 0 6 (Bx3-0412 ∷ []) (refl) ▸ done


-- nat 2 SBOX(4;0;3;1): 3 steps
lem-nat-2-SBOX⟨4·0·3·1⟩ : WsL → ⟪ (Sw23 ∷ Sb4-0-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-0-2-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨4·0·3·1⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb4-0-3-1 ∷ []) (Sb4-0-2-1 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS03 ∷ []) (refl) ▸
       at 0 2 (CS02 ∷ Sw23 ∷ []) (lem-nat-2-CS03 c4) ▸
       at 0 1 (Sb4-0-2-1 ∷ []) (refl) ▸ done


-- nat 3 SBOX(4;0;2;1): 2 steps
lem-nat-3-SBOX⟨4·0·2·1⟩ : WsL → ⟪ (Sw34 ∷ Sb4-0-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-2-1 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨4·0·2·1⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb4-0-2-1 ∷ []) (Sb3-0-2-1 ∷ Sw34 ∷ [])
  b0 = at 0 2 (Sb4-0-2-1 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑ • CS • Swap ↑) (Swap))) ▸
       at 0 1 (Sb3-0-2-1 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 3 SBOXd(4;0;2;1): 2 steps
lem-nat-3-SBOXd⟨4·0·2·1⟩ : WsL → ⟪ (Sw34 ∷ Sb⁻4-0-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻3-0-2-1 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨4·0·2·1⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb⁻4-0-2-1 ∷ []) (Sb⁻3-0-2-1 ∷ Sw34 ∷ [])
  b0 = at 0 2 (Sb⁻4-0-2-1 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑ • (CS • CS • CS) • Swap ↑) (Swap))) ▸
       at 0 1 (Sb⁻3-0-2-1 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm SBOXd(0;1;2;3) TOFF034: 17 steps
lem-comm-SBOXd⟨0·1·2·3⟩-TOFF034 : WsL → ⟪ (Sb⁻0-1-2-3 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ Sb⁻0-1-2-3 ∷ []) ⟫ʷ
lem-comm-SBOXd⟨0·1·2·3⟩-TOFF034 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sb⁻0-1-2-3 ∷ Toff034 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CS34⁻ ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 0 1 (CS12⁻ ∷ []) (refl) ▸
       at 1 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 1 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw12 ∷ CS23⁻ ∷ []) (wl0043 c4) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 3 3 (CS24⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw23 ∷ CS34⁻ ∷ []) (wl0016 c4) ▸ done

  b1 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CS34⁻ ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (Toff034 ∷ CS12⁻ ∷ [])
  b1 = at 4 2 (Toff012 ∷ CS34⁻ ∷ []) (sym (c₃ (Toff) (CS • CS • CS))) ▸
       at 5 2 (Sw23 ∷ CS24⁻ ∷ []) (wl0012 c4) ▸
       at 6 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0007 c4) ▸
       at 7 2 (Sw12 ∷ CS13⁻ ∷ []) (wl0046 c4) ▸
       at 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (wl0006 c4) ▸
       at 0 9 (Toff034 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (Toff034 ∷ CS12⁻ ∷ []) (Toff034 ∷ Sb⁻0-1-2-3 ∷ [])
  b2 = at 1 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸ done


-- comm SBOX(0;1;2;3) TOFF034: 17 steps
lem-comm-SBOX⟨0·1·2·3⟩-TOFF034 : WsL → ⟪ (Sb0-1-2-3 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ Sb0-1-2-3 ∷ []) ⟫ʷ
lem-comm-SBOX⟨0·1·2·3⟩-TOFF034 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sb0-1-2-3 ∷ Toff034 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CS34 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 0 1 (CS12 ∷ []) (refl) ▸
       at 1 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 1 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw12 ∷ CS23 ∷ []) (wl0024 c4) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 3 3 (CS24 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw23 ∷ CS34 ∷ []) (wl0015 c4) ▸ done

  b1 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CS34 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (Toff034 ∷ CS12 ∷ [])
  b1 = at 4 2 (Toff012 ∷ CS34 ∷ []) (sym (c₃ (Toff) (CS))) ▸
       at 5 2 (Sw23 ∷ CS24 ∷ []) (wl0011 c4) ▸
       at 6 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0007 c4) ▸
       at 7 2 (Sw12 ∷ CS13 ∷ []) (wl0025 c4) ▸
       at 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (wl0006 c4) ▸
       at 0 9 (Toff034 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (Toff034 ∷ CS12 ∷ []) (Toff034 ∷ Sb0-1-2-3 ∷ [])
  b2 = at 1 1 (Sb0-1-2-3 ∷ []) (refl) ▸ done


-- nat 2 BOX(2;041): 8 steps
lem-nat-2-BOX⟨2·041⟩ : WsL → ⟪ (Sw23 ∷ Bx2-041 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-041 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·041⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx2-041 ∷ []) (Bx3-041 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff204 ∷ Bx0-21 ∷ Toff204 ∷ CCZ024 ∷ Bx0-21 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 1 2 (Toff304 ∷ Sw23 ∷ []) (lem-nat-2-TOFF204 c4) ▸
       at 2 2 (Bx0-31 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·21⟩ c4) ▸
       at 3 2 (Toff304 ∷ Sw23 ∷ []) (lem-nat-2-TOFF204 c4) ▸
       at 4 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 5 2 (Bx0-31 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·21⟩ c4) ▸
       at 0 6 (Bx3-041 ∷ []) (refl) ▸ done


-- nat 2 BOX(0;2341): 8 steps
lem-nat-2-BOX⟨0·2341⟩ : WsL → ⟪ (Sw23 ∷ Bx0-2341 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3241 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·2341⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-2341 ∷ []) (Bx0-3241 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff023 ∷ Bx2-041 ∷ Toff023 ∷ CCZ023 ∷ Bx2-041 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw23 ∷ []) (sym (wl0065 c4)) ▸
       at 1 2 (Toff023 ∷ Sw23 ∷ []) (wl0093 c4) ▸
       at 2 2 (Bx3-041 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·041⟩ c4) ▸
       at 3 2 (Toff023 ∷ Sw23 ∷ []) (wl0093 c4) ▸
       at 4 2 (CCZ023 ∷ Sw23 ∷ []) (sym (wl0065 c4)) ▸
       at 5 2 (Bx3-041 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·041⟩ c4) ▸
       at 0 6 (Bx0-3241 ∷ []) (refl) ▸ done


-- nat 1 SBOX(3;2;1;0): 3 steps
lem-nat-1-SBOX⟨3·2·1·0⟩ : WsL → ⟪ (Sw12 ∷ Sb3-2-1-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-1-2-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨3·2·1·0⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb3-2-1-0 ∷ []) (Sb3-1-2-0 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS12 ∷ []) (refl) ▸
       at 0 2 (CS12 ∷ Sw12 ∷ []) (sym (wl0134 c4)) ▸
       at 0 1 (Sb3-1-2-0 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(3;2;1;0): 3 steps
lem-nat-1-SBOXd⟨3·2·1·0⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻3-2-1-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻3-1-2-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨3·2·1·0⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻3-2-1-0 ∷ []) (Sb⁻3-1-2-0 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS12⁻ ∷ []) (refl) ▸
       at 0 2 (CS12⁻ ∷ Sw12 ∷ []) (sym (wl0135 c4)) ▸
       at 0 1 (Sb⁻3-1-2-0 ∷ []) (refl) ▸ done


-- nat 1 SBOX(3;2;40;1): 7 steps
lem-nat-1-SBOX⟨3·2·40·1⟩ : WsL → ⟪ (Sw12 ∷ Sb3-2-40-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-1-40-2 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨3·2·40·1⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb3-2-40-1 ∷ []) (Sb3-1-40-2 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx3-2401 ∷ Toff104 ∷ Sb3-2-1-0 ∷ Toff104 ∷ Sb⁻3-2-1-0 ∷ []) (refl) ▸
       at 0 2 (Bx3-1402 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·2401⟩ c4) ▸
       at 1 2 (Toff204 ∷ Sw12 ∷ []) (lem-nat-1-TOFF104 c4) ▸
       at 2 2 (Sb3-1-2-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·2·1·0⟩ c4) ▸
       at 3 2 (Toff204 ∷ Sw12 ∷ []) (lem-nat-1-TOFF104 c4) ▸
       at 4 2 (Sb⁻3-1-2-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨3·2·1·0⟩ c4) ▸
       at 0 5 (Sb3-1-40-2 ∷ []) (refl) ▸ done


-- nat 2 SBOX(2;1;40;3): 7 steps
lem-nat-2-SBOX⟨2·1·40·3⟩ : WsL → ⟪ (Sw23 ∷ Sb2-1-40-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-1-40-2 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨2·1·40·3⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb2-1-40-3 ∷ []) (Sb3-1-40-2 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx2-1403 ∷ Toff304 ∷ Sb2-1-3-0 ∷ Toff304 ∷ Sb⁻2-1-3-0 ∷ []) (refl) ▸
       at 0 2 (Bx3-1402 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·1403⟩ c4) ▸
       at 1 2 (Toff204 ∷ Sw23 ∷ []) (lem-nat-2-TOFF304 c4) ▸
       at 2 2 (Sb3-1-2-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨2·1·3·0⟩ c4) ▸
       at 3 2 (Toff204 ∷ Sw23 ∷ []) (lem-nat-2-TOFF304 c4) ▸
       at 4 2 (Sb⁻3-1-2-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨2·1·3·0⟩ c4) ▸
       at 0 5 (Sb3-1-40-2 ∷ []) (refl) ▸ done


-- nat 2 SBOX(3;1;40;2): 7 steps
lem-nat-2-SBOX⟨3·1·40·2⟩ : WsL → ⟪ (Sw23 ∷ Sb3-1-40-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-1-40-3 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨3·1·40·2⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb3-1-40-2 ∷ []) (Sb2-1-40-3 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx3-1402 ∷ Toff204 ∷ Sb3-1-2-0 ∷ Toff204 ∷ Sb⁻3-1-2-0 ∷ []) (refl) ▸
       at 0 2 (Bx2-1403 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·1402⟩ c4) ▸
       at 1 2 (Toff304 ∷ Sw23 ∷ []) (lem-nat-2-TOFF204 c4) ▸
       at 2 2 (Sb2-1-3-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·1·2·0⟩ c4) ▸
       at 3 2 (Toff304 ∷ Sw23 ∷ []) (lem-nat-2-TOFF204 c4) ▸
       at 4 2 (Sb⁻2-1-3-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨3·1·2·0⟩ c4) ▸
       at 0 5 (Sb2-1-40-3 ∷ []) (refl) ▸ done


-- nat 2 SBOX(0;2;1;4): 3 steps
lem-nat-2-SBOX⟨0·2·1·4⟩ : WsL → ⟪ (Sw23 ∷ Sb0-2-1-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-3-1-4 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨0·2·1·4⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb0-2-1-4 ∷ []) (Sb0-3-1-4 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS12 ∷ []) (refl) ▸
       at 0 2 (CS13 ∷ Sw23 ∷ []) (lem-nat-2-CS12 c4) ▸
       at 0 1 (Sb0-3-1-4 ∷ []) (refl) ▸ done


-- nat 3 SBOX(0;2;1;3): 2 steps
lem-nat-3-SBOX⟨0·2·1·3⟩ : WsL → ⟪ (Sw34 ∷ Sb0-2-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-1-4 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨0·2·1·3⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb0-2-1-3 ∷ []) (Sb0-2-1-4 ∷ Sw34 ∷ [])
  b0 = at 0 2 (Sb0-2-1-3 ∷ Sw34 ∷ []) (sym (c₃ (CS ↑) (Swap))) ▸
       at 0 1 (Sb0-2-1-4 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 3 SBOX(0;2;1;4): 2 steps
lem-nat-3-SBOX⟨0·2·1·4⟩ : WsL → ⟪ (Sw34 ∷ Sb0-2-1-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-1-3 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨0·2·1·4⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb0-2-1-4 ∷ []) (Sb0-2-1-3 ∷ Sw34 ∷ [])
  b0 = at 0 2 (Sb0-2-1-4 ∷ Sw34 ∷ []) (sym (c₃ (CS ↑) (Swap))) ▸
       at 0 1 (Sb0-2-1-3 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 2 SBOXd(0;2;1;4): 3 steps
lem-nat-2-SBOXd⟨0·2·1·4⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻0-2-1-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-3-1-4 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨0·2·1·4⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻0-2-1-4 ∷ []) (Sb⁻0-3-1-4 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS12⁻ ∷ []) (refl) ▸
       at 0 2 (CS13⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd12 c4) ▸
       at 0 1 (Sb⁻0-3-1-4 ∷ []) (refl) ▸ done


-- nat 3 SBOXd(0;2;1;3): 2 steps
lem-nat-3-SBOXd⟨0·2·1·3⟩ : WsL → ⟪ (Sw34 ∷ Sb⁻0-2-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-2-1-4 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨0·2·1·3⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb⁻0-2-1-3 ∷ []) (Sb⁻0-2-1-4 ∷ Sw34 ∷ [])
  b0 = at 0 2 (Sb⁻0-2-1-3 ∷ Sw34 ∷ []) (sym (c₃ ((CS • CS • CS) ↑) (Swap))) ▸
       at 0 1 (Sb⁻0-2-1-4 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 3 SBOXd(0;2;1;4): 2 steps
lem-nat-3-SBOXd⟨0·2·1·4⟩ : WsL → ⟪ (Sw34 ∷ Sb⁻0-2-1-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-2-1-3 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨0·2·1·4⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb⁻0-2-1-4 ∷ []) (Sb⁻0-2-1-3 ∷ Sw34 ∷ [])
  b0 = at 0 2 (Sb⁻0-2-1-4 ∷ Sw34 ∷ []) (sym (c₃ ((CS • CS • CS) ↑) (Swap))) ▸
       at 0 1 (Sb⁻0-2-1-3 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp CX30 at 1: 2 steps
lem-resp-CX30-at-1 : WsL → ⟪ (CX30 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CX31 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CX30-at-1 c4 = run b0
  where
  b0 : Chain (CX30 ∷ []) (Sw01 ∷ CX31 ∷ Sw01 ∷ [])
  b0 = at 1 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 c4)) ▸
       at 0 2 (Sw01 ∷ CX31 ∷ []) (wl0122 c4) ▸ done


-- nat 3 BOX(0;42): 3 steps
lem-nat-3-BOX⟨0·42⟩ : WsL → ⟪ (Sw34 ∷ Bx0-42 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-32 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·42⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx0-42 ∷ []) (Bx0-32 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CZ24 ∷ []) (refl) ▸
       at 0 2 (CZ23 ∷ Sw34 ∷ []) (lem-nat-3-CZ24 c4) ▸
       at 0 1 (Bx0-32 ∷ []) (refl) ▸ done


-- nat 3 BOX(4;012): 8 steps
lem-nat-3-BOX⟨4·012⟩ : WsL → ⟪ (Sw34 ∷ Bx4-012 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-012 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨4·012⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx4-012 ∷ []) (Bx3-012 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff401 ∷ Bx0-42 ∷ Toff401 ∷ CCZ014 ∷ Bx0-42 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4) ▸
       at 1 2 (Toff301 ∷ Sw34 ∷ []) (lem-nat-3-TOFF401 c4) ▸
       at 2 2 (Bx0-32 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·42⟩ c4) ▸
       at 3 2 (Toff301 ∷ Sw34 ∷ []) (lem-nat-3-TOFF401 c4) ▸
       at 4 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4) ▸
       at 5 2 (Bx0-32 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·42⟩ c4) ▸
       at 0 6 (Bx3-012 ∷ []) (refl) ▸ done


-- nat 3 BOX(0;4312): 8 steps
lem-nat-3-BOX⟨0·4312⟩ : WsL → ⟪ (Sw34 ∷ Bx0-4312 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3412 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·4312⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx0-4312 ∷ []) (Bx0-3412 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff034 ∷ Bx4-012 ∷ Toff034 ∷ CCZ034 ∷ Bx4-012 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw34 ∷ []) (lem-nat-3-CCZ034 c4) ▸
       at 1 2 (Toff034 ∷ Sw34 ∷ []) (lem-nat-3-TOFF034 c4) ▸
       at 2 2 (Bx3-012 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·012⟩ c4) ▸
       at 3 2 (Toff034 ∷ Sw34 ∷ []) (lem-nat-3-TOFF034 c4) ▸
       at 4 2 (CCZ034 ∷ Sw34 ∷ []) (lem-nat-3-CCZ034 c4) ▸
       at 5 2 (Bx3-012 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·012⟩ c4) ▸
       at 0 6 (Bx0-3412 ∷ []) (refl) ▸ done


-- nat 3 BOX(3;012): 8 steps
lem-nat-3-BOX⟨3·012⟩ : WsL → ⟪ (Sw34 ∷ Bx3-012 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-012 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨3·012⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx3-012 ∷ []) (Bx4-012 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff301 ∷ Bx0-32 ∷ Toff301 ∷ CCZ013 ∷ Bx0-32 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4) ▸
       at 1 2 (Toff401 ∷ Sw34 ∷ []) (lem-nat-3-TOFF301 c4) ▸
       at 2 2 (Bx0-42 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·32⟩ c4) ▸
       at 3 2 (Toff401 ∷ Sw34 ∷ []) (lem-nat-3-TOFF301 c4) ▸
       at 4 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4) ▸
       at 5 2 (Bx0-42 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·32⟩ c4) ▸
       at 0 6 (Bx4-012 ∷ []) (refl) ▸ done


-- nat 3 BOX(0;3412): 8 steps
lem-nat-3-BOX⟨0·3412⟩ : WsL → ⟪ (Sw34 ∷ Bx0-3412 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4312 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·3412⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx0-3412 ∷ []) (Bx0-4312 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff034 ∷ Bx3-012 ∷ Toff034 ∷ CCZ034 ∷ Bx3-012 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw34 ∷ []) (lem-nat-3-CCZ034 c4) ▸
       at 1 2 (Toff034 ∷ Sw34 ∷ []) (lem-nat-3-TOFF034 c4) ▸
       at 2 2 (Bx4-012 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·012⟩ c4) ▸
       at 3 2 (Toff034 ∷ Sw34 ∷ []) (lem-nat-3-TOFF034 c4) ▸
       at 4 2 (CCZ034 ∷ Sw34 ∷ []) (lem-nat-3-CCZ034 c4) ▸
       at 5 2 (Bx4-012 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·012⟩ c4) ▸
       at 0 6 (Bx0-4312 ∷ []) (refl) ▸ done


-- nat 0 BOX(0;341): 8 steps
lem-nat-0-BOX⟨0·341⟩ : WsL → ⟪ (Sw01 ∷ Bx0-341 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-340 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·341⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-341 ∷ []) (Bx1-340 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff034 ∷ Bx3-01 ∷ Toff034 ∷ CCZ034 ∷ Bx3-01 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4) ▸
       at 1 2 (Toff134 ∷ Sw01 ∷ []) (lem-nat-0-TOFF034 c4) ▸
       at 2 2 (Bx3-10 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·01⟩ c4) ▸
       at 3 2 (Toff134 ∷ Sw01 ∷ []) (lem-nat-0-TOFF034 c4) ▸
       at 4 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4) ▸
       at 5 2 (Bx3-10 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·01⟩ c4) ▸
       at 0 6 (Bx1-340 ∷ []) (refl) ▸ done


-- nat 0 BOX(3;0241): 8 steps
lem-nat-0-BOX⟨3·0241⟩ : WsL → ⟪ (Sw01 ∷ Bx3-0241 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1240 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·0241⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx3-0241 ∷ []) (Bx3-1240 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff302 ∷ Bx0-341 ∷ Toff302 ∷ CCZ023 ∷ Bx0-341 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw01 ∷ []) (sym (wl0103 c4)) ▸
       at 1 2 (Toff312 ∷ Sw01 ∷ []) (wl0116 c4) ▸
       at 2 2 (Bx1-340 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·341⟩ c4) ▸
       at 3 2 (Toff312 ∷ Sw01 ∷ []) (wl0116 c4) ▸
       at 4 2 (CCZ123 ∷ Sw01 ∷ []) (sym (wl0103 c4)) ▸
       at 5 2 (Bx1-340 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·341⟩ c4) ▸
       at 0 6 (Bx3-1240 ∷ []) (refl) ▸ done


-- nat 0 BOX(1;340): 8 steps
lem-nat-0-BOX⟨1·340⟩ : WsL → ⟪ (Sw01 ∷ Bx1-340 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-341 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·340⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-340 ∷ []) (Bx0-341 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff134 ∷ Bx3-10 ∷ Toff134 ∷ CCZ134 ∷ Bx3-10 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 1 2 (Toff034 ∷ Sw01 ∷ []) (lem-nat-0-TOFF134 c4) ▸
       at 2 2 (Bx3-01 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·10⟩ c4) ▸
       at 3 2 (Toff034 ∷ Sw01 ∷ []) (lem-nat-0-TOFF134 c4) ▸
       at 4 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 5 2 (Bx3-01 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·10⟩ c4) ▸
       at 0 6 (Bx0-341 ∷ []) (refl) ▸ done


-- nat 0 BOX(3;1240): 8 steps
lem-nat-0-BOX⟨3·1240⟩ : WsL → ⟪ (Sw01 ∷ Bx3-1240 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0241 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·1240⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx3-1240 ∷ []) (Bx3-0241 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff312 ∷ Bx1-340 ∷ Toff312 ∷ CCZ123 ∷ Bx1-340 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw01 ∷ []) (sym (wl0003 c4)) ▸
       at 1 2 (Toff302 ∷ Sw01 ∷ []) (wl0110 c4) ▸
       at 2 2 (Bx0-341 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·340⟩ c4) ▸
       at 3 2 (Toff302 ∷ Sw01 ∷ []) (wl0110 c4) ▸
       at 4 2 (CCZ023 ∷ Sw01 ∷ []) (sym (wl0003 c4)) ▸
       at 5 2 (Bx0-341 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·340⟩ c4) ▸
       at 0 6 (Bx3-0241 ∷ []) (refl) ▸ done

