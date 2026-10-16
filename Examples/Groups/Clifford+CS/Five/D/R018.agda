{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.R018 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (WsL ; wl0001 ; wl0002 ; wl0006 ; wl0007 ; wl0011 ; wl0012 ; wl0015 ; wl0016 ; wl0043 ; wl0046 ; wl0129 ; wl0147 ; wl0152 ; wl0153)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-0-TOFF024)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-1-CS02)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-1-CSd02 ; lem-nat-3-CS23 ; lem-nat-3-CS24)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-nat-1-TOFF034)
open import Examples.Groups.Clifford+CS.Five.D.R012 using (lem-nat-3-CSd24)
open import Examples.Groups.Clifford+CS.Five.D.R013 using (lem-nat-3-CSd23)
open import Examples.Groups.Clifford+CS.Five.D.R015 using (lem-nat-0-BOX⟨3·1420⟩)
open import Examples.Groups.Clifford+CS.Five.D.R016 using (lem-nat-1-BOX⟨1·2430⟩ ; lem-nat-3-BOX⟨0·2341⟩ ; lem-nat-3-BOX⟨0·2431⟩)
open import Examples.Groups.Clifford+CS.Five.D.R017 using (lem-nat-0-SBOX⟨3·1·0·2⟩ ; lem-nat-0-SBOXd⟨3·1·0·2⟩ ; lem-nat-3-SBOX⟨0·2·1·3⟩ ; lem-nat-3-SBOX⟨0·2·1·4⟩ ; lem-nat-3-SBOXd⟨0·2·1·3⟩ ; lem-nat-3-SBOXd⟨0·2·1·4⟩)
-- nat 1 SBOX(1;2;0;3): 3 steps
lem-nat-1-SBOX⟨1·2·0·3⟩ : WsL → ⟪ (Sw12 ∷ Sb1-2-0-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-1-0-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨1·2·0·3⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb1-2-0-3 ∷ []) (Sb2-1-0-3 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS02 ∷ []) (refl) ▸
       at 0 2 (CS01 ∷ Sw12 ∷ []) (lem-nat-1-CS02 c4) ▸
       at 0 1 (Sb2-1-0-3 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(1;2;0;3): 3 steps
lem-nat-1-SBOXd⟨1·2·0·3⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻1-2-0-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-1-0-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨1·2·0·3⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻1-2-0-3 ∷ []) (Sb⁻2-1-0-3 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS02⁻ ∷ []) (refl) ▸
       at 0 2 (CS01⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd02 c4) ▸
       at 0 1 (Sb⁻2-1-0-3 ∷ []) (refl) ▸ done


-- nat 1 SBOX(1;2;43;0): 7 steps
lem-nat-1-SBOX⟨1·2·43·0⟩ : WsL → ⟪ (Sw12 ∷ Sb1-2-43-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-1-43-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨1·2·43·0⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb1-2-43-0 ∷ []) (Sb2-1-43-0 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx1-2430 ∷ Toff034 ∷ Sb1-2-0-3 ∷ Toff034 ∷ Sb⁻1-2-0-3 ∷ []) (refl) ▸
       at 0 2 (Bx2-1430 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·2430⟩ c4) ▸
       at 1 2 (Toff034 ∷ Sw12 ∷ []) (lem-nat-1-TOFF034 c4) ▸
       at 2 2 (Sb2-1-0-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·2·0·3⟩ c4) ▸
       at 3 2 (Toff034 ∷ Sw12 ∷ []) (lem-nat-1-TOFF034 c4) ▸
       at 4 2 (Sb⁻2-1-0-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·2·0·3⟩ c4) ▸
       at 0 5 (Sb2-1-43-0 ∷ []) (refl) ▸ done


-- nat 2 SBOX(0;4;2;1): 3 steps
lem-nat-2-SBOX⟨0·4·2·1⟩ : WsL → ⟪ (Sw23 ∷ Sb0-4-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-4-3-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨0·4·2·1⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb0-4-2-1 ∷ []) (Sb0-4-3-1 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS24 ∷ []) (refl) ▸
       at 0 2 (CS34 ∷ Sw23 ∷ []) (sym (wl0011 c4)) ▸
       at 0 1 (Sb0-4-3-1 ∷ []) (refl) ▸ done


-- nat 2 SBOX(0;4;3;1): 3 steps
lem-nat-2-SBOX⟨0·4·3·1⟩ : WsL → ⟪ (Sw23 ∷ Sb0-4-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-4-2-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨0·4·3·1⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb0-4-3-1 ∷ []) (Sb0-4-2-1 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS34 ∷ []) (refl) ▸
       at 0 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0015 c4)) ▸
       at 0 1 (Sb0-4-2-1 ∷ []) (refl) ▸ done


-- nat 3 SBOX(0;3;2;1): 3 steps
lem-nat-3-SBOX⟨0·3·2·1⟩ : WsL → ⟪ (Sw34 ∷ Sb0-3-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-4-2-1 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨0·3·2·1⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb0-3-2-1 ∷ []) (Sb0-4-2-1 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS23 ∷ []) (refl) ▸
       at 0 2 (CS24 ∷ Sw34 ∷ []) (lem-nat-3-CS23 c4) ▸
       at 0 1 (Sb0-4-2-1 ∷ []) (refl) ▸ done


-- nat 3 SBOX(0;4;2;1): 3 steps
lem-nat-3-SBOX⟨0·4·2·1⟩ : WsL → ⟪ (Sw34 ∷ Sb0-4-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-3-2-1 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨0·4·2·1⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb0-4-2-1 ∷ []) (Sb0-3-2-1 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS24 ∷ []) (refl) ▸
       at 0 2 (CS23 ∷ Sw34 ∷ []) (lem-nat-3-CS24 c4) ▸
       at 0 1 (Sb0-3-2-1 ∷ []) (refl) ▸ done


-- nat 2 SBOX(0;2;3;1): 3 steps
lem-nat-2-SBOX⟨0·2·3·1⟩ : WsL → ⟪ (Sw23 ∷ Sb0-2-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-3-2-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨0·2·3·1⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb0-2-3-1 ∷ []) (Sb0-3-2-1 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS23 ∷ []) (refl) ▸
       at 0 2 (CS23 ∷ Sw23 ∷ []) (sym (wl0152 c4)) ▸
       at 0 1 (Sb0-3-2-1 ∷ []) (refl) ▸ done


-- nat 2 SBOX(0;3;2;1): 3 steps
lem-nat-2-SBOX⟨0·3·2·1⟩ : WsL → ⟪ (Sw23 ∷ Sb0-3-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-3-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨0·3·2·1⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb0-3-2-1 ∷ []) (Sb0-2-3-1 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS23 ∷ []) (refl) ▸
       at 0 2 (CS23 ∷ Sw23 ∷ []) (sym (wl0152 c4)) ▸
       at 0 1 (Sb0-2-3-1 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(0;4;2;1): 3 steps
lem-nat-2-SBOXd⟨0·4·2·1⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻0-4-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-4-3-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨0·4·2·1⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻0-4-2-1 ∷ []) (Sb⁻0-4-3-1 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS24⁻ ∷ []) (refl) ▸
       at 0 2 (CS34⁻ ∷ Sw23 ∷ []) (sym (wl0012 c4)) ▸
       at 0 1 (Sb⁻0-4-3-1 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(0;4;3;1): 3 steps
lem-nat-2-SBOXd⟨0·4·3·1⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻0-4-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-4-2-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨0·4·3·1⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻0-4-3-1 ∷ []) (Sb⁻0-4-2-1 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS34⁻ ∷ []) (refl) ▸
       at 0 2 (CS24⁻ ∷ Sw23 ∷ []) (sym (wl0016 c4)) ▸
       at 0 1 (Sb⁻0-4-2-1 ∷ []) (refl) ▸ done


-- nat 3 SBOXd(0;3;2;1): 3 steps
lem-nat-3-SBOXd⟨0·3·2·1⟩ : WsL → ⟪ (Sw34 ∷ Sb⁻0-3-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-4-2-1 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨0·3·2·1⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb⁻0-3-2-1 ∷ []) (Sb⁻0-4-2-1 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS23⁻ ∷ []) (refl) ▸
       at 0 2 (CS24⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd23 c4) ▸
       at 0 1 (Sb⁻0-4-2-1 ∷ []) (refl) ▸ done


-- nat 3 SBOXd(0;4;2;1): 3 steps
lem-nat-3-SBOXd⟨0·4·2·1⟩ : WsL → ⟪ (Sw34 ∷ Sb⁻0-4-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-3-2-1 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨0·4·2·1⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb⁻0-4-2-1 ∷ []) (Sb⁻0-3-2-1 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS24⁻ ∷ []) (refl) ▸
       at 0 2 (CS23⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd24 c4) ▸
       at 0 1 (Sb⁻0-3-2-1 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(0;2;3;1): 3 steps
lem-nat-2-SBOXd⟨0·2·3·1⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻0-2-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-3-2-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨0·2·3·1⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻0-2-3-1 ∷ []) (Sb⁻0-3-2-1 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS23⁻ ∷ []) (refl) ▸
       at 0 2 (CS23⁻ ∷ Sw23 ∷ []) (sym (wl0153 c4)) ▸
       at 0 1 (Sb⁻0-3-2-1 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(0;3;2;1): 3 steps
lem-nat-2-SBOXd⟨0·3·2·1⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻0-3-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-2-3-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨0·3·2·1⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻0-3-2-1 ∷ []) (Sb⁻0-2-3-1 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS23⁻ ∷ []) (refl) ▸
       at 0 2 (CS23⁻ ∷ Sw23 ∷ []) (sym (wl0153 c4)) ▸
       at 0 1 (Sb⁻0-2-3-1 ∷ []) (refl) ▸ done


-- comm CCZ024 CSd13: 11 steps
lem-comm-CCZ024-CSd13 : WsL → ⟪ (CCZ024 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ CCZ024 ∷ []) ⟫ʷ
lem-comm-CCZ024-CSd13 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ024 ∷ CS13⁻ ∷ []) (Sw12 ∷ Sw34 ∷ Sw34 ∷ CS23⁻ ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ [])
  b0 = at 0 1 (Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CS23⁻ ∷ Sw12 ∷ []) (sym (wl0046 c4)) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 5 3 (CS24⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS34⁻ ∷ Sw23 ∷ []) (sym (wl0012 c4)) ▸
       at 3 2 (CS34⁻ ∷ CCZ012 ∷ []) (c₃ (CCZ) (CS • CS • CS)) ▸
       at 2 2 (CS24⁻ ∷ Sw23 ∷ []) (sym (wl0016 c4)) ▸
       at 2 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw12 ∷ Sw34 ∷ Sw34 ∷ CS23⁻ ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) (CS13⁻ ∷ CCZ024 ∷ [])
  b1 = at 1 2 [] (wl0007 c4) ▸
       at 0 2 (CS13⁻ ∷ Sw12 ∷ []) (sym (wl0043 c4)) ▸
       at 1 7 (CCZ024 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp CX42 at 3: 6 steps
lem-resp-CX42-at-3 : WsL → ⟪ (CX42 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ CX43 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-CX42-at-3 c4 = run b0
  where
  b0 : Chain (CX42 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ CX43 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 0 2 (Sw23 ∷ CX43 ∷ []) (wl0147 c4) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 1 2 (Sw12 ∷ CX43 ∷ []) (sym (c₃ (Swap ↑) (CX₁₀))) ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 c4)) ▸
       at 2 2 (Sw01 ∷ CX43 ∷ []) (sym (c₂ (Swap) (CX₁₀ ↑))) ▸ done


-- nat 3 SBOX(0;2;43;1): 7 steps
lem-nat-3-SBOX⟨0·2·43·1⟩ : WsL → ⟪ (Sw34 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-34-1 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨0·2·43·1⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-34-1 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 0 2 (Bx0-2341 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·2431⟩ c4) ▸
       at 1 2 (Toff134 ∷ Sw34 ∷ []) (wl0129 c4) ▸
       at 2 2 (Sb0-2-1-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·2·1·3⟩ c4) ▸
       at 3 2 (Toff134 ∷ Sw34 ∷ []) (wl0129 c4) ▸
       at 4 2 (Sb⁻0-2-1-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·2·1·3⟩ c4) ▸
       at 0 5 (Sb0-2-34-1 ∷ []) (refl) ▸ done


-- nat 3 SBOX(0;2;34;1): 7 steps
lem-nat-3-SBOX⟨0·2·34·1⟩ : WsL → ⟪ (Sw34 ∷ Sb0-2-34-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨0·2·34·1⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb0-2-34-1 ∷ []) (Sb0-2-43-1 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx0-2341 ∷ Toff134 ∷ Sb0-2-1-4 ∷ Toff134 ∷ Sb⁻0-2-1-4 ∷ []) (refl) ▸
       at 0 2 (Bx0-2431 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·2341⟩ c4) ▸
       at 1 2 (Toff134 ∷ Sw34 ∷ []) (wl0129 c4) ▸
       at 2 2 (Sb0-2-1-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·2·1·4⟩ c4) ▸
       at 3 2 (Toff134 ∷ Sw34 ∷ []) (wl0129 c4) ▸
       at 4 2 (Sb⁻0-2-1-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·2·1·4⟩ c4) ▸
       at 0 5 (Sb0-2-43-1 ∷ []) (refl) ▸ done


-- nat 0 SBOX(3;1;42;0): 7 steps
lem-nat-0-SBOX⟨3·1·42·0⟩ : WsL → ⟪ (Sw01 ∷ Sb3-1-42-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-42-1 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨3·1·42·0⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb3-1-42-0 ∷ []) (Sb3-0-42-1 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx3-1420 ∷ Toff024 ∷ Sb3-1-0-2 ∷ Toff024 ∷ Sb⁻3-1-0-2 ∷ []) (refl) ▸
       at 0 2 (Bx3-0421 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·1420⟩ c4) ▸
       at 1 2 (Toff124 ∷ Sw01 ∷ []) (lem-nat-0-TOFF024 c4) ▸
       at 2 2 (Sb3-0-1-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·1·0·2⟩ c4) ▸
       at 3 2 (Toff124 ∷ Sw01 ∷ []) (lem-nat-0-TOFF024 c4) ▸
       at 4 2 (Sb⁻3-0-1-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨3·1·0·2⟩ c4) ▸
       at 0 5 (Sb3-0-42-1 ∷ []) (refl) ▸ done

