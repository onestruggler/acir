{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.R009 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (WsL ; wl0001 ; wl0002 ; wl0003 ; wl0004 ; wl0006 ; wl0007 ; wl0013 ; wl0015 ; wl0018 ; wl0021 ; wl0022 ; wl0033 ; wl0034 ; wl0037 ; wl0038 ; wl0044 ; wl0047 ; wl0049 ; wl0050 ; wl0051 ; wl0052 ; wl0053 ; wl0057 ; wl0058 ; wl0065 ; wl0067 ; wl0068 ; wl0084 ; wl0085 ; wl0087 ; wl0091 ; wl0093 ; wl0096 ; wl0097 ; wl0099 ; wl0100 ; wl0101 ; wl0102 ; wl0103 ; wl0104 ; wl0107 ; wl0108 ; wl0110 ; wl0111 ; wl0112 ; wl0114 ; wl0116 ; wl0121 ; wl0130 ; wl0141 ; wl0142 ; wl0143)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-nat-1-CCZ023 ; lem-nat-1-CCZ024 ; lem-nat-1-CCZ034 ; lem-nat-1-TOFF014 ; lem-nat-1-TOFF203 ; lem-nat-2-CCZ012 ; lem-nat-2-CCZ013 ; lem-nat-2-CCZ024 ; lem-nat-2-CCZ034 ; lem-nat-2-TOFF012 ; lem-nat-2-TOFF013 ; lem-nat-2-TOFF024 ; lem-nat-2-TOFF034 ; lem-nat-2-TOFF102 ; lem-nat-2-TOFF103 ; lem-nat-2-TOFF301 ; lem-nat-3-CCZ014 ; lem-nat-3-CCZ024 ; lem-nat-3-CCZ034 ; lem-nat-3-TOFF013)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-0-CCZ024 ; lem-nat-0-CCZ124 ; lem-nat-1-CCZ013 ; lem-nat-1-CCZ014 ; lem-nat-1-TOFF103 ; lem-nat-2-TOFF201 ; lem-nat-3-CCZ013 ; lem-nat-3-CCZ023 ; lem-nat-3-TOFF203)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-0-CCZ034 ; lem-nat-0-CCZ134 ; lem-nat-0-TOFF412 ; lem-nat-3-TOFF304)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-0-CZ04 ; lem-nat-0-CZ14 ; lem-nat-0-TOFF402 ; lem-nat-1-TOFF013 ; lem-nat-3-TOFF023 ; lem-nat-3-TOFF214 ; lem-nat-3-TOFF301)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-1-BOX⟨2·0134⟩ ; lem-nat-1-CZ04 ; lem-nat-1-TOFF023 ; lem-nat-1-TOFF401 ; lem-nat-2-CCZ014 ; lem-nat-2-CZ02 ; lem-nat-2-CZ03 ; lem-nat-2-CZ04 ; lem-nat-3-BOX⟨2·03⟩ ; lem-nat-3-CZ03 ; lem-nat-3-CZ04)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-1-CZ01 ; lem-nat-1-CZ02 ; lem-nat-2-BOX⟨0·13⟩ ; lem-nat-2-BOXd⟨0·1324⟩ ; lem-nat-2-BOXd⟨0·14⟩ ; lem-nat-2-CS12 ; lem-nat-2-CS13 ; lem-nat-2-CSd12 ; lem-nat-2-CSd13)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-0-CS04 ; lem-nat-0-TOFF134 ; lem-nat-1-CS04 ; lem-nat-2-SBOX⟨0·1·4·2⟩ ; lem-nat-2-SBOX⟨0·1·4·3⟩ ; lem-nat-2-SBOXd⟨0·1·4·2⟩ ; lem-nat-2-SBOXd⟨0·1·4·3⟩ ; lem-nat-2-TOFF014 ; lem-nat-2-TOFF403)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-nat-0-BOX⟨1·0324⟩ ; lem-nat-0-SBOX⟨0·1·4·3⟩ ; lem-nat-0-SBOX⟨4·0·1·3⟩ ; lem-nat-0-SBOXd⟨0·1·4·3⟩ ; lem-nat-0-SBOXd⟨4·0·1·3⟩ ; lem-nat-0-TOFF034 ; lem-nat-1-BOX⟨4·02⟩ ; lem-nat-1-CSd04 ; lem-nat-1-SBOX⟨1·0·4·2⟩ ; lem-nat-1-SBOX⟨4·0·2·1⟩ ; lem-nat-1-SBOXd⟨1·0·4·2⟩ ; lem-nat-1-SBOXd⟨4·0·2·1⟩ ; lem-nat-1-TOFF034 ; lem-nat-1-TOFF403 ; lem-nat-2-SBOX⟨1·0·4·3⟩ ; lem-nat-2-SBOX⟨4·0·1·2⟩ ; lem-nat-2-SBOXd⟨1·0·4·3⟩ ; lem-nat-2-SBOXd⟨4·0·1·2⟩ ; lem-nat-3-SBOX⟨2·0·4·1⟩ ; lem-nat-3-SBOX⟨3·0·2·1⟩ ; lem-nat-3-SBOXd⟨2·0·4·1⟩ ; lem-nat-3-SBOXd⟨3·0·2·1⟩ ; lem-nat-3-TOFF024 ; lem-nat-3-TOFF401)
-- nat 2 TOFF401: 68 steps
lem-nat-2-TOFF401 : WsL → ⟪ (Sw23 ∷ Toff401 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-TOFF401 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (run b8))))))))
  where
  b0 : Chain (Sw23 ∷ Toff401 ∷ []) (Sw23 ∷ Sw34 ∷ K3 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Toff301 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (K3 ∷ Sw23 ∷ []) (sym (wl0057 c4)) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 3 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸ done

  b1 : Chain (Sw23 ∷ Sw34 ∷ K3 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw34 ∷ []) (Sw23 ∷ K4 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw34 ∷ [])
  b1 = at 5 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 7 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K3 ∷ Sw23 ∷ []) (sym (wl0057 c4)) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 10 2 [] (wl0006 c4) ▸
       at 1 2 (K4 ∷ Sw34 ∷ []) (sym (wl0067 c4)) ▸ done

  b2 : Chain (Sw23 ∷ K4 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw34 ∷ []) (Sw23 ∷ K4 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw34 ∷ K3 ∷ ι ∷ Sw34 ∷ [])
  b2 = at 4 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 2 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 6 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 4 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 6 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸ done

  b3 : Chain (Sw23 ∷ K4 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw34 ∷ K3 ∷ ι ∷ Sw34 ∷ []) (K4 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw23 ∷ CS04 ∷ K4 ∷ ι ∷ [])
  b3 = at 7 2 (K4 ∷ Sw34 ∷ []) (sym (wl0067 c4)) ▸
       at 8 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 9 2 [] (wl0007 c4) ▸
       at 0 2 (K4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K)) ▸
       at 1 2 (CS14 ∷ Sw23 ∷ []) (sym (wl0021 c4)) ▸
       at 2 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 3 2 (CS14⁻ ∷ Sw23 ∷ []) (sym (wl0033 c4)) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸ done

  b4 : Chain (K4 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw23 ∷ CS04 ∷ K4 ∷ ι ∷ []) (K4 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K4 ∷ Sw23 ∷ ι ∷ [])
  b4 = at 6 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (wl0013 c4) ▸
       at 7 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 8 2 (CS01 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸
       at 9 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 10 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (sym (wl0013 c4)) ▸
       at 5 7 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K)) ▸ done

  b5 : Chain (K4 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K4 ∷ Sw23 ∷ ι ∷ []) (Sw34 ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw34 ∷ CX01 ∷ CS04 ∷ K4 ∷ ι ∷ Sw23 ∷ [])
  b5 = at 7 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 1 2 (K3 ∷ Sw34 ∷ []) (sym (wl0068 c4)) ▸
       at 3 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (wl0007 c4) ▸
       at 3 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 5 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0007 c4) ▸ done

  b6 : Chain (Sw34 ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw34 ∷ CX01 ∷ CS04 ∷ K4 ∷ ι ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ K2 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw23 ∷ [])
  b6 = at 5 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 7 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0007 c4) ▸
       at 7 2 (K3 ∷ Sw34 ∷ []) (sym (wl0068 c4)) ▸
       at 8 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 2 2 (K2 ∷ Sw23 ∷ []) (sym (wl0058 c4)) ▸
       at 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b7 : Chain (Sw34 ∷ Sw23 ∷ K2 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ Sw23 ∷ ι ∷ Sw34 ∷ Sw23 ∷ [])
  b7 = at 3 2 [] (wl0006 c4) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0006 c4) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0006 c4) ▸
       at 8 2 (K2 ∷ Sw23 ∷ []) (sym (wl0058 c4)) ▸ done

  b8 : Chain (Sw34 ∷ Sw23 ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ Sw23 ∷ ι ∷ Sw34 ∷ Sw23 ∷ []) (Toff401 ∷ Sw23 ∷ [])
  b8 = at 9 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 2 8 (Toff201 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff301 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Toff401 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 2 BOX(4;02): 3 steps
lem-nat-2-BOX⟨4·02⟩ : WsL → ⟪ (Sw23 ∷ Bx4-02 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-03 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·02⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx4-02 ∷ []) (Bx4-03 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ02 ∷ []) (refl) ▸
       at 0 2 (CZ03 ∷ Sw23 ∷ []) (lem-nat-2-CZ02 c4) ▸
       at 0 1 (Bx4-03 ∷ []) (refl) ▸ done


-- nat 2 BOX(0;432): 8 steps
lem-nat-2-BOX⟨0·432⟩ : WsL → ⟪ (Sw23 ∷ Bx0-432 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-423 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·432⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-432 ∷ []) (Bx0-423 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff034 ∷ Bx4-02 ∷ Toff034 ∷ CCZ034 ∷ Bx4-02 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 1 2 (Toff024 ∷ Sw23 ∷ []) (lem-nat-2-TOFF034 c4) ▸
       at 2 2 (Bx4-03 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·02⟩ c4) ▸
       at 3 2 (Toff024 ∷ Sw23 ∷ []) (lem-nat-2-TOFF034 c4) ▸
       at 4 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 5 2 (Bx4-03 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·02⟩ c4) ▸
       at 0 6 (Bx0-423 ∷ []) (refl) ▸ done


-- nat 2 BOX(4;0132): 8 steps
lem-nat-2-BOX⟨4·0132⟩ : WsL → ⟪ (Sw23 ∷ Bx4-0132 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0123 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·0132⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx4-0132 ∷ []) (Bx4-0123 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff401 ∷ Bx0-432 ∷ Toff401 ∷ CCZ014 ∷ Bx0-432 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 1 2 (Toff401 ∷ Sw23 ∷ []) (lem-nat-2-TOFF401 c4) ▸
       at 2 2 (Bx0-423 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·432⟩ c4) ▸
       at 3 2 (Toff401 ∷ Sw23 ∷ []) (lem-nat-2-TOFF401 c4) ▸
       at 4 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 5 2 (Bx0-423 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·432⟩ c4) ▸
       at 0 6 (Bx4-0123 ∷ []) (refl) ▸ done


-- nat 2 BOX(4;03): 3 steps
lem-nat-2-BOX⟨4·03⟩ : WsL → ⟪ (Sw23 ∷ Bx4-03 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-02 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·03⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx4-03 ∷ []) (Bx4-02 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ03 ∷ []) (refl) ▸
       at 0 2 (CZ02 ∷ Sw23 ∷ []) (lem-nat-2-CZ03 c4) ▸
       at 0 1 (Bx4-02 ∷ []) (refl) ▸ done


-- nat 2 BOX(0;423): 8 steps
lem-nat-2-BOX⟨0·423⟩ : WsL → ⟪ (Sw23 ∷ Bx0-423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-432 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·423⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-423 ∷ []) (Bx0-432 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff024 ∷ Bx4-03 ∷ Toff024 ∷ CCZ024 ∷ Bx4-03 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 1 2 (Toff034 ∷ Sw23 ∷ []) (lem-nat-2-TOFF024 c4) ▸
       at 2 2 (Bx4-02 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·03⟩ c4) ▸
       at 3 2 (Toff034 ∷ Sw23 ∷ []) (lem-nat-2-TOFF024 c4) ▸
       at 4 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 5 2 (Bx4-02 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·03⟩ c4) ▸
       at 0 6 (Bx0-432 ∷ []) (refl) ▸ done


-- nat 2 BOX(4;0123): 8 steps
lem-nat-2-BOX⟨4·0123⟩ : WsL → ⟪ (Sw23 ∷ Bx4-0123 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0132 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·0123⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx4-0123 ∷ []) (Bx4-0132 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff401 ∷ Bx0-423 ∷ Toff401 ∷ CCZ014 ∷ Bx0-423 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 1 2 (Toff401 ∷ Sw23 ∷ []) (lem-nat-2-TOFF401 c4) ▸
       at 2 2 (Bx0-432 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·423⟩ c4) ▸
       at 3 2 (Toff401 ∷ Sw23 ∷ []) (lem-nat-2-TOFF401 c4) ▸
       at 4 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 5 2 (Bx0-432 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·423⟩ c4) ▸
       at 0 6 (Bx4-0132 ∷ []) (refl) ▸ done


-- nat 1 TOFF402: 2 steps
lem-nat-1-TOFF402 : WsL → ⟪ (Sw12 ∷ Toff402 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-TOFF402 c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Toff402 ∷ []) (Toff401 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sw12 ∷ Toff401 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0001 c4) ▸ done


-- nat 1 BOX(4;01): 3 steps
lem-nat-1-BOX⟨4·01⟩ : WsL → ⟪ (Sw12 ∷ Bx4-01 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-02 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·01⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx4-01 ∷ []) (Bx4-02 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ01 ∷ []) (refl) ▸
       at 0 2 (CZ02 ∷ Sw12 ∷ []) (lem-nat-1-CZ01 c4) ▸
       at 0 1 (Bx4-02 ∷ []) (refl) ▸ done


-- nat 1 BOX(0;431): 8 steps
lem-nat-1-BOX⟨0·431⟩ : WsL → ⟪ (Sw12 ∷ Bx0-431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-432 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·431⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-431 ∷ []) (Bx0-432 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff034 ∷ Bx4-01 ∷ Toff034 ∷ CCZ034 ∷ Bx4-01 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 1 2 (Toff034 ∷ Sw12 ∷ []) (lem-nat-1-TOFF034 c4) ▸
       at 2 2 (Bx4-02 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·01⟩ c4) ▸
       at 3 2 (Toff034 ∷ Sw12 ∷ []) (lem-nat-1-TOFF034 c4) ▸
       at 4 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 5 2 (Bx4-02 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·01⟩ c4) ▸
       at 0 6 (Bx0-432 ∷ []) (refl) ▸ done


-- nat 1 BOX(4;0231): 8 steps
lem-nat-1-BOX⟨4·0231⟩ : WsL → ⟪ (Sw12 ∷ Bx4-0231 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0132 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·0231⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx4-0231 ∷ []) (Bx4-0132 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff402 ∷ Bx0-431 ∷ Toff402 ∷ CCZ024 ∷ Bx0-431 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 1 2 (Toff401 ∷ Sw12 ∷ []) (lem-nat-1-TOFF402 c4) ▸
       at 2 2 (Bx0-432 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·431⟩ c4) ▸
       at 3 2 (Toff401 ∷ Sw12 ∷ []) (lem-nat-1-TOFF402 c4) ▸
       at 4 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 5 2 (Bx0-432 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·431⟩ c4) ▸
       at 0 6 (Bx4-0132 ∷ []) (refl) ▸ done


-- nat 1 BOX(0;432): 8 steps
lem-nat-1-BOX⟨0·432⟩ : WsL → ⟪ (Sw12 ∷ Bx0-432 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-431 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·432⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-432 ∷ []) (Bx0-431 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff034 ∷ Bx4-02 ∷ Toff034 ∷ CCZ034 ∷ Bx4-02 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 1 2 (Toff034 ∷ Sw12 ∷ []) (lem-nat-1-TOFF034 c4) ▸
       at 2 2 (Bx4-01 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·02⟩ c4) ▸
       at 3 2 (Toff034 ∷ Sw12 ∷ []) (lem-nat-1-TOFF034 c4) ▸
       at 4 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 5 2 (Bx4-01 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·02⟩ c4) ▸
       at 0 6 (Bx0-431 ∷ []) (refl) ▸ done


-- nat 1 BOX(4;0132): 8 steps
lem-nat-1-BOX⟨4·0132⟩ : WsL → ⟪ (Sw12 ∷ Bx4-0132 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0231 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·0132⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx4-0132 ∷ []) (Bx4-0231 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff401 ∷ Bx0-432 ∷ Toff401 ∷ CCZ014 ∷ Bx0-432 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 1 2 (Toff402 ∷ Sw12 ∷ []) (lem-nat-1-TOFF401 c4) ▸
       at 2 2 (Bx0-431 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·432⟩ c4) ▸
       at 3 2 (Toff402 ∷ Sw12 ∷ []) (lem-nat-1-TOFF401 c4) ▸
       at 4 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 5 2 (Bx0-431 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·432⟩ c4) ▸
       at 0 6 (Bx4-0231 ∷ []) (refl) ▸ done


-- nat 0 BOX(4;10): 3 steps
lem-nat-0-BOX⟨4·10⟩ : WsL → ⟪ (Sw01 ∷ Bx4-10 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-01 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·10⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx4-10 ∷ []) (Bx4-01 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CZ01 ∷ []) (refl) ▸
       at 0 2 (CZ01 ∷ Sw01 ∷ []) (sym (wl0130 c4)) ▸
       at 0 1 (Bx4-01 ∷ []) (refl) ▸ done


-- nat 0 BOX(1;430): 8 steps
lem-nat-0-BOX⟨1·430⟩ : WsL → ⟪ (Sw01 ∷ Bx1-430 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-431 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·430⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-430 ∷ []) (Bx0-431 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff134 ∷ Bx4-10 ∷ Toff134 ∷ CCZ134 ∷ Bx4-10 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 1 2 (Toff034 ∷ Sw01 ∷ []) (lem-nat-0-TOFF134 c4) ▸
       at 2 2 (Bx4-01 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·10⟩ c4) ▸
       at 3 2 (Toff034 ∷ Sw01 ∷ []) (lem-nat-0-TOFF134 c4) ▸
       at 4 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 5 2 (Bx4-01 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·10⟩ c4) ▸
       at 0 6 (Bx0-431 ∷ []) (refl) ▸ done


-- nat 0 BOX(4;1230): 8 steps
lem-nat-0-BOX⟨4·1230⟩ : WsL → ⟪ (Sw01 ∷ Bx4-1230 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0231 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·1230⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx4-1230 ∷ []) (Bx4-0231 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff412 ∷ Bx1-430 ∷ Toff412 ∷ CCZ124 ∷ Bx1-430 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 1 2 (Toff402 ∷ Sw01 ∷ []) (lem-nat-0-TOFF412 c4) ▸
       at 2 2 (Bx0-431 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·430⟩ c4) ▸
       at 3 2 (Toff402 ∷ Sw01 ∷ []) (lem-nat-0-TOFF412 c4) ▸
       at 4 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 5 2 (Bx0-431 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·430⟩ c4) ▸
       at 0 6 (Bx4-0231 ∷ []) (refl) ▸ done


-- nat 3 BOX(0;243): 8 steps
lem-nat-3-BOX⟨0·243⟩ : WsL → ⟪ (Sw34 ∷ Bx0-243 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-234 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·243⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx0-243 ∷ []) (Bx0-234 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff024 ∷ Bx2-03 ∷ Toff024 ∷ CCZ024 ∷ Bx2-03 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 c4) ▸
       at 1 2 (Toff023 ∷ Sw34 ∷ []) (lem-nat-3-TOFF024 c4) ▸
       at 2 2 (Bx2-04 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·03⟩ c4) ▸
       at 3 2 (Toff023 ∷ Sw34 ∷ []) (lem-nat-3-TOFF024 c4) ▸
       at 4 2 (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 c4) ▸
       at 5 2 (Bx2-04 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·03⟩ c4) ▸
       at 0 6 (Bx0-234 ∷ []) (refl) ▸ done


-- nat 3 BOX(2;0143): 8 steps
lem-nat-3-BOX⟨2·0143⟩ : WsL → ⟪ (Sw34 ∷ Bx2-0143 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨2·0143⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx2-0143 ∷ []) (Bx2-0134 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff201 ∷ Bx0-243 ∷ Toff201 ∷ CCZ012 ∷ Bx0-243 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 1 2 (Toff201 ∷ Sw34 ∷ []) (sym (c₃ (Toffᵗ) (Swap))) ▸
       at 2 2 (Bx0-234 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·243⟩ c4) ▸
       at 3 2 (Toff201 ∷ Sw34 ∷ []) (sym (c₃ (Toffᵗ) (Swap))) ▸
       at 4 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 5 2 (Bx0-234 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·243⟩ c4) ▸
       at 0 6 (Bx2-0134 ∷ []) (refl) ▸ done


-- nat 3 CS03: 2 steps
lem-nat-3-CS03 : WsL → ⟪ (Sw34 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-CS03 c4 = run b0
  where
  b0 : Chain (Sw34 ∷ CS03 ∷ []) (CS04 ∷ Sw34 ∷ [])
  b0 = at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 0 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 3 SBOX(2;0;3;4): 3 steps
lem-nat-3-SBOX⟨2·0·3·4⟩ : WsL → ⟪ (Sw34 ∷ Sb2-0-3-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-4-3 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨2·0·3·4⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb2-0-3-4 ∷ []) (Sb2-0-4-3 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS03 ∷ []) (refl) ▸
       at 0 2 (CS04 ∷ Sw34 ∷ []) (lem-nat-3-CS03 c4) ▸
       at 0 1 (Sb2-0-4-3 ∷ []) (refl) ▸ done


-- nat 3 CSd03: 2 steps
lem-nat-3-CSd03 : WsL → ⟪ (Sw34 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS04⁻ ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-CSd03 c4 = run b0
  where
  b0 : Chain (Sw34 ∷ CS03⁻ ∷ []) (CS04⁻ ∷ Sw34 ∷ [])
  b0 = at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 0 3 (CS04⁻ ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 3 SBOXd(2;0;3;4): 3 steps
lem-nat-3-SBOXd⟨2·0·3·4⟩ : WsL → ⟪ (Sw34 ∷ Sb⁻2-0-3-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-0-4-3 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨2·0·3·4⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb⁻2-0-3-4 ∷ []) (Sb⁻2-0-4-3 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS03⁻ ∷ []) (refl) ▸
       at 0 2 (CS04⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd03 c4) ▸
       at 0 1 (Sb⁻2-0-4-3 ∷ []) (refl) ▸ done


-- nat 3 SBOX(2;0;14;3): 7 steps
lem-nat-3-SBOX⟨2·0·14·3⟩ : WsL → ⟪ (Sw34 ∷ Sb2-0-14-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-13-4 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨2·0·14·3⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb2-0-14-3 ∷ []) (Sb2-0-13-4 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx2-0143 ∷ Toff314 ∷ Sb2-0-3-4 ∷ Toff314 ∷ Sb⁻2-0-3-4 ∷ []) (refl) ▸
       at 0 2 (Bx2-0134 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·0143⟩ c4) ▸
       at 1 2 (Toff413 ∷ Sw34 ∷ []) (wl0142 c4) ▸
       at 2 2 (Sb2-0-4-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨2·0·3·4⟩ c4) ▸
       at 3 2 (Toff413 ∷ Sw34 ∷ []) (wl0142 c4) ▸
       at 4 2 (Sb⁻2-0-4-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨2·0·3·4⟩ c4) ▸
       at 0 5 (Sb2-0-13-4 ∷ []) (refl) ▸ done


-- nat 1 SBOX(2;0;4;3): 3 steps
lem-nat-1-SBOX⟨2·0·4·3⟩ : WsL → ⟪ (Sw12 ∷ Sb2-0-4-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-4-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨2·0·4·3⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb2-0-4-3 ∷ []) (Sb1-0-4-3 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS04 ∷ []) (refl) ▸
       at 0 2 (CS04 ∷ Sw12 ∷ []) (lem-nat-1-CS04 c4) ▸
       at 0 1 (Sb1-0-4-3 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(2;0;4;3): 3 steps
lem-nat-1-SBOXd⟨2·0·4·3⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻2-0-4-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-4-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨2·0·4·3⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻2-0-4-3 ∷ []) (Sb⁻1-0-4-3 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS04⁻ ∷ []) (refl) ▸
       at 0 2 (CS04⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd04 c4) ▸
       at 0 1 (Sb⁻1-0-4-3 ∷ []) (refl) ▸ done


-- nat 1 SBOX(2;0;13;4): 7 steps
lem-nat-1-SBOX⟨2·0·13·4⟩ : WsL → ⟪ (Sw12 ∷ Sb2-0-13-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-23-4 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨2·0·13·4⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb2-0-13-4 ∷ []) (Sb1-0-23-4 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx2-0134 ∷ Toff413 ∷ Sb2-0-4-3 ∷ Toff413 ∷ Sb⁻2-0-4-3 ∷ []) (refl) ▸
       at 0 2 (Bx1-0234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0134⟩ c4) ▸
       at 1 2 (Toff423 ∷ Sw12 ∷ []) (wl0085 c4) ▸
       at 2 2 (Sb1-0-4-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·4·3⟩ c4) ▸
       at 3 2 (Toff423 ∷ Sw12 ∷ []) (wl0085 c4) ▸
       at 4 2 (Sb⁻1-0-4-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·4·3⟩ c4) ▸
       at 0 5 (Sb1-0-23-4 ∷ []) (refl) ▸ done


-- nat 0 SBOX(1;0;4;2): 3 steps
lem-nat-0-SBOX⟨1·0·4·2⟩ : WsL → ⟪ (Sw01 ∷ Sb1-0-4-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-4-2 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨1·0·4·2⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb1-0-4-2 ∷ []) (Sb0-1-4-2 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS04 ∷ []) (refl) ▸
       at 0 2 (CS14 ∷ Sw01 ∷ []) (lem-nat-0-CS04 c4) ▸
       at 0 1 (Sb0-1-4-2 ∷ []) (refl) ▸ done


-- nat 0 CSd04: 5 steps
lem-nat-0-CSd04 : WsL → ⟪ (Sw01 ∷ CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS14⁻ ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-CSd04 c4 = run b0
  where
  b0 : Chain (Sw01 ∷ CS04⁻ ∷ []) (CS14⁻ ∷ Sw01 ∷ [])
  b0 = at 1 1 (Sw34 ∷ CS03⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 1 2 (CS13⁻ ∷ Sw01 ∷ []) (sym (wl0121 c4)) ▸
       at 2 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 0 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 SBOXd(1;0;4;2): 3 steps
lem-nat-0-SBOXd⟨1·0·4·2⟩ : WsL → ⟪ (Sw01 ∷ Sb⁻1-0-4-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-4-2 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨1·0·4·2⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻1-0-4-2 ∷ []) (Sb⁻0-1-4-2 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS04⁻ ∷ []) (refl) ▸
       at 0 2 (CS14⁻ ∷ Sw01 ∷ []) (lem-nat-0-CSd04 c4) ▸
       at 0 1 (Sb⁻0-1-4-2 ∷ []) (refl) ▸ done


-- nat 0 SBOX(1;0;32;4): 7 steps
lem-nat-0-SBOX⟨1·0·32·4⟩ : WsL → ⟪ (Sw01 ∷ Sb1-0-32-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-32-4 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨1·0·32·4⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb1-0-32-4 ∷ []) (Sb0-1-32-4 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx1-0324 ∷ Toff423 ∷ Sb1-0-4-2 ∷ Toff423 ∷ Sb⁻1-0-4-2 ∷ []) (refl) ▸
       at 0 2 (Bx0-1324 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0324⟩ c4) ▸
       at 1 2 (Toff423 ∷ Sw01 ∷ []) (c₂ (Swap) (Toffᵗ)) ▸
       at 2 2 (Sb0-1-4-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·4·2⟩ c4) ▸
       at 3 2 (Toff423 ∷ Sw01 ∷ []) (c₂ (Swap) (Toffᵗ)) ▸
       at 4 2 (Sb⁻0-1-4-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·4·2⟩ c4) ▸
       at 0 5 (Sb0-1-32-4 ∷ []) (refl) ▸ done


-- nat 3 BOXd(2;04): 3 steps
lem-nat-3-BOXd⟨2·04⟩ : WsL → ⟪ (Sw34 ∷ Bx⁻2-04 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-03 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨2·04⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx⁻2-04 ∷ []) (Bx⁻2-03 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CZ04 ∷ []) (refl) ▸
       at 0 2 (CZ03 ∷ Sw34 ∷ []) (lem-nat-3-CZ04 c4) ▸
       at 0 1 (Bx⁻2-03 ∷ []) (refl) ▸ done


-- nat 3 BOXd(0;214): 8 steps
lem-nat-3-BOXd⟨0·214⟩ : WsL → ⟪ (Sw34 ∷ Bx⁻0-214 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-213 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨0·214⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx⁻0-214 ∷ []) (Bx⁻0-213 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx⁻2-04 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-04 ∷ Toff012 ∷ CCZ012 ∷ []) (refl) ▸
       at 0 2 (Bx⁻2-03 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨2·04⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 2 2 (Toff012 ∷ Sw34 ∷ []) (sym (c₃ (Toff) (Swap))) ▸
       at 3 2 (Bx⁻2-03 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨2·04⟩ c4) ▸
       at 4 2 (Toff012 ∷ Sw34 ∷ []) (sym (c₃ (Toff) (Swap))) ▸
       at 5 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 0 6 (Bx⁻0-213 ∷ []) (refl) ▸ done


-- nat 3 BOXd(2;0314): 8 steps
lem-nat-3-BOXd⟨2·0314⟩ : WsL → ⟪ (Sw34 ∷ Bx⁻2-0314 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-0413 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨2·0314⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx⁻2-0314 ∷ []) (Bx⁻2-0413 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx⁻0-214 ∷ CCZ023 ∷ Toff203 ∷ Bx⁻0-214 ∷ Toff203 ∷ CCZ023 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-213 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨0·214⟩ c4) ▸
       at 1 2 (CCZ024 ∷ Sw34 ∷ []) (lem-nat-3-CCZ023 c4) ▸
       at 2 2 (Toff204 ∷ Sw34 ∷ []) (lem-nat-3-TOFF203 c4) ▸
       at 3 2 (Bx⁻0-213 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨0·214⟩ c4) ▸
       at 4 2 (Toff204 ∷ Sw34 ∷ []) (lem-nat-3-TOFF203 c4) ▸
       at 5 2 (CCZ024 ∷ Sw34 ∷ []) (lem-nat-3-CCZ023 c4) ▸
       at 0 6 (Bx⁻2-0413 ∷ []) (refl) ▸ done


-- nat 3 SBOXd(2;0;31;4): 7 steps
lem-nat-3-SBOXd⟨2·0·31·4⟩ : WsL → ⟪ (Sw34 ∷ Sb⁻2-0-31-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-0-41-3 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨2·0·31·4⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb⁻2-0-31-4 ∷ []) (Sb⁻2-0-41-3 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sb2-0-4-1 ∷ Toff413 ∷ Sb⁻2-0-4-1 ∷ Toff413 ∷ Bx⁻2-0314 ∷ []) (refl) ▸
       at 0 2 (Sb2-0-3-1 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨2·0·4·1⟩ c4) ▸
       at 1 2 (Toff314 ∷ Sw34 ∷ []) (wl0141 c4) ▸
       at 2 2 (Sb⁻2-0-3-1 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨2·0·4·1⟩ c4) ▸
       at 3 2 (Toff314 ∷ Sw34 ∷ []) (wl0141 c4) ▸
       at 4 2 (Bx⁻2-0413 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨2·0314⟩ c4) ▸
       at 0 5 (Sb⁻2-0-41-3 ∷ []) (refl) ▸ done


-- nat 3 BOXd(2;03): 3 steps
lem-nat-3-BOXd⟨2·03⟩ : WsL → ⟪ (Sw34 ∷ Bx⁻2-03 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-04 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨2·03⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx⁻2-03 ∷ []) (Bx⁻2-04 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CZ03 ∷ []) (refl) ▸
       at 0 2 (CZ04 ∷ Sw34 ∷ []) (lem-nat-3-CZ03 c4) ▸
       at 0 1 (Bx⁻2-04 ∷ []) (refl) ▸ done


-- nat 3 BOXd(0;243): 8 steps
lem-nat-3-BOXd⟨0·243⟩ : WsL → ⟪ (Sw34 ∷ Bx⁻0-243 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-234 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨0·243⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx⁻0-243 ∷ []) (Bx⁻0-234 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx⁻2-03 ∷ CCZ024 ∷ Toff024 ∷ Bx⁻2-03 ∷ Toff024 ∷ CCZ024 ∷ []) (refl) ▸
       at 0 2 (Bx⁻2-04 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨2·03⟩ c4) ▸
       at 1 2 (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 c4) ▸
       at 2 2 (Toff023 ∷ Sw34 ∷ []) (lem-nat-3-TOFF024 c4) ▸
       at 3 2 (Bx⁻2-04 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨2·03⟩ c4) ▸
       at 4 2 (Toff023 ∷ Sw34 ∷ []) (lem-nat-3-TOFF024 c4) ▸
       at 5 2 (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 c4) ▸
       at 0 6 (Bx⁻0-234 ∷ []) (refl) ▸ done


-- nat 3 BOXd(2;0143): 8 steps
lem-nat-3-BOXd⟨2·0143⟩ : WsL → ⟪ (Sw34 ∷ Bx⁻2-0143 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-0134 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨2·0143⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx⁻2-0143 ∷ []) (Bx⁻2-0134 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx⁻0-243 ∷ CCZ012 ∷ Toff201 ∷ Bx⁻0-243 ∷ Toff201 ∷ CCZ012 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-234 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨0·243⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 2 2 (Toff201 ∷ Sw34 ∷ []) (sym (c₃ (Toffᵗ) (Swap))) ▸
       at 3 2 (Bx⁻0-234 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨0·243⟩ c4) ▸
       at 4 2 (Toff201 ∷ Sw34 ∷ []) (sym (c₃ (Toffᵗ) (Swap))) ▸
       at 5 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 0 6 (Bx⁻2-0134 ∷ []) (refl) ▸ done


-- nat 3 SBOXd(2;0;14;3): 7 steps
lem-nat-3-SBOXd⟨2·0·14·3⟩ : WsL → ⟪ (Sw34 ∷ Sb⁻2-0-14-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-0-13-4 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨2·0·14·3⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb⁻2-0-14-3 ∷ []) (Sb⁻2-0-13-4 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sb2-0-3-4 ∷ Toff314 ∷ Sb⁻2-0-3-4 ∷ Toff314 ∷ Bx⁻2-0143 ∷ []) (refl) ▸
       at 0 2 (Sb2-0-4-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨2·0·3·4⟩ c4) ▸
       at 1 2 (Toff413 ∷ Sw34 ∷ []) (wl0142 c4) ▸
       at 2 2 (Sb⁻2-0-4-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨2·0·3·4⟩ c4) ▸
       at 3 2 (Toff413 ∷ Sw34 ∷ []) (wl0142 c4) ▸
       at 4 2 (Bx⁻2-0134 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨2·0143⟩ c4) ▸
       at 0 5 (Sb⁻2-0-13-4 ∷ []) (refl) ▸ done


-- nat 1 BOXd(1;04): 3 steps
lem-nat-1-BOXd⟨1·04⟩ : WsL → ⟪ (Sw12 ∷ Bx⁻1-04 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-04 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨1·04⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻1-04 ∷ []) (Bx⁻2-04 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ04 ∷ []) (refl) ▸
       at 0 2 (CZ04 ∷ Sw12 ∷ []) (lem-nat-1-CZ04 c4) ▸
       at 0 1 (Bx⁻2-04 ∷ []) (refl) ▸ done


-- nat 1 BOXd(0;124): 8 steps
lem-nat-1-BOXd⟨0·124⟩ : WsL → ⟪ (Sw12 ∷ Bx⁻0-124 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-214 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨0·124⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻0-124 ∷ []) (Bx⁻0-214 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx⁻1-04 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻1-04 ∷ Toff012 ∷ CCZ012 ∷ []) (refl) ▸
       at 0 2 (Bx⁻2-04 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨1·04⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw12 ∷ []) (sym (wl0037 c4)) ▸
       at 2 2 (Toff012 ∷ Sw12 ∷ []) (wl0038 c4) ▸
       at 3 2 (Bx⁻2-04 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨1·04⟩ c4) ▸
       at 4 2 (Toff012 ∷ Sw12 ∷ []) (wl0038 c4) ▸
       at 5 2 (CCZ012 ∷ Sw12 ∷ []) (sym (wl0037 c4)) ▸
       at 0 6 (Bx⁻0-214 ∷ []) (refl) ▸ done


-- nat 1 BOXd(1;0324): 8 steps
lem-nat-1-BOXd⟨1·0324⟩ : WsL → ⟪ (Sw12 ∷ Bx⁻1-0324 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-0314 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨1·0324⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻1-0324 ∷ []) (Bx⁻2-0314 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx⁻0-124 ∷ CCZ013 ∷ Toff103 ∷ Bx⁻0-124 ∷ Toff103 ∷ CCZ013 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-214 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨0·124⟩ c4) ▸
       at 1 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 2 2 (Toff203 ∷ Sw12 ∷ []) (lem-nat-1-TOFF103 c4) ▸
       at 3 2 (Bx⁻0-214 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨0·124⟩ c4) ▸
       at 4 2 (Toff203 ∷ Sw12 ∷ []) (lem-nat-1-TOFF103 c4) ▸
       at 5 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 0 6 (Bx⁻2-0314 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(1;0;32;4): 7 steps
lem-nat-1-SBOXd⟨1·0·32·4⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻1-0-32-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-0-31-4 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨1·0·32·4⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻1-0-32-4 ∷ []) (Sb⁻2-0-31-4 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sb1-0-4-2 ∷ Toff423 ∷ Sb⁻1-0-4-2 ∷ Toff423 ∷ Bx⁻1-0324 ∷ []) (refl) ▸
       at 0 2 (Sb2-0-4-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·4·2⟩ c4) ▸
       at 1 2 (Toff413 ∷ Sw12 ∷ []) (wl0091 c4) ▸
       at 2 2 (Sb⁻2-0-4-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·0·4·2⟩ c4) ▸
       at 3 2 (Toff413 ∷ Sw12 ∷ []) (wl0091 c4) ▸
       at 4 2 (Bx⁻2-0314 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨1·0324⟩ c4) ▸
       at 0 5 (Sb⁻2-0-31-4 ∷ []) (refl) ▸ done


-- nat 1 BOXd(2;04): 3 steps
lem-nat-1-BOXd⟨2·04⟩ : WsL → ⟪ (Sw12 ∷ Bx⁻2-04 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-04 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨2·04⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻2-04 ∷ []) (Bx⁻1-04 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ04 ∷ []) (refl) ▸
       at 0 2 (CZ04 ∷ Sw12 ∷ []) (lem-nat-1-CZ04 c4) ▸
       at 0 1 (Bx⁻1-04 ∷ []) (refl) ▸ done


-- nat 1 BOXd(0;234): 8 steps
lem-nat-1-BOXd⟨0·234⟩ : WsL → ⟪ (Sw12 ∷ Bx⁻0-234 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-134 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨0·234⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻0-234 ∷ []) (Bx⁻0-134 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx⁻2-04 ∷ CCZ023 ∷ Toff023 ∷ Bx⁻2-04 ∷ Toff023 ∷ CCZ023 ∷ []) (refl) ▸
       at 0 2 (Bx⁻1-04 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨2·04⟩ c4) ▸
       at 1 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 2 2 (Toff013 ∷ Sw12 ∷ []) (lem-nat-1-TOFF023 c4) ▸
       at 3 2 (Bx⁻1-04 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨2·04⟩ c4) ▸
       at 4 2 (Toff013 ∷ Sw12 ∷ []) (lem-nat-1-TOFF023 c4) ▸
       at 5 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 0 6 (Bx⁻0-134 ∷ []) (refl) ▸ done


-- nat 1 BOXd(2;0134): 8 steps
lem-nat-1-BOXd⟨2·0134⟩ : WsL → ⟪ (Sw12 ∷ Bx⁻2-0134 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-0234 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨2·0134⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻2-0134 ∷ []) (Bx⁻1-0234 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx⁻0-234 ∷ CCZ012 ∷ Toff201 ∷ Bx⁻0-234 ∷ Toff201 ∷ CCZ012 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-134 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨0·234⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw12 ∷ []) (sym (wl0037 c4)) ▸
       at 2 2 (Toff102 ∷ Sw12 ∷ []) (wl0044 c4) ▸
       at 3 2 (Bx⁻0-134 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨0·234⟩ c4) ▸
       at 4 2 (Toff102 ∷ Sw12 ∷ []) (wl0044 c4) ▸
       at 5 2 (CCZ012 ∷ Sw12 ∷ []) (sym (wl0037 c4)) ▸
       at 0 6 (Bx⁻1-0234 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(2;0;13;4): 7 steps
lem-nat-1-SBOXd⟨2·0·13·4⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻2-0-13-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-23-4 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨2·0·13·4⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻2-0-13-4 ∷ []) (Sb⁻1-0-23-4 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sb2-0-4-3 ∷ Toff413 ∷ Sb⁻2-0-4-3 ∷ Toff413 ∷ Bx⁻2-0134 ∷ []) (refl) ▸
       at 0 2 (Sb1-0-4-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·4·3⟩ c4) ▸
       at 1 2 (Toff423 ∷ Sw12 ∷ []) (wl0085 c4) ▸
       at 2 2 (Sb⁻1-0-4-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·4·3⟩ c4) ▸
       at 3 2 (Toff423 ∷ Sw12 ∷ []) (wl0085 c4) ▸
       at 4 2 (Bx⁻1-0234 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨2·0134⟩ c4) ▸
       at 0 5 (Sb⁻1-0-23-4 ∷ []) (refl) ▸ done


-- nat 2 BOXd(1;04): 3 steps
lem-nat-2-BOXd⟨1·04⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻1-04 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-04 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨1·04⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻1-04 ∷ []) (Bx⁻1-04 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ04 ∷ []) (refl) ▸
       at 0 2 (CZ04 ∷ Sw23 ∷ []) (lem-nat-2-CZ04 c4) ▸
       at 0 1 (Bx⁻1-04 ∷ []) (refl) ▸ done


-- nat 2 BOXd(0;134): 8 steps
lem-nat-2-BOXd⟨0·134⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻0-134 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-124 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨0·134⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻0-134 ∷ []) (Bx⁻0-124 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx⁻1-04 ∷ CCZ013 ∷ Toff013 ∷ Bx⁻1-04 ∷ Toff013 ∷ CCZ013 ∷ []) (refl) ▸
       at 0 2 (Bx⁻1-04 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·04⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 2 2 (Toff012 ∷ Sw23 ∷ []) (lem-nat-2-TOFF013 c4) ▸
       at 3 2 (Bx⁻1-04 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·04⟩ c4) ▸
       at 4 2 (Toff012 ∷ Sw23 ∷ []) (lem-nat-2-TOFF013 c4) ▸
       at 5 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 0 6 (Bx⁻0-124 ∷ []) (refl) ▸ done


-- nat 2 BOXd(1;0234): 8 steps
lem-nat-2-BOXd⟨1·0234⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻1-0234 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-0324 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨1·0234⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻1-0234 ∷ []) (Bx⁻1-0324 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx⁻0-134 ∷ CCZ012 ∷ Toff102 ∷ Bx⁻0-134 ∷ Toff102 ∷ CCZ012 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-124 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·134⟩ c4) ▸
       at 1 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 2 2 (Toff103 ∷ Sw23 ∷ []) (lem-nat-2-TOFF102 c4) ▸
       at 3 2 (Bx⁻0-124 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·134⟩ c4) ▸
       at 4 2 (Toff103 ∷ Sw23 ∷ []) (lem-nat-2-TOFF102 c4) ▸
       at 5 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 0 6 (Bx⁻1-0324 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(1;0;23;4): 7 steps
lem-nat-2-SBOXd⟨1·0·23·4⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻1-0-23-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-32-4 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨1·0·23·4⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻1-0-23-4 ∷ []) (Sb⁻1-0-32-4 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sb1-0-4-3 ∷ Toff423 ∷ Sb⁻1-0-4-3 ∷ Toff423 ∷ Bx⁻1-0234 ∷ []) (refl) ▸
       at 0 2 (Sb1-0-4-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·4·3⟩ c4) ▸
       at 1 2 (Toff423 ∷ Sw23 ∷ []) (wl0087 c4) ▸
       at 2 2 (Sb⁻1-0-4-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·0·4·3⟩ c4) ▸
       at 3 2 (Toff423 ∷ Sw23 ∷ []) (wl0087 c4) ▸
       at 4 2 (Bx⁻1-0324 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·0234⟩ c4) ▸
       at 0 5 (Sb⁻1-0-32-4 ∷ []) (refl) ▸ done


-- nat 0 BOXd(0;14): 3 steps
lem-nat-0-BOXd⟨0·14⟩ : WsL → ⟪ (Sw01 ∷ Bx⁻0-14 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-04 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨0·14⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻0-14 ∷ []) (Bx⁻1-04 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CZ14 ∷ []) (refl) ▸
       at 0 2 (CZ04 ∷ Sw01 ∷ []) (lem-nat-0-CZ14 c4) ▸
       at 0 1 (Bx⁻1-04 ∷ []) (refl) ▸ done


-- nat 0 BOXd(1;034): 8 steps
lem-nat-0-BOXd⟨1·034⟩ : WsL → ⟪ (Sw01 ∷ Bx⁻1-034 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-134 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨1·034⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻1-034 ∷ []) (Bx⁻0-134 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx⁻0-14 ∷ CCZ013 ∷ Toff103 ∷ Bx⁻0-14 ∷ Toff103 ∷ CCZ013 ∷ []) (refl) ▸
       at 0 2 (Bx⁻1-04 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨0·14⟩ c4) ▸
       at 1 2 (CCZ013 ∷ Sw01 ∷ []) (sym (wl0100 c4)) ▸
       at 2 2 (Toff013 ∷ Sw01 ∷ []) (wl0102 c4) ▸
       at 3 2 (Bx⁻1-04 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨0·14⟩ c4) ▸
       at 4 2 (Toff013 ∷ Sw01 ∷ []) (wl0102 c4) ▸
       at 5 2 (CCZ013 ∷ Sw01 ∷ []) (sym (wl0100 c4)) ▸
       at 0 6 (Bx⁻0-134 ∷ []) (refl) ▸ done


-- nat 0 BOXd(0;1234): 8 steps
lem-nat-0-BOXd⟨0·1234⟩ : WsL → ⟪ (Sw01 ∷ Bx⁻0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-0234 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨0·1234⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻0-1234 ∷ []) (Bx⁻1-0234 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx⁻1-034 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻1-034 ∷ Toff012 ∷ CCZ012 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-134 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨1·034⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw01 ∷ []) (sym (wl0096 c4)) ▸
       at 2 2 (Toff102 ∷ Sw01 ∷ []) (wl0099 c4) ▸
       at 3 2 (Bx⁻0-134 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨1·034⟩ c4) ▸
       at 4 2 (Toff102 ∷ Sw01 ∷ []) (wl0099 c4) ▸
       at 5 2 (CCZ012 ∷ Sw01 ∷ []) (sym (wl0096 c4)) ▸
       at 0 6 (Bx⁻1-0234 ∷ []) (refl) ▸ done


-- nat 0 SBOXd(0;1;23;4): 7 steps
lem-nat-0-SBOXd⟨0·1·23·4⟩ : WsL → ⟪ (Sw01 ∷ Sb⁻0-1-23-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-23-4 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨0·1·23·4⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻0-1-23-4 ∷ []) (Sb⁻1-0-23-4 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ []) (refl) ▸
       at 0 2 (Sb1-0-4-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·4·3⟩ c4) ▸
       at 1 2 (Toff423 ∷ Sw01 ∷ []) (c₂ (Swap) (Toffᵗ)) ▸
       at 2 2 (Sb⁻1-0-4-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨0·1·4·3⟩ c4) ▸
       at 3 2 (Toff423 ∷ Sw01 ∷ []) (c₂ (Swap) (Toffᵗ)) ▸
       at 4 2 (Bx⁻1-0234 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨0·1234⟩ c4) ▸
       at 0 5 (Sb⁻1-0-23-4 ∷ []) (refl) ▸ done


-- nat 0 BOXd(1;04): 3 steps
lem-nat-0-BOXd⟨1·04⟩ : WsL → ⟪ (Sw01 ∷ Bx⁻1-04 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-14 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨1·04⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻1-04 ∷ []) (Bx⁻0-14 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CZ04 ∷ []) (refl) ▸
       at 0 2 (CZ14 ∷ Sw01 ∷ []) (lem-nat-0-CZ04 c4) ▸
       at 0 1 (Bx⁻0-14 ∷ []) (refl) ▸ done


-- nat 0 BOXd(0;124): 8 steps
lem-nat-0-BOXd⟨0·124⟩ : WsL → ⟪ (Sw01 ∷ Bx⁻0-124 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-024 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨0·124⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻0-124 ∷ []) (Bx⁻1-024 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx⁻1-04 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻1-04 ∷ Toff012 ∷ CCZ012 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-14 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨1·04⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw01 ∷ []) (sym (wl0096 c4)) ▸
       at 2 2 (Toff102 ∷ Sw01 ∷ []) (wl0099 c4) ▸
       at 3 2 (Bx⁻0-14 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨1·04⟩ c4) ▸
       at 4 2 (Toff102 ∷ Sw01 ∷ []) (wl0099 c4) ▸
       at 5 2 (CCZ012 ∷ Sw01 ∷ []) (sym (wl0096 c4)) ▸
       at 0 6 (Bx⁻1-024 ∷ []) (refl) ▸ done


-- nat 0 BOXd(1;0324): 8 steps
lem-nat-0-BOXd⟨1·0324⟩ : WsL → ⟪ (Sw01 ∷ Bx⁻1-0324 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-1324 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨1·0324⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻1-0324 ∷ []) (Bx⁻0-1324 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx⁻0-124 ∷ CCZ013 ∷ Toff103 ∷ Bx⁻0-124 ∷ Toff103 ∷ CCZ013 ∷ []) (refl) ▸
       at 0 2 (Bx⁻1-024 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨0·124⟩ c4) ▸
       at 1 2 (CCZ013 ∷ Sw01 ∷ []) (sym (wl0100 c4)) ▸
       at 2 2 (Toff013 ∷ Sw01 ∷ []) (wl0102 c4) ▸
       at 3 2 (Bx⁻1-024 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨0·124⟩ c4) ▸
       at 4 2 (Toff013 ∷ Sw01 ∷ []) (wl0102 c4) ▸
       at 5 2 (CCZ013 ∷ Sw01 ∷ []) (sym (wl0100 c4)) ▸
       at 0 6 (Bx⁻0-1324 ∷ []) (refl) ▸ done


-- nat 0 SBOXd(1;0;32;4): 7 steps
lem-nat-0-SBOXd⟨1·0·32·4⟩ : WsL → ⟪ (Sw01 ∷ Sb⁻1-0-32-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-32-4 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨1·0·32·4⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻1-0-32-4 ∷ []) (Sb⁻0-1-32-4 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Sb1-0-4-2 ∷ Toff423 ∷ Sb⁻1-0-4-2 ∷ Toff423 ∷ Bx⁻1-0324 ∷ []) (refl) ▸
       at 0 2 (Sb0-1-4-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·4·2⟩ c4) ▸
       at 1 2 (Toff423 ∷ Sw01 ∷ []) (c₂ (Swap) (Toffᵗ)) ▸
       at 2 2 (Sb⁻0-1-4-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·4·2⟩ c4) ▸
       at 3 2 (Toff423 ∷ Sw01 ∷ []) (c₂ (Swap) (Toffᵗ)) ▸
       at 4 2 (Bx⁻0-1324 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨1·0324⟩ c4) ▸
       at 0 5 (Sb⁻0-1-32-4 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(0;1;32;4): 7 steps
lem-nat-2-SBOXd⟨0·1·32·4⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻0-1-32-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-23-4 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨0·1·32·4⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻0-1-32-4 ∷ []) (Sb⁻0-1-23-4 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ Toff423 ∷ Bx⁻0-1324 ∷ []) (refl) ▸
       at 0 2 (Sb0-1-4-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·4·2⟩ c4) ▸
       at 1 2 (Toff423 ∷ Sw23 ∷ []) (wl0087 c4) ▸
       at 2 2 (Sb⁻0-1-4-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·4·2⟩ c4) ▸
       at 3 2 (Toff423 ∷ Sw23 ∷ []) (wl0087 c4) ▸
       at 4 2 (Bx⁻0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·1324⟩ c4) ▸
       at 0 5 (Sb⁻0-1-23-4 ∷ []) (refl) ▸ done


-- nat 2 BOXd(1;034): 8 steps
lem-nat-2-BOXd⟨1·034⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻1-034 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-024 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨1·034⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻1-034 ∷ []) (Bx⁻1-024 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx⁻0-14 ∷ CCZ013 ∷ Toff103 ∷ Bx⁻0-14 ∷ Toff103 ∷ CCZ013 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-14 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·14⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 2 2 (Toff102 ∷ Sw23 ∷ []) (lem-nat-2-TOFF103 c4) ▸
       at 3 2 (Bx⁻0-14 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·14⟩ c4) ▸
       at 4 2 (Toff102 ∷ Sw23 ∷ []) (lem-nat-2-TOFF103 c4) ▸
       at 5 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 0 6 (Bx⁻1-024 ∷ []) (refl) ▸ done


-- nat 2 BOXd(0;1234): 8 steps
lem-nat-2-BOXd⟨0·1234⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-1324 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨0·1234⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻0-1234 ∷ []) (Bx⁻0-1324 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx⁻1-034 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻1-034 ∷ Toff012 ∷ CCZ012 ∷ []) (refl) ▸
       at 0 2 (Bx⁻1-024 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·034⟩ c4) ▸
       at 1 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 2 2 (Toff013 ∷ Sw23 ∷ []) (lem-nat-2-TOFF012 c4) ▸
       at 3 2 (Bx⁻1-024 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·034⟩ c4) ▸
       at 4 2 (Toff013 ∷ Sw23 ∷ []) (lem-nat-2-TOFF012 c4) ▸
       at 5 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 0 6 (Bx⁻0-1324 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(0;1;23;4): 7 steps
lem-nat-2-SBOXd⟨0·1·23·4⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻0-1-23-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-32-4 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨0·1·23·4⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻0-1-23-4 ∷ []) (Sb⁻0-1-32-4 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ []) (refl) ▸
       at 0 2 (Sb0-1-4-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·4·3⟩ c4) ▸
       at 1 2 (Toff423 ∷ Sw23 ∷ []) (wl0087 c4) ▸
       at 2 2 (Sb⁻0-1-4-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·4·3⟩ c4) ▸
       at 3 2 (Toff423 ∷ Sw23 ∷ []) (wl0087 c4) ▸
       at 4 2 (Bx⁻0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·1234⟩ c4) ▸
       at 0 5 (Sb⁻0-1-32-4 ∷ []) (refl) ▸ done


-- nat 3 BOXd(3;02): 2 steps
lem-nat-3-BOXd⟨3·02⟩ : WsL → ⟪ (Sw34 ∷ Bx⁻3-02 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻4-02 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨3·02⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx⁻3-02 ∷ []) (Bx⁻4-02 ∷ Sw34 ∷ [])
  b0 = at 0 2 (Bx⁻3-02 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑ • CZ • Swap ↑) (Swap))) ▸
       at 0 1 (Bx⁻4-02 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 3 BOXd(0;312): 8 steps
lem-nat-3-BOXd⟨0·312⟩ : WsL → ⟪ (Sw34 ∷ Bx⁻0-312 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-412 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨0·312⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx⁻0-312 ∷ []) (Bx⁻0-412 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx⁻3-02 ∷ CCZ013 ∷ Toff013 ∷ Bx⁻3-02 ∷ Toff013 ∷ CCZ013 ∷ []) (refl) ▸
       at 0 2 (Bx⁻4-02 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨3·02⟩ c4) ▸
       at 1 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4) ▸
       at 2 2 (Toff014 ∷ Sw34 ∷ []) (lem-nat-3-TOFF013 c4) ▸
       at 3 2 (Bx⁻4-02 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨3·02⟩ c4) ▸
       at 4 2 (Toff014 ∷ Sw34 ∷ []) (lem-nat-3-TOFF013 c4) ▸
       at 5 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4) ▸
       at 0 6 (Bx⁻0-412 ∷ []) (refl) ▸ done


-- nat 3 BOXd(3;0412): 8 steps
lem-nat-3-BOXd⟨3·0412⟩ : WsL → ⟪ (Sw34 ∷ Bx⁻3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻4-0312 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨3·0412⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx⁻3-0412 ∷ []) (Bx⁻4-0312 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx⁻0-312 ∷ CCZ034 ∷ Toff304 ∷ Bx⁻0-312 ∷ Toff304 ∷ CCZ034 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-412 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨0·312⟩ c4) ▸
       at 1 2 (CCZ034 ∷ Sw34 ∷ []) (lem-nat-3-CCZ034 c4) ▸
       at 2 2 (Toff403 ∷ Sw34 ∷ []) (lem-nat-3-TOFF304 c4) ▸
       at 3 2 (Bx⁻0-412 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨0·312⟩ c4) ▸
       at 4 2 (Toff403 ∷ Sw34 ∷ []) (lem-nat-3-TOFF304 c4) ▸
       at 5 2 (CCZ034 ∷ Sw34 ∷ []) (lem-nat-3-CCZ034 c4) ▸
       at 0 6 (Bx⁻4-0312 ∷ []) (refl) ▸ done


-- nat 3 SBOXd(3;0;41;2): 7 steps
lem-nat-3-SBOXd⟨3·0·41·2⟩ : WsL → ⟪ (Sw34 ∷ Sb⁻3-0-41-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻4-0-31-2 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨3·0·41·2⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb⁻3-0-41-2 ∷ []) (Sb⁻4-0-31-2 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ Toff214 ∷ Bx⁻3-0412 ∷ []) (refl) ▸
       at 0 2 (Sb4-0-2-1 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨3·0·2·1⟩ c4) ▸
       at 1 2 (Toff213 ∷ Sw34 ∷ []) (lem-nat-3-TOFF214 c4) ▸
       at 2 2 (Sb⁻4-0-2-1 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨3·0·2·1⟩ c4) ▸
       at 3 2 (Toff213 ∷ Sw34 ∷ []) (lem-nat-3-TOFF214 c4) ▸
       at 4 2 (Bx⁻4-0312 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨3·0412⟩ c4) ▸
       at 0 5 (Sb⁻4-0-31-2 ∷ []) (refl) ▸ done


-- nat 1 BOXd(4;02): 3 steps
lem-nat-1-BOXd⟨4·02⟩ : WsL → ⟪ (Sw12 ∷ Bx⁻4-02 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻4-01 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨4·02⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻4-02 ∷ []) (Bx⁻4-01 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ02 ∷ []) (refl) ▸
       at 0 2 (CZ01 ∷ Sw12 ∷ []) (lem-nat-1-CZ02 c4) ▸
       at 0 1 (Bx⁻4-01 ∷ []) (refl) ▸ done


-- nat 1 BOXd(0;412): 8 steps
lem-nat-1-BOXd⟨0·412⟩ : WsL → ⟪ (Sw12 ∷ Bx⁻0-412 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-421 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨0·412⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻0-412 ∷ []) (Bx⁻0-421 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx⁻4-02 ∷ CCZ014 ∷ Toff014 ∷ Bx⁻4-02 ∷ Toff014 ∷ CCZ014 ∷ []) (refl) ▸
       at 0 2 (Bx⁻4-01 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨4·02⟩ c4) ▸
       at 1 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 2 2 (Toff024 ∷ Sw12 ∷ []) (lem-nat-1-TOFF014 c4) ▸
       at 3 2 (Bx⁻4-01 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨4·02⟩ c4) ▸
       at 4 2 (Toff024 ∷ Sw12 ∷ []) (lem-nat-1-TOFF014 c4) ▸
       at 5 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 0 6 (Bx⁻0-421 ∷ []) (refl) ▸ done


-- nat 1 BOXd(4;0312): 8 steps
lem-nat-1-BOXd⟨4·0312⟩ : WsL → ⟪ (Sw12 ∷ Bx⁻4-0312 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻4-0321 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨4·0312⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻4-0312 ∷ []) (Bx⁻4-0321 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx⁻0-412 ∷ CCZ034 ∷ Toff403 ∷ Bx⁻0-412 ∷ Toff403 ∷ CCZ034 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-421 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨0·412⟩ c4) ▸
       at 1 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 2 2 (Toff403 ∷ Sw12 ∷ []) (lem-nat-1-TOFF403 c4) ▸
       at 3 2 (Bx⁻0-421 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨0·412⟩ c4) ▸
       at 4 2 (Toff403 ∷ Sw12 ∷ []) (lem-nat-1-TOFF403 c4) ▸
       at 5 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 0 6 (Bx⁻4-0321 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(4;0;31;2): 7 steps
lem-nat-1-SBOXd⟨4·0·31·2⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻4-0-31-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻4-0-32-1 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨4·0·31·2⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻4-0-31-2 ∷ []) (Sb⁻4-0-32-1 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sb4-0-2-1 ∷ Toff213 ∷ Sb⁻4-0-2-1 ∷ Toff213 ∷ Bx⁻4-0312 ∷ []) (refl) ▸
       at 0 2 (Sb4-0-1-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨4·0·2·1⟩ c4) ▸
       at 1 2 (Toff123 ∷ Sw12 ∷ []) (wl0112 c4) ▸
       at 2 2 (Sb⁻4-0-1-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨4·0·2·1⟩ c4) ▸
       at 3 2 (Toff123 ∷ Sw12 ∷ []) (wl0112 c4) ▸
       at 4 2 (Bx⁻4-0321 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨4·0312⟩ c4) ▸
       at 0 5 (Sb⁻4-0-32-1 ∷ []) (refl) ▸ done


-- nat 2 BOXd(0;421): 8 steps
lem-nat-2-BOXd⟨0·421⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻0-421 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-431 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨0·421⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻0-421 ∷ []) (Bx⁻0-431 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx⁻4-01 ∷ CCZ024 ∷ Toff024 ∷ Bx⁻4-01 ∷ Toff024 ∷ CCZ024 ∷ []) (refl) ▸
       at 0 2 (Bx⁻4-01 ∷ Sw23 ∷ []) (sym (c₂ (CZ) (Swap))) ▸
       at 1 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 2 2 (Toff034 ∷ Sw23 ∷ []) (lem-nat-2-TOFF024 c4) ▸
       at 3 2 (Bx⁻4-01 ∷ Sw23 ∷ []) (sym (c₂ (CZ) (Swap))) ▸
       at 4 2 (Toff034 ∷ Sw23 ∷ []) (lem-nat-2-TOFF024 c4) ▸
       at 5 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 0 6 (Bx⁻0-431 ∷ []) (refl) ▸ done


-- nat 2 BOXd(4;0321): 8 steps
lem-nat-2-BOXd⟨4·0321⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻4-0321 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻4-0231 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨4·0321⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻4-0321 ∷ []) (Bx⁻4-0231 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx⁻0-421 ∷ CCZ034 ∷ Toff403 ∷ Bx⁻0-421 ∷ Toff403 ∷ CCZ034 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-431 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·421⟩ c4) ▸
       at 1 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 2 2 (Toff402 ∷ Sw23 ∷ []) (lem-nat-2-TOFF403 c4) ▸
       at 3 2 (Bx⁻0-431 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·421⟩ c4) ▸
       at 4 2 (Toff402 ∷ Sw23 ∷ []) (lem-nat-2-TOFF403 c4) ▸
       at 5 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 0 6 (Bx⁻4-0231 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(4;0;32;1): 7 steps
lem-nat-2-SBOXd⟨4·0·32·1⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻4-0-32-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻4-0-23-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨4·0·32·1⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻4-0-32-1 ∷ []) (Sb⁻4-0-23-1 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sb4-0-1-2 ∷ Toff123 ∷ Sb⁻4-0-1-2 ∷ Toff123 ∷ Bx⁻4-0321 ∷ []) (refl) ▸
       at 0 2 (Sb4-0-1-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨4·0·1·2⟩ c4) ▸
       at 1 2 (Toff123 ∷ Sw23 ∷ []) (wl0114 c4) ▸
       at 2 2 (Sb⁻4-0-1-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨4·0·1·2⟩ c4) ▸
       at 3 2 (Toff123 ∷ Sw23 ∷ []) (wl0114 c4) ▸
       at 4 2 (Bx⁻4-0231 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨4·0321⟩ c4) ▸
       at 0 5 (Sb⁻4-0-23-1 ∷ []) (refl) ▸ done


-- nat 0 BOXd(4;01): 3 steps
lem-nat-0-BOXd⟨4·01⟩ : WsL → ⟪ (Sw01 ∷ Bx⁻4-01 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻4-10 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨4·01⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻4-01 ∷ []) (Bx⁻4-10 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CZ01 ∷ []) (refl) ▸
       at 0 2 (CZ01 ∷ Sw01 ∷ []) (sym (wl0130 c4)) ▸
       at 0 1 (Bx⁻4-10 ∷ []) (refl) ▸ done


-- nat 0 BOXd(0;431): 8 steps
lem-nat-0-BOXd⟨0·431⟩ : WsL → ⟪ (Sw01 ∷ Bx⁻0-431 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-430 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨0·431⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻0-431 ∷ []) (Bx⁻1-430 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx⁻4-01 ∷ CCZ034 ∷ Toff034 ∷ Bx⁻4-01 ∷ Toff034 ∷ CCZ034 ∷ []) (refl) ▸
       at 0 2 (Bx⁻4-10 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨4·01⟩ c4) ▸
       at 1 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4) ▸
       at 2 2 (Toff134 ∷ Sw01 ∷ []) (lem-nat-0-TOFF034 c4) ▸
       at 3 2 (Bx⁻4-10 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨4·01⟩ c4) ▸
       at 4 2 (Toff134 ∷ Sw01 ∷ []) (lem-nat-0-TOFF034 c4) ▸
       at 5 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4) ▸
       at 0 6 (Bx⁻1-430 ∷ []) (refl) ▸ done


-- nat 0 BOXd(4;0231): 8 steps
lem-nat-0-BOXd⟨4·0231⟩ : WsL → ⟪ (Sw01 ∷ Bx⁻4-0231 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻4-1230 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨4·0231⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻4-0231 ∷ []) (Bx⁻4-1230 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx⁻0-431 ∷ CCZ024 ∷ Toff402 ∷ Bx⁻0-431 ∷ Toff402 ∷ CCZ024 ∷ []) (refl) ▸
       at 0 2 (Bx⁻1-430 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨0·431⟩ c4) ▸
       at 1 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 2 2 (Toff412 ∷ Sw01 ∷ []) (lem-nat-0-TOFF402 c4) ▸
       at 3 2 (Bx⁻1-430 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨0·431⟩ c4) ▸
       at 4 2 (Toff412 ∷ Sw01 ∷ []) (lem-nat-0-TOFF402 c4) ▸
       at 5 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 0 6 (Bx⁻4-1230 ∷ []) (refl) ▸ done


-- nat 0 SBOXd(4;0;23;1): 7 steps
lem-nat-0-SBOXd⟨4·0·23·1⟩ : WsL → ⟪ (Sw01 ∷ Sb⁻4-0-23-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻4-1-23-0 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨4·0·23·1⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻4-0-23-1 ∷ []) (Sb⁻4-1-23-0 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Sb4-0-1-3 ∷ Toff123 ∷ Sb⁻4-0-1-3 ∷ Toff123 ∷ Bx⁻4-0231 ∷ []) (refl) ▸
       at 0 2 (Sb4-1-0-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨4·0·1·3⟩ c4) ▸
       at 1 2 (Toff023 ∷ Sw01 ∷ []) (wl0053 c4) ▸
       at 2 2 (Sb⁻4-1-0-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨4·0·1·3⟩ c4) ▸
       at 3 2 (Toff023 ∷ Sw01 ∷ []) (wl0053 c4) ▸
       at 4 2 (Bx⁻4-1230 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨4·0231⟩ c4) ▸
       at 0 5 (Sb⁻4-1-23-0 ∷ []) (refl) ▸ done


-- nat 0 BOXd(0;134): 8 steps
lem-nat-0-BOXd⟨0·134⟩ : WsL → ⟪ (Sw01 ∷ Bx⁻0-134 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-034 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨0·134⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻0-134 ∷ []) (Bx⁻1-034 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx⁻1-04 ∷ CCZ013 ∷ Toff013 ∷ Bx⁻1-04 ∷ Toff013 ∷ CCZ013 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-14 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨1·04⟩ c4) ▸
       at 1 2 (CCZ013 ∷ Sw01 ∷ []) (sym (wl0100 c4)) ▸
       at 2 2 (Toff103 ∷ Sw01 ∷ []) (wl0101 c4) ▸
       at 3 2 (Bx⁻0-14 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨1·04⟩ c4) ▸
       at 4 2 (Toff103 ∷ Sw01 ∷ []) (wl0101 c4) ▸
       at 5 2 (CCZ013 ∷ Sw01 ∷ []) (sym (wl0100 c4)) ▸
       at 0 6 (Bx⁻1-034 ∷ []) (refl) ▸ done


-- nat 0 BOXd(1;0234): 8 steps
lem-nat-0-BOXd⟨1·0234⟩ : WsL → ⟪ (Sw01 ∷ Bx⁻1-0234 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-1234 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨1·0234⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻1-0234 ∷ []) (Bx⁻0-1234 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx⁻0-134 ∷ CCZ012 ∷ Toff102 ∷ Bx⁻0-134 ∷ Toff102 ∷ CCZ012 ∷ []) (refl) ▸
       at 0 2 (Bx⁻1-034 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨0·134⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw01 ∷ []) (sym (wl0096 c4)) ▸
       at 2 2 (Toff012 ∷ Sw01 ∷ []) (wl0097 c4) ▸
       at 3 2 (Bx⁻1-034 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨0·134⟩ c4) ▸
       at 4 2 (Toff012 ∷ Sw01 ∷ []) (wl0097 c4) ▸
       at 5 2 (CCZ012 ∷ Sw01 ∷ []) (sym (wl0096 c4)) ▸
       at 0 6 (Bx⁻0-1234 ∷ []) (refl) ▸ done


-- nat 1 BOXd(0;134): 8 steps
lem-nat-1-BOXd⟨0·134⟩ : WsL → ⟪ (Sw12 ∷ Bx⁻0-134 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-234 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨0·134⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻0-134 ∷ []) (Bx⁻0-234 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx⁻1-04 ∷ CCZ013 ∷ Toff013 ∷ Bx⁻1-04 ∷ Toff013 ∷ CCZ013 ∷ []) (refl) ▸
       at 0 2 (Bx⁻2-04 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨1·04⟩ c4) ▸
       at 1 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 2 2 (Toff023 ∷ Sw12 ∷ []) (lem-nat-1-TOFF013 c4) ▸
       at 3 2 (Bx⁻2-04 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨1·04⟩ c4) ▸
       at 4 2 (Toff023 ∷ Sw12 ∷ []) (lem-nat-1-TOFF013 c4) ▸
       at 5 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 0 6 (Bx⁻0-234 ∷ []) (refl) ▸ done


-- nat 1 BOXd(1;0234): 8 steps
lem-nat-1-BOXd⟨1·0234⟩ : WsL → ⟪ (Sw12 ∷ Bx⁻1-0234 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-0134 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨1·0234⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻1-0234 ∷ []) (Bx⁻2-0134 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx⁻0-134 ∷ CCZ012 ∷ Toff102 ∷ Bx⁻0-134 ∷ Toff102 ∷ CCZ012 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-234 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨0·134⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw12 ∷ []) (sym (wl0037 c4)) ▸
       at 2 2 (Toff201 ∷ Sw12 ∷ []) (wl0047 c4) ▸
       at 3 2 (Bx⁻0-234 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨0·134⟩ c4) ▸
       at 4 2 (Toff201 ∷ Sw12 ∷ []) (wl0047 c4) ▸
       at 5 2 (CCZ012 ∷ Sw12 ∷ []) (sym (wl0037 c4)) ▸
       at 0 6 (Bx⁻2-0134 ∷ []) (refl) ▸ done


-- nat 2 BOXd(3;04): 3 steps
lem-nat-2-BOXd⟨3·04⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻3-04 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-04 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨3·04⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻3-04 ∷ []) (Bx⁻2-04 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ04 ∷ []) (refl) ▸
       at 0 2 (CZ04 ∷ Sw23 ∷ []) (lem-nat-2-CZ04 c4) ▸
       at 0 1 (Bx⁻2-04 ∷ []) (refl) ▸ done


-- nat 2 BOXd(0;324): 8 steps
lem-nat-2-BOXd⟨0·324⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻0-324 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-234 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨0·324⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻0-324 ∷ []) (Bx⁻0-234 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx⁻3-04 ∷ CCZ023 ∷ Toff023 ∷ Bx⁻3-04 ∷ Toff023 ∷ CCZ023 ∷ []) (refl) ▸
       at 0 2 (Bx⁻2-04 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨3·04⟩ c4) ▸
       at 1 2 (CCZ023 ∷ Sw23 ∷ []) (sym (wl0065 c4)) ▸
       at 2 2 (Toff023 ∷ Sw23 ∷ []) (wl0093 c4) ▸
       at 3 2 (Bx⁻2-04 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨3·04⟩ c4) ▸
       at 4 2 (Toff023 ∷ Sw23 ∷ []) (wl0093 c4) ▸
       at 5 2 (CCZ023 ∷ Sw23 ∷ []) (sym (wl0065 c4)) ▸
       at 0 6 (Bx⁻0-234 ∷ []) (refl) ▸ done


-- nat 2 BOXd(3;0124): 8 steps
lem-nat-2-BOXd⟨3·0124⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻3-0124 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-0134 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨3·0124⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻3-0124 ∷ []) (Bx⁻2-0134 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx⁻0-324 ∷ CCZ013 ∷ Toff301 ∷ Bx⁻0-324 ∷ Toff301 ∷ CCZ013 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-234 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·324⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 2 2 (Toff201 ∷ Sw23 ∷ []) (lem-nat-2-TOFF301 c4) ▸
       at 3 2 (Bx⁻0-234 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·324⟩ c4) ▸
       at 4 2 (Toff201 ∷ Sw23 ∷ []) (lem-nat-2-TOFF301 c4) ▸
       at 5 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 0 6 (Bx⁻2-0134 ∷ []) (refl) ▸ done


-- nat 2 BOXd(2;04): 3 steps
lem-nat-2-BOXd⟨2·04⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻2-04 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻3-04 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨2·04⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻2-04 ∷ []) (Bx⁻3-04 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ04 ∷ []) (refl) ▸
       at 0 2 (CZ04 ∷ Sw23 ∷ []) (lem-nat-2-CZ04 c4) ▸
       at 0 1 (Bx⁻3-04 ∷ []) (refl) ▸ done


-- nat 2 BOXd(0;234): 8 steps
lem-nat-2-BOXd⟨0·234⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻0-234 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-324 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨0·234⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻0-234 ∷ []) (Bx⁻0-324 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx⁻2-04 ∷ CCZ023 ∷ Toff023 ∷ Bx⁻2-04 ∷ Toff023 ∷ CCZ023 ∷ []) (refl) ▸
       at 0 2 (Bx⁻3-04 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨2·04⟩ c4) ▸
       at 1 2 (CCZ023 ∷ Sw23 ∷ []) (sym (wl0065 c4)) ▸
       at 2 2 (Toff023 ∷ Sw23 ∷ []) (wl0093 c4) ▸
       at 3 2 (Bx⁻3-04 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨2·04⟩ c4) ▸
       at 4 2 (Toff023 ∷ Sw23 ∷ []) (wl0093 c4) ▸
       at 5 2 (CCZ023 ∷ Sw23 ∷ []) (sym (wl0065 c4)) ▸
       at 0 6 (Bx⁻0-324 ∷ []) (refl) ▸ done


-- nat 2 BOXd(2;0134): 8 steps
lem-nat-2-BOXd⟨2·0134⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻2-0134 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻3-0124 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨2·0134⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻2-0134 ∷ []) (Bx⁻3-0124 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx⁻0-234 ∷ CCZ012 ∷ Toff201 ∷ Bx⁻0-234 ∷ Toff201 ∷ CCZ012 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-324 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·234⟩ c4) ▸
       at 1 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 2 2 (Toff301 ∷ Sw23 ∷ []) (lem-nat-2-TOFF201 c4) ▸
       at 3 2 (Bx⁻0-324 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·234⟩ c4) ▸
       at 4 2 (Toff301 ∷ Sw23 ∷ []) (lem-nat-2-TOFF201 c4) ▸
       at 5 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 0 6 (Bx⁻3-0124 ∷ []) (refl) ▸ done


-- nat 3 BOXd(4;03): 3 steps
lem-nat-3-BOXd⟨4·03⟩ : WsL → ⟪ (Sw34 ∷ Bx⁻4-03 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻3-04 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨4·03⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx⁻4-03 ∷ []) (Bx⁻3-04 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CZ03 ∷ []) (refl) ▸
       at 0 2 (CZ04 ∷ Sw34 ∷ []) (lem-nat-3-CZ03 c4) ▸
       at 0 1 (Bx⁻3-04 ∷ []) (refl) ▸ done


-- nat 3 BOXd(0;423): 8 steps
lem-nat-3-BOXd⟨0·423⟩ : WsL → ⟪ (Sw34 ∷ Bx⁻0-423 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-324 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨0·423⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx⁻0-423 ∷ []) (Bx⁻0-324 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx⁻4-03 ∷ CCZ024 ∷ Toff024 ∷ Bx⁻4-03 ∷ Toff024 ∷ CCZ024 ∷ []) (refl) ▸
       at 0 2 (Bx⁻3-04 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨4·03⟩ c4) ▸
       at 1 2 (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 c4) ▸
       at 2 2 (Toff023 ∷ Sw34 ∷ []) (lem-nat-3-TOFF024 c4) ▸
       at 3 2 (Bx⁻3-04 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨4·03⟩ c4) ▸
       at 4 2 (Toff023 ∷ Sw34 ∷ []) (lem-nat-3-TOFF024 c4) ▸
       at 5 2 (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 c4) ▸
       at 0 6 (Bx⁻0-324 ∷ []) (refl) ▸ done


-- nat 3 BOXd(4;0123): 8 steps
lem-nat-3-BOXd⟨4·0123⟩ : WsL → ⟪ (Sw34 ∷ Bx⁻4-0123 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻3-0124 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨4·0123⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx⁻4-0123 ∷ []) (Bx⁻3-0124 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx⁻0-423 ∷ CCZ014 ∷ Toff401 ∷ Bx⁻0-423 ∷ Toff401 ∷ CCZ014 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-324 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨0·423⟩ c4) ▸
       at 1 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4) ▸
       at 2 2 (Toff301 ∷ Sw34 ∷ []) (lem-nat-3-TOFF401 c4) ▸
       at 3 2 (Bx⁻0-324 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨0·423⟩ c4) ▸
       at 4 2 (Toff301 ∷ Sw34 ∷ []) (lem-nat-3-TOFF401 c4) ▸
       at 5 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4) ▸
       at 0 6 (Bx⁻3-0124 ∷ []) (refl) ▸ done


-- nat 3 BOXd(3;04): 3 steps
lem-nat-3-BOXd⟨3·04⟩ : WsL → ⟪ (Sw34 ∷ Bx⁻3-04 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻4-03 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨3·04⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx⁻3-04 ∷ []) (Bx⁻4-03 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CZ04 ∷ []) (refl) ▸
       at 0 2 (CZ03 ∷ Sw34 ∷ []) (lem-nat-3-CZ04 c4) ▸
       at 0 1 (Bx⁻4-03 ∷ []) (refl) ▸ done


-- nat 3 BOXd(0;324): 8 steps
lem-nat-3-BOXd⟨0·324⟩ : WsL → ⟪ (Sw34 ∷ Bx⁻0-324 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-423 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨0·324⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx⁻0-324 ∷ []) (Bx⁻0-423 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx⁻3-04 ∷ CCZ023 ∷ Toff023 ∷ Bx⁻3-04 ∷ Toff023 ∷ CCZ023 ∷ []) (refl) ▸
       at 0 2 (Bx⁻4-03 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨3·04⟩ c4) ▸
       at 1 2 (CCZ024 ∷ Sw34 ∷ []) (lem-nat-3-CCZ023 c4) ▸
       at 2 2 (Toff024 ∷ Sw34 ∷ []) (lem-nat-3-TOFF023 c4) ▸
       at 3 2 (Bx⁻4-03 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨3·04⟩ c4) ▸
       at 4 2 (Toff024 ∷ Sw34 ∷ []) (lem-nat-3-TOFF023 c4) ▸
       at 5 2 (CCZ024 ∷ Sw34 ∷ []) (lem-nat-3-CCZ023 c4) ▸
       at 0 6 (Bx⁻0-423 ∷ []) (refl) ▸ done


-- nat 3 BOXd(3;0124): 8 steps
lem-nat-3-BOXd⟨3·0124⟩ : WsL → ⟪ (Sw34 ∷ Bx⁻3-0124 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻4-0123 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨3·0124⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx⁻3-0124 ∷ []) (Bx⁻4-0123 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx⁻0-324 ∷ CCZ013 ∷ Toff301 ∷ Bx⁻0-324 ∷ Toff301 ∷ CCZ013 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-423 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨0·324⟩ c4) ▸
       at 1 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4) ▸
       at 2 2 (Toff401 ∷ Sw34 ∷ []) (lem-nat-3-TOFF301 c4) ▸
       at 3 2 (Bx⁻0-423 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨0·324⟩ c4) ▸
       at 4 2 (Toff401 ∷ Sw34 ∷ []) (lem-nat-3-TOFF301 c4) ▸
       at 5 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4) ▸
       at 0 6 (Bx⁻4-0123 ∷ []) (refl) ▸ done


-- nat 2 BOXd(4;02): 3 steps
lem-nat-2-BOXd⟨4·02⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻4-02 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻4-03 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨4·02⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻4-02 ∷ []) (Bx⁻4-03 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ02 ∷ []) (refl) ▸
       at 0 2 (CZ03 ∷ Sw23 ∷ []) (lem-nat-2-CZ02 c4) ▸
       at 0 1 (Bx⁻4-03 ∷ []) (refl) ▸ done


-- nat 2 BOXd(0;432): 8 steps
lem-nat-2-BOXd⟨0·432⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻0-432 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-423 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨0·432⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻0-432 ∷ []) (Bx⁻0-423 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx⁻4-02 ∷ CCZ034 ∷ Toff034 ∷ Bx⁻4-02 ∷ Toff034 ∷ CCZ034 ∷ []) (refl) ▸
       at 0 2 (Bx⁻4-03 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨4·02⟩ c4) ▸
       at 1 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 2 2 (Toff024 ∷ Sw23 ∷ []) (lem-nat-2-TOFF034 c4) ▸
       at 3 2 (Bx⁻4-03 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨4·02⟩ c4) ▸
       at 4 2 (Toff024 ∷ Sw23 ∷ []) (lem-nat-2-TOFF034 c4) ▸
       at 5 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 0 6 (Bx⁻0-423 ∷ []) (refl) ▸ done


-- nat 2 BOXd(4;0132): 8 steps
lem-nat-2-BOXd⟨4·0132⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻4-0132 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻4-0123 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨4·0132⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻4-0132 ∷ []) (Bx⁻4-0123 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx⁻0-432 ∷ CCZ014 ∷ Toff401 ∷ Bx⁻0-432 ∷ Toff401 ∷ CCZ014 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-423 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·432⟩ c4) ▸
       at 1 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 2 2 (Toff401 ∷ Sw23 ∷ []) (lem-nat-2-TOFF401 c4) ▸
       at 3 2 (Bx⁻0-423 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·432⟩ c4) ▸
       at 4 2 (Toff401 ∷ Sw23 ∷ []) (lem-nat-2-TOFF401 c4) ▸
       at 5 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 0 6 (Bx⁻4-0123 ∷ []) (refl) ▸ done


-- nat 2 BOXd(4;03): 3 steps
lem-nat-2-BOXd⟨4·03⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻4-03 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻4-02 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨4·03⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻4-03 ∷ []) (Bx⁻4-02 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ03 ∷ []) (refl) ▸
       at 0 2 (CZ02 ∷ Sw23 ∷ []) (lem-nat-2-CZ03 c4) ▸
       at 0 1 (Bx⁻4-02 ∷ []) (refl) ▸ done


-- nat 2 BOXd(0;423): 8 steps
lem-nat-2-BOXd⟨0·423⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻0-423 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-432 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨0·423⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻0-423 ∷ []) (Bx⁻0-432 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx⁻4-03 ∷ CCZ024 ∷ Toff024 ∷ Bx⁻4-03 ∷ Toff024 ∷ CCZ024 ∷ []) (refl) ▸
       at 0 2 (Bx⁻4-02 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨4·03⟩ c4) ▸
       at 1 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 2 2 (Toff034 ∷ Sw23 ∷ []) (lem-nat-2-TOFF024 c4) ▸
       at 3 2 (Bx⁻4-02 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨4·03⟩ c4) ▸
       at 4 2 (Toff034 ∷ Sw23 ∷ []) (lem-nat-2-TOFF024 c4) ▸
       at 5 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 0 6 (Bx⁻0-432 ∷ []) (refl) ▸ done


-- nat 2 BOXd(4;0123): 8 steps
lem-nat-2-BOXd⟨4·0123⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻4-0123 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻4-0132 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨4·0123⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻4-0123 ∷ []) (Bx⁻4-0132 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx⁻0-423 ∷ CCZ014 ∷ Toff401 ∷ Bx⁻0-423 ∷ Toff401 ∷ CCZ014 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-432 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·423⟩ c4) ▸
       at 1 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 2 2 (Toff401 ∷ Sw23 ∷ []) (lem-nat-2-TOFF401 c4) ▸
       at 3 2 (Bx⁻0-432 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·423⟩ c4) ▸
       at 4 2 (Toff401 ∷ Sw23 ∷ []) (lem-nat-2-TOFF401 c4) ▸
       at 5 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 0 6 (Bx⁻4-0132 ∷ []) (refl) ▸ done


-- nat 1 BOXd(4;01): 3 steps
lem-nat-1-BOXd⟨4·01⟩ : WsL → ⟪ (Sw12 ∷ Bx⁻4-01 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻4-02 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨4·01⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻4-01 ∷ []) (Bx⁻4-02 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ01 ∷ []) (refl) ▸
       at 0 2 (CZ02 ∷ Sw12 ∷ []) (lem-nat-1-CZ01 c4) ▸
       at 0 1 (Bx⁻4-02 ∷ []) (refl) ▸ done


-- nat 1 BOXd(0;431): 8 steps
lem-nat-1-BOXd⟨0·431⟩ : WsL → ⟪ (Sw12 ∷ Bx⁻0-431 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-432 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨0·431⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻0-431 ∷ []) (Bx⁻0-432 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx⁻4-01 ∷ CCZ034 ∷ Toff034 ∷ Bx⁻4-01 ∷ Toff034 ∷ CCZ034 ∷ []) (refl) ▸
       at 0 2 (Bx⁻4-02 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨4·01⟩ c4) ▸
       at 1 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 2 2 (Toff034 ∷ Sw12 ∷ []) (lem-nat-1-TOFF034 c4) ▸
       at 3 2 (Bx⁻4-02 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨4·01⟩ c4) ▸
       at 4 2 (Toff034 ∷ Sw12 ∷ []) (lem-nat-1-TOFF034 c4) ▸
       at 5 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 0 6 (Bx⁻0-432 ∷ []) (refl) ▸ done


-- nat 1 BOXd(4;0231): 8 steps
lem-nat-1-BOXd⟨4·0231⟩ : WsL → ⟪ (Sw12 ∷ Bx⁻4-0231 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻4-0132 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨4·0231⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻4-0231 ∷ []) (Bx⁻4-0132 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx⁻0-431 ∷ CCZ024 ∷ Toff402 ∷ Bx⁻0-431 ∷ Toff402 ∷ CCZ024 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-432 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨0·431⟩ c4) ▸
       at 1 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 2 2 (Toff401 ∷ Sw12 ∷ []) (lem-nat-1-TOFF402 c4) ▸
       at 3 2 (Bx⁻0-432 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨0·431⟩ c4) ▸
       at 4 2 (Toff401 ∷ Sw12 ∷ []) (lem-nat-1-TOFF402 c4) ▸
       at 5 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 0 6 (Bx⁻4-0132 ∷ []) (refl) ▸ done


-- nat 1 BOXd(0;432): 8 steps
lem-nat-1-BOXd⟨0·432⟩ : WsL → ⟪ (Sw12 ∷ Bx⁻0-432 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-431 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨0·432⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻0-432 ∷ []) (Bx⁻0-431 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx⁻4-02 ∷ CCZ034 ∷ Toff034 ∷ Bx⁻4-02 ∷ Toff034 ∷ CCZ034 ∷ []) (refl) ▸
       at 0 2 (Bx⁻4-01 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨4·02⟩ c4) ▸
       at 1 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 2 2 (Toff034 ∷ Sw12 ∷ []) (lem-nat-1-TOFF034 c4) ▸
       at 3 2 (Bx⁻4-01 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨4·02⟩ c4) ▸
       at 4 2 (Toff034 ∷ Sw12 ∷ []) (lem-nat-1-TOFF034 c4) ▸
       at 5 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 0 6 (Bx⁻0-431 ∷ []) (refl) ▸ done


-- nat 1 BOXd(4;0132): 8 steps
lem-nat-1-BOXd⟨4·0132⟩ : WsL → ⟪ (Sw12 ∷ Bx⁻4-0132 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻4-0231 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨4·0132⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻4-0132 ∷ []) (Bx⁻4-0231 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx⁻0-432 ∷ CCZ014 ∷ Toff401 ∷ Bx⁻0-432 ∷ Toff401 ∷ CCZ014 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-431 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨0·432⟩ c4) ▸
       at 1 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 2 2 (Toff402 ∷ Sw12 ∷ []) (lem-nat-1-TOFF401 c4) ▸
       at 3 2 (Bx⁻0-431 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨0·432⟩ c4) ▸
       at 4 2 (Toff402 ∷ Sw12 ∷ []) (lem-nat-1-TOFF401 c4) ▸
       at 5 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 0 6 (Bx⁻4-0231 ∷ []) (refl) ▸ done


-- nat 0 BOXd(4;10): 3 steps
lem-nat-0-BOXd⟨4·10⟩ : WsL → ⟪ (Sw01 ∷ Bx⁻4-10 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻4-01 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨4·10⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻4-10 ∷ []) (Bx⁻4-01 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CZ01 ∷ []) (refl) ▸
       at 0 2 (CZ01 ∷ Sw01 ∷ []) (sym (wl0130 c4)) ▸
       at 0 1 (Bx⁻4-01 ∷ []) (refl) ▸ done


-- nat 0 BOXd(1;430): 8 steps
lem-nat-0-BOXd⟨1·430⟩ : WsL → ⟪ (Sw01 ∷ Bx⁻1-430 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-431 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨1·430⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻1-430 ∷ []) (Bx⁻0-431 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx⁻4-10 ∷ CCZ134 ∷ Toff134 ∷ Bx⁻4-10 ∷ Toff134 ∷ CCZ134 ∷ []) (refl) ▸
       at 0 2 (Bx⁻4-01 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨4·10⟩ c4) ▸
       at 1 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 2 2 (Toff034 ∷ Sw01 ∷ []) (lem-nat-0-TOFF134 c4) ▸
       at 3 2 (Bx⁻4-01 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨4·10⟩ c4) ▸
       at 4 2 (Toff034 ∷ Sw01 ∷ []) (lem-nat-0-TOFF134 c4) ▸
       at 5 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 0 6 (Bx⁻0-431 ∷ []) (refl) ▸ done


-- nat 0 BOXd(4;1230): 8 steps
lem-nat-0-BOXd⟨4·1230⟩ : WsL → ⟪ (Sw01 ∷ Bx⁻4-1230 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻4-0231 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨4·1230⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻4-1230 ∷ []) (Bx⁻4-0231 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx⁻1-430 ∷ CCZ124 ∷ Toff412 ∷ Bx⁻1-430 ∷ Toff412 ∷ CCZ124 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-431 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨1·430⟩ c4) ▸
       at 1 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 2 2 (Toff402 ∷ Sw01 ∷ []) (lem-nat-0-TOFF412 c4) ▸
       at 3 2 (Bx⁻0-431 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨1·430⟩ c4) ▸
       at 4 2 (Toff402 ∷ Sw01 ∷ []) (lem-nat-0-TOFF412 c4) ▸
       at 5 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 0 6 (Bx⁻4-0231 ∷ []) (refl) ▸ done


-- resp CSd14 at 2: 4 steps
lem-resp-CSd14-at-2 : WsL → ⟪ (CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CS24⁻ ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CSd14-at-2 c4 = run b0
  where
  b0 : Chain (CS14⁻ ∷ []) (Sw12 ∷ Sw01 ∷ CS24⁻ ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 0 2 (Sw12 ∷ CS24⁻ ∷ []) (wl0018 c4) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 c4)) ▸
       at 1 2 (Sw01 ∷ CS24⁻ ∷ []) (sym (c₂ (Swap) (Swap ↑ • (CS • CS • CS) • Swap ↑))) ▸ done


-- nat 2 CS03: 2 steps
lem-nat-2-CS03 : WsL → ⟪ (Sw23 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-CS03 c4 = run b0
  where
  b0 : Chain (Sw23 ∷ CS03 ∷ []) (CS02 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0006 c4) ▸ done


-- comm CCZ024 CX13: 11 steps
lem-comm-CCZ024-CX13 : WsL → ⟪ (CCZ024 ∷ CX13 ∷ []) ⟫ʷ ≈ ⟪ (CX13 ∷ CCZ024 ∷ []) ⟫ʷ
lem-comm-CCZ024-CX13 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ024 ∷ CX13 ∷ []) (Sw12 ∷ Sw34 ∷ Sw34 ∷ CX23 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ [])
  b0 = at 0 1 (Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX23 ∷ Sw12 ∷ []) (sym (wl0052 c4)) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 5 3 (CX24 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX34 ∷ Sw23 ∷ []) (sym (wl0051 c4)) ▸
       at 3 2 (CX34 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CX₀₁)) ▸
       at 2 2 (CX24 ∷ Sw23 ∷ []) (sym (wl0050 c4)) ▸
       at 2 1 (Sw34 ∷ CX23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw12 ∷ Sw34 ∷ Sw34 ∷ CX23 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) (CX13 ∷ CCZ024 ∷ [])
  b1 = at 1 2 [] (wl0007 c4) ▸
       at 0 2 (CX13 ∷ Sw12 ∷ []) (sym (wl0049 c4)) ▸
       at 1 7 (CCZ024 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp CSd03 at 1: 2 steps
lem-resp-CSd03-at-1 : WsL → ⟪ (CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CS13⁻ ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CSd03-at-1 c4 = run b0
  where
  b0 : Chain (CS03⁻ ∷ []) (Sw01 ∷ CS13⁻ ∷ Sw01 ∷ [])
  b0 = at 1 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 c4)) ▸
       at 0 2 (Sw01 ∷ CS13⁻ ∷ []) (wl0022 c4) ▸ done


-- resp CX13 at 2: 4 steps
lem-resp-CX13-at-2 : WsL → ⟪ (CX13 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CX23 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CX13-at-2 c4 = run b0
  where
  b0 : Chain (CX13 ∷ []) (Sw12 ∷ Sw01 ∷ CX23 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 0 2 (Sw12 ∷ CX23 ∷ []) (wl0049 c4) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 c4)) ▸
       at 1 2 (Sw01 ∷ CX23 ∷ []) (sym (c₂ (Swap) (CX₀₁))) ▸ done


-- nat 2 CSd03: 2 steps
lem-nat-2-CSd03 : WsL → ⟪ (Sw23 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-CSd03 c4 = run b0
  where
  b0 : Chain (Sw23 ∷ CS03⁻ ∷ []) (CS02⁻ ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0006 c4) ▸ done


-- resp CS24 at 3: 6 steps
lem-resp-CS24-at-3 : WsL → ⟪ (CS24 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ CS34 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-CS24-at-3 c4 = run b0
  where
  b0 : Chain (CS24 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ CS34 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 0 2 (Sw23 ∷ CS34 ∷ []) (wl0015 c4) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 1 2 (Sw12 ∷ CS34 ∷ []) (sym (c₃ (Swap ↑) (CS))) ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 c4)) ▸
       at 2 2 (Sw01 ∷ CS34 ∷ []) (sym (c₂ (Swap) (CS ↑))) ▸ done


-- comm CSd03 CCZ124: 9 steps
lem-comm-CSd03-CCZ124 : WsL → ⟪ (CS03⁻ ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-comm-CSd03-CCZ124 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CS03⁻ ∷ CCZ124 ∷ []) (CCZ124 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 0 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 4 3 (CCZ134 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CCZ234 ∷ Sw12 ∷ []) (sym (wl0084 c4)) ▸
       at 2 2 (CCZ234 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (CCZ)) ▸
       at 1 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0034 c4)) ▸
       at 1 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0006 c4) ▸ done

  b1 : Chain (CCZ124 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) (CCZ124 ∷ CS03⁻ ∷ [])
  b1 = at 1 5 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 2 SBOXd(0;1;3;2): 3 steps
lem-nat-2-SBOXd⟨0·1·3·2⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻0-1-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-2-3 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨0·1·3·2⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻0-1-3-2 ∷ []) (Sb⁻0-1-2-3 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS13⁻ ∷ []) (refl) ▸
       at 0 2 (CS12⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd13 c4) ▸
       at 0 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸ done


-- nat 2 BOX(1;023): 8 steps
lem-nat-2-BOX⟨1·023⟩ : WsL → ⟪ (Sw23 ∷ Bx1-023 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-032 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·023⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx1-023 ∷ []) (Bx1-032 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff102 ∷ Bx0-13 ∷ Toff102 ∷ CCZ012 ∷ Bx0-13 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 1 2 (Toff103 ∷ Sw23 ∷ []) (lem-nat-2-TOFF102 c4) ▸
       at 2 2 (Bx0-12 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·13⟩ c4) ▸
       at 3 2 (Toff103 ∷ Sw23 ∷ []) (lem-nat-2-TOFF102 c4) ▸
       at 4 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 5 2 (Bx0-12 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·13⟩ c4) ▸
       at 0 6 (Bx1-032 ∷ []) (refl) ▸ done


-- nat 2 BOX(0;1423): 8 steps
lem-nat-2-BOX⟨0·1423⟩ : WsL → ⟪ (Sw23 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1432 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·1423⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-1423 ∷ []) (Bx0-1432 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff014 ∷ Bx1-023 ∷ Toff014 ∷ CCZ014 ∷ Bx1-023 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 1 2 (Toff014 ∷ Sw23 ∷ []) (lem-nat-2-TOFF014 c4) ▸
       at 2 2 (Bx1-032 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·023⟩ c4) ▸
       at 3 2 (Toff014 ∷ Sw23 ∷ []) (lem-nat-2-TOFF014 c4) ▸
       at 4 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 5 2 (Bx1-032 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·023⟩ c4) ▸
       at 0 6 (Bx0-1432 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(0;1;2;3): 3 steps
lem-nat-2-SBOXd⟨0·1·2·3⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻0-1-2-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-3-2 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨0·1·2·3⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻0-1-2-3 ∷ []) (Sb⁻0-1-3-2 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS12⁻ ∷ []) (refl) ▸
       at 0 2 (CS13⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd12 c4) ▸
       at 0 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸ done


-- nat 2 SBOX(0;1;3;2): 3 steps
lem-nat-2-SBOX⟨0·1·3·2⟩ : WsL → ⟪ (Sw23 ∷ Sb0-1-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-2-3 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨0·1·3·2⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb0-1-3-2 ∷ []) (Sb0-1-2-3 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS13 ∷ []) (refl) ▸
       at 0 2 (CS12 ∷ Sw23 ∷ []) (lem-nat-2-CS13 c4) ▸
       at 0 1 (Sb0-1-2-3 ∷ []) (refl) ▸ done


-- nat 2 SBOX(0;1;2;3): 3 steps
lem-nat-2-SBOX⟨0·1·2·3⟩ : WsL → ⟪ (Sw23 ∷ Sb0-1-2-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-3-2 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨0·1·2·3⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb0-1-2-3 ∷ []) (Sb0-1-3-2 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS12 ∷ []) (refl) ▸
       at 0 2 (CS13 ∷ Sw23 ∷ []) (lem-nat-2-CS12 c4) ▸
       at 0 1 (Sb0-1-3-2 ∷ []) (refl) ▸ done


-- nat 0 BOX(1;34): 2 steps
lem-nat-0-BOX⟨1·34⟩ : WsL → ⟪ (Sw01 ∷ Bx1-34 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-34 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·34⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-34 ∷ []) (Bx0-34 ∷ Sw01 ∷ [])
  b0 = at 0 2 (Bx1-34 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑)) ▸
       at 0 1 (Bx0-34 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 BOX(3;124): 8 steps
lem-nat-0-BOX⟨3·124⟩ : WsL → ⟪ (Sw01 ∷ Bx3-124 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-024 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·124⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx3-124 ∷ []) (Bx3-024 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff312 ∷ Bx1-34 ∷ Toff312 ∷ CCZ123 ∷ Bx1-34 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw01 ∷ []) (sym (wl0003 c4)) ▸
       at 1 2 (Toff302 ∷ Sw01 ∷ []) (wl0110 c4) ▸
       at 2 2 (Bx0-34 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·34⟩ c4) ▸
       at 3 2 (Toff302 ∷ Sw01 ∷ []) (wl0110 c4) ▸
       at 4 2 (CCZ023 ∷ Sw01 ∷ []) (sym (wl0003 c4)) ▸
       at 5 2 (Bx0-34 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·34⟩ c4) ▸
       at 0 6 (Bx3-024 ∷ []) (refl) ▸ done


-- nat 0 BOX(1;3024): 8 steps
lem-nat-0-BOX⟨1·3024⟩ : WsL → ⟪ (Sw01 ∷ Bx1-3024 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3124 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·3024⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-3024 ∷ []) (Bx0-3124 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff103 ∷ Bx3-124 ∷ Toff103 ∷ CCZ013 ∷ Bx3-124 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw01 ∷ []) (sym (wl0100 c4)) ▸
       at 1 2 (Toff013 ∷ Sw01 ∷ []) (wl0102 c4) ▸
       at 2 2 (Bx3-024 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·124⟩ c4) ▸
       at 3 2 (Toff013 ∷ Sw01 ∷ []) (wl0102 c4) ▸
       at 4 2 (CCZ013 ∷ Sw01 ∷ []) (sym (wl0100 c4)) ▸
       at 5 2 (Bx3-024 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·124⟩ c4) ▸
       at 0 6 (Bx0-3124 ∷ []) (refl) ▸ done


-- nat 1 BOX(2;34): 2 steps
lem-nat-1-BOX⟨2·34⟩ : WsL → ⟪ (Sw12 ∷ Bx2-34 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-34 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·34⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx2-34 ∷ []) (Bx1-34 ∷ Sw12 ∷ [])
  b0 = at 0 2 (Bx2-34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CZ)) ▸
       at 0 1 (Bx1-34 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 1 BOX(3;214): 8 steps
lem-nat-1-BOX⟨3·214⟩ : WsL → ⟪ (Sw12 ∷ Bx3-214 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-124 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·214⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-214 ∷ []) (Bx3-124 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff312 ∷ Bx2-34 ∷ Toff312 ∷ CCZ123 ∷ Bx2-34 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw12 ∷ []) (sym (wl0111 c4)) ▸
       at 1 2 (Toff312 ∷ Sw12 ∷ []) (wl0143 c4) ▸
       at 2 2 (Bx1-34 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·34⟩ c4) ▸
       at 3 2 (Toff312 ∷ Sw12 ∷ []) (wl0143 c4) ▸
       at 4 2 (CCZ123 ∷ Sw12 ∷ []) (sym (wl0111 c4)) ▸
       at 5 2 (Bx1-34 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·34⟩ c4) ▸
       at 0 6 (Bx3-124 ∷ []) (refl) ▸ done


-- nat 1 BOX(2;3014): 8 steps
lem-nat-1-BOX⟨2·3014⟩ : WsL → ⟪ (Sw12 ∷ Bx2-3014 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3024 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·3014⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx2-3014 ∷ []) (Bx1-3024 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff203 ∷ Bx3-214 ∷ Toff203 ∷ CCZ023 ∷ Bx3-214 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 1 2 (Toff103 ∷ Sw12 ∷ []) (lem-nat-1-TOFF203 c4) ▸
       at 2 2 (Bx3-124 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·214⟩ c4) ▸
       at 3 2 (Toff103 ∷ Sw12 ∷ []) (lem-nat-1-TOFF203 c4) ▸
       at 4 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 5 2 (Bx3-124 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·214⟩ c4) ▸
       at 0 6 (Bx1-3024 ∷ []) (refl) ▸ done


-- nat 0 BOX(3;204): 8 steps
lem-nat-0-BOX⟨3·204⟩ : WsL → ⟪ (Sw01 ∷ Bx3-204 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-214 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·204⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx3-204 ∷ []) (Bx3-214 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff302 ∷ Bx2-34 ∷ Toff302 ∷ CCZ023 ∷ Bx2-34 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw01 ∷ []) (sym (wl0103 c4)) ▸
       at 1 2 (Toff312 ∷ Sw01 ∷ []) (wl0116 c4) ▸
       at 2 2 (Bx2-34 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑)) ▸
       at 3 2 (Toff312 ∷ Sw01 ∷ []) (wl0116 c4) ▸
       at 4 2 (CCZ123 ∷ Sw01 ∷ []) (sym (wl0103 c4)) ▸
       at 5 2 (Bx2-34 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑)) ▸
       at 0 6 (Bx3-214 ∷ []) (refl) ▸ done


-- nat 0 BOX(2;3104): 8 steps
lem-nat-0-BOX⟨2·3104⟩ : WsL → ⟪ (Sw01 ∷ Bx2-3104 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3014 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·3104⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx2-3104 ∷ []) (Bx2-3014 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff213 ∷ Bx3-204 ∷ Toff213 ∷ CCZ123 ∷ Bx3-204 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw01 ∷ []) (sym (wl0003 c4)) ▸
       at 1 2 (Toff203 ∷ Sw01 ∷ []) (wl0004 c4) ▸
       at 2 2 (Bx3-214 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·204⟩ c4) ▸
       at 3 2 (Toff203 ∷ Sw01 ∷ []) (wl0004 c4) ▸
       at 4 2 (CCZ023 ∷ Sw01 ∷ []) (sym (wl0003 c4)) ▸
       at 5 2 (Bx3-214 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·204⟩ c4) ▸
       at 0 6 (Bx2-3014 ∷ []) (refl) ▸ done


-- nat 0 BOX(2;04): 3 steps
lem-nat-0-BOX⟨2·04⟩ : WsL → ⟪ (Sw01 ∷ Bx2-04 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-14 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·04⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx2-04 ∷ []) (Bx2-14 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CZ04 ∷ []) (refl) ▸
       at 0 2 (CZ14 ∷ Sw01 ∷ []) (lem-nat-0-CZ04 c4) ▸
       at 0 1 (Bx2-14 ∷ []) (refl) ▸ done


-- nat 0 BOX(0;214): 8 steps
lem-nat-0-BOX⟨0·214⟩ : WsL → ⟪ (Sw01 ∷ Bx0-214 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-204 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·214⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-214 ∷ []) (Bx1-204 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff012 ∷ Bx2-04 ∷ Toff012 ∷ CCZ012 ∷ Bx2-04 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw01 ∷ []) (sym (wl0096 c4)) ▸
       at 1 2 (Toff102 ∷ Sw01 ∷ []) (wl0099 c4) ▸
       at 2 2 (Bx2-14 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·04⟩ c4) ▸
       at 3 2 (Toff102 ∷ Sw01 ∷ []) (wl0099 c4) ▸
       at 4 2 (CCZ012 ∷ Sw01 ∷ []) (sym (wl0096 c4)) ▸
       at 5 2 (Bx2-14 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·04⟩ c4) ▸
       at 0 6 (Bx1-204 ∷ []) (refl) ▸ done


-- nat 0 BOX(2;0314): 8 steps
lem-nat-0-BOX⟨2·0314⟩ : WsL → ⟪ (Sw01 ∷ Bx2-0314 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1304 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·0314⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx2-0314 ∷ []) (Bx2-1304 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff203 ∷ Bx0-214 ∷ Toff203 ∷ CCZ023 ∷ Bx0-214 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw01 ∷ []) (sym (wl0103 c4)) ▸
       at 1 2 (Toff213 ∷ Sw01 ∷ []) (wl0104 c4) ▸
       at 2 2 (Bx1-204 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·214⟩ c4) ▸
       at 3 2 (Toff213 ∷ Sw01 ∷ []) (wl0104 c4) ▸
       at 4 2 (CCZ123 ∷ Sw01 ∷ []) (sym (wl0103 c4)) ▸
       at 5 2 (Bx1-204 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·214⟩ c4) ▸
       at 0 6 (Bx2-1304 ∷ []) (refl) ▸ done


-- nat 0 BOX(2;14): 3 steps
lem-nat-0-BOX⟨2·14⟩ : WsL → ⟪ (Sw01 ∷ Bx2-14 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-04 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·14⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx2-14 ∷ []) (Bx2-04 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CZ14 ∷ []) (refl) ▸
       at 0 2 (CZ04 ∷ Sw01 ∷ []) (lem-nat-0-CZ14 c4) ▸
       at 0 1 (Bx2-04 ∷ []) (refl) ▸ done


-- nat 0 BOX(1;204): 8 steps
lem-nat-0-BOX⟨1·204⟩ : WsL → ⟪ (Sw01 ∷ Bx1-204 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-214 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·204⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-204 ∷ []) (Bx0-214 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff102 ∷ Bx2-14 ∷ Toff102 ∷ CCZ012 ∷ Bx2-14 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw01 ∷ []) (sym (wl0096 c4)) ▸
       at 1 2 (Toff012 ∷ Sw01 ∷ []) (wl0097 c4) ▸
       at 2 2 (Bx2-04 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·14⟩ c4) ▸
       at 3 2 (Toff012 ∷ Sw01 ∷ []) (wl0097 c4) ▸
       at 4 2 (CCZ012 ∷ Sw01 ∷ []) (sym (wl0096 c4)) ▸
       at 5 2 (Bx2-04 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·14⟩ c4) ▸
       at 0 6 (Bx0-214 ∷ []) (refl) ▸ done


-- nat 0 BOX(2;1304): 8 steps
lem-nat-0-BOX⟨2·1304⟩ : WsL → ⟪ (Sw01 ∷ Bx2-1304 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0314 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·1304⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx2-1304 ∷ []) (Bx2-0314 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff213 ∷ Bx1-204 ∷ Toff213 ∷ CCZ123 ∷ Bx1-204 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw01 ∷ []) (sym (wl0003 c4)) ▸
       at 1 2 (Toff203 ∷ Sw01 ∷ []) (wl0004 c4) ▸
       at 2 2 (Bx0-214 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·204⟩ c4) ▸
       at 3 2 (Toff203 ∷ Sw01 ∷ []) (wl0004 c4) ▸
       at 4 2 (CCZ023 ∷ Sw01 ∷ []) (sym (wl0003 c4)) ▸
       at 5 2 (Bx0-214 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·204⟩ c4) ▸
       at 0 6 (Bx2-0314 ∷ []) (refl) ▸ done


-- nat 0 BOX(0;234): 8 steps
lem-nat-0-BOX⟨0·234⟩ : WsL → ⟪ (Sw01 ∷ Bx0-234 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-234 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·234⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-234 ∷ []) (Bx1-234 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff023 ∷ Bx2-04 ∷ Toff023 ∷ CCZ023 ∷ Bx2-04 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw01 ∷ []) (sym (wl0103 c4)) ▸
       at 1 2 (Toff123 ∷ Sw01 ∷ []) (wl0108 c4) ▸
       at 2 2 (Bx2-14 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·04⟩ c4) ▸
       at 3 2 (Toff123 ∷ Sw01 ∷ []) (wl0108 c4) ▸
       at 4 2 (CCZ123 ∷ Sw01 ∷ []) (sym (wl0103 c4)) ▸
       at 5 2 (Bx2-14 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·04⟩ c4) ▸
       at 0 6 (Bx1-234 ∷ []) (refl) ▸ done


-- nat 0 BOX(2;0134): 8 steps
lem-nat-0-BOX⟨2·0134⟩ : WsL → ⟪ (Sw01 ∷ Bx2-0134 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1034 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·0134⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx2-0134 ∷ []) (Bx2-1034 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff201 ∷ Bx0-234 ∷ Toff201 ∷ CCZ012 ∷ Bx0-234 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw01 ∷ []) (sym (wl0096 c4)) ▸
       at 1 2 (Toff201 ∷ Sw01 ∷ []) (wl0107 c4) ▸
       at 2 2 (Bx1-234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·234⟩ c4) ▸
       at 3 2 (Toff201 ∷ Sw01 ∷ []) (wl0107 c4) ▸
       at 4 2 (CCZ012 ∷ Sw01 ∷ []) (sym (wl0096 c4)) ▸
       at 5 2 (Bx1-234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·234⟩ c4) ▸
       at 0 6 (Bx2-1034 ∷ []) (refl) ▸ done


-- nat 0 BOX(1;234): 8 steps
lem-nat-0-BOX⟨1·234⟩ : WsL → ⟪ (Sw01 ∷ Bx1-234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-234 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·234⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-234 ∷ []) (Bx0-234 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff123 ∷ Bx2-14 ∷ Toff123 ∷ CCZ123 ∷ Bx2-14 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw01 ∷ []) (sym (wl0003 c4)) ▸
       at 1 2 (Toff023 ∷ Sw01 ∷ []) (wl0053 c4) ▸
       at 2 2 (Bx2-04 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·14⟩ c4) ▸
       at 3 2 (Toff023 ∷ Sw01 ∷ []) (wl0053 c4) ▸
       at 4 2 (CCZ023 ∷ Sw01 ∷ []) (sym (wl0003 c4)) ▸
       at 5 2 (Bx2-04 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·14⟩ c4) ▸
       at 0 6 (Bx0-234 ∷ []) (refl) ▸ done


-- nat 0 BOX(2;1034): 8 steps
lem-nat-0-BOX⟨2·1034⟩ : WsL → ⟪ (Sw01 ∷ Bx2-1034 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·1034⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx2-1034 ∷ []) (Bx2-0134 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff201 ∷ Bx1-234 ∷ Toff201 ∷ CCZ012 ∷ Bx1-234 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw01 ∷ []) (sym (wl0096 c4)) ▸
       at 1 2 (Toff201 ∷ Sw01 ∷ []) (wl0107 c4) ▸
       at 2 2 (Bx0-234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·234⟩ c4) ▸
       at 3 2 (Toff201 ∷ Sw01 ∷ []) (wl0107 c4) ▸
       at 4 2 (CCZ012 ∷ Sw01 ∷ []) (sym (wl0096 c4)) ▸
       at 5 2 (Bx0-234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·234⟩ c4) ▸
       at 0 6 (Bx2-0134 ∷ []) (refl) ▸ done


-- nat 0 BOX(0;34): 2 steps
lem-nat-0-BOX⟨0·34⟩ : WsL → ⟪ (Sw01 ∷ Bx0-34 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-34 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·34⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-34 ∷ []) (Bx1-34 ∷ Sw01 ∷ [])
  b0 = at 0 2 (Bx0-34 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑)) ▸
       at 0 1 (Bx1-34 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 BOX(3;024): 8 steps
lem-nat-0-BOX⟨3·024⟩ : WsL → ⟪ (Sw01 ∷ Bx3-024 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-124 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·024⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx3-024 ∷ []) (Bx3-124 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff302 ∷ Bx0-34 ∷ Toff302 ∷ CCZ023 ∷ Bx0-34 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw01 ∷ []) (sym (wl0103 c4)) ▸
       at 1 2 (Toff312 ∷ Sw01 ∷ []) (wl0116 c4) ▸
       at 2 2 (Bx1-34 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·34⟩ c4) ▸
       at 3 2 (Toff312 ∷ Sw01 ∷ []) (wl0116 c4) ▸
       at 4 2 (CCZ123 ∷ Sw01 ∷ []) (sym (wl0103 c4)) ▸
       at 5 2 (Bx1-34 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·34⟩ c4) ▸
       at 0 6 (Bx3-124 ∷ []) (refl) ▸ done


-- nat 0 BOX(0;3124): 8 steps
lem-nat-0-BOX⟨0·3124⟩ : WsL → ⟪ (Sw01 ∷ Bx0-3124 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3024 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·3124⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-3124 ∷ []) (Bx1-3024 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff013 ∷ Bx3-024 ∷ Toff013 ∷ CCZ013 ∷ Bx3-024 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw01 ∷ []) (sym (wl0100 c4)) ▸
       at 1 2 (Toff103 ∷ Sw01 ∷ []) (wl0101 c4) ▸
       at 2 2 (Bx3-124 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·024⟩ c4) ▸
       at 3 2 (Toff103 ∷ Sw01 ∷ []) (wl0101 c4) ▸
       at 4 2 (CCZ013 ∷ Sw01 ∷ []) (sym (wl0100 c4)) ▸
       at 5 2 (Bx3-124 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·024⟩ c4) ▸
       at 0 6 (Bx1-3024 ∷ []) (refl) ▸ done


-- nat 1 BOX(1;34): 2 steps
lem-nat-1-BOX⟨1·34⟩ : WsL → ⟪ (Sw12 ∷ Bx1-34 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-34 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·34⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx1-34 ∷ []) (Bx2-34 ∷ Sw12 ∷ [])
  b0 = at 0 2 (Bx1-34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CZ)) ▸
       at 0 1 (Bx2-34 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 1 BOX(3;124): 8 steps
lem-nat-1-BOX⟨3·124⟩ : WsL → ⟪ (Sw12 ∷ Bx3-124 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-214 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·124⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-124 ∷ []) (Bx3-214 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff312 ∷ Bx1-34 ∷ Toff312 ∷ CCZ123 ∷ Bx1-34 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw12 ∷ []) (sym (wl0111 c4)) ▸
       at 1 2 (Toff312 ∷ Sw12 ∷ []) (wl0143 c4) ▸
       at 2 2 (Bx2-34 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·34⟩ c4) ▸
       at 3 2 (Toff312 ∷ Sw12 ∷ []) (wl0143 c4) ▸
       at 4 2 (CCZ123 ∷ Sw12 ∷ []) (sym (wl0111 c4)) ▸
       at 5 2 (Bx2-34 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·34⟩ c4) ▸
       at 0 6 (Bx3-214 ∷ []) (refl) ▸ done

