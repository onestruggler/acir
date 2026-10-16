{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.R021 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Lits using (lw0 ; lw1 ; lw2 ; lw3 ; lw4)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-1-CCZ023 ; lem-nat-1-CCZ024 ; lem-nat-1-TOFF014 ; lem-nat-1-TOFF024 ; lem-nat-1-TOFF203 ; lem-nat-2-TOFF024 ; lem-nat-2-TOFF034 ; lem-nat-3-CCZ014 ; lem-nat-3-TOFF013 ; lem-nat-3-TOFF104)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-1-CCZ013 ; lem-nat-1-CCZ014 ; lem-nat-3-CCZ013)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-0-CCZ024 ; lem-nat-0-CCZ124 ; lem-nat-1-TOFF103 ; lem-nat-2-CCZ124 ; lem-nat-2-CCZ134)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-0-CCZ014 ; lem-nat-0-TOFF014 ; lem-nat-0-TOFF104 ; lem-nat-1-TOFF104)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-0-TOFF024 ; lem-nat-1-TOFF013 ; lem-nat-2-CZ03 ; lem-nat-2-TOFF214)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-nat-2-CZ02)
open import Examples.Groups.Clifford+CS.Five.D.R012 using (lem-nat-1-BOX⟨0·12⟩ ; lem-nat-1-BOX⟨0·21⟩)
open import Examples.Groups.Clifford+CS.Five.D.R013 using (lem-nat-2-TOFF314)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-nat-2-CS02 ; lem-nat-2-CSd02)
open import Examples.Groups.Clifford+CS.Five.D.R015 using (lem-nat-0-BOX⟨0·12⟩ ; lem-nat-0-BOX⟨1·20⟩ ; lem-nat-0-TOFF134)
open import Examples.Groups.Clifford+CS.Five.D.R016 using (lem-nat-0-BOX⟨1·02⟩ ; lem-nat-0-TOFF034 ; lem-nat-1-BOX⟨1·02⟩)
open import Examples.Groups.Clifford+CS.Five.D.R019 using (lem-nat-0-BOX⟨0·21⟩ ; lem-nat-2-CS03 ; lem-nat-2-CSd03)
-- nat 0 BOX(2;031): 8 steps
lem-nat-0-BOX⟨2·031⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx2-031 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-130 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·031⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx2-031 ∷ []) (Bx2-130 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff203 ∷ Bx0-21 ∷ Toff203 ∷ CCZ023 ∷ Bx0-21 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ023 ∷ []) (CCZ123 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff213 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff203 ∷ []) (Toff213 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx1-20 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·21⟩ c4) ▸
       at 3 2 (Toff213 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff203 ∷ []) (Toff213 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ123 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ023 ∷ []) (CCZ123 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx1-20 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·21⟩ c4) ▸
       at 0 6 (Bx2-130 ∷ []) (refl) ▸ done


-- nat 0 BOX(0;2431): 8 steps
lem-nat-0-BOX⟨0·2431⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2430 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·2431⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-2431 ∷ []) (Bx1-2430 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff024 ∷ Bx2-031 ∷ Toff024 ∷ CCZ024 ∷ Bx2-031 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 1 2 (Toff124 ∷ Sw01 ∷ []) (lem-nat-0-TOFF024 c4) ▸
       at 2 2 (Bx2-130 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·031⟩ c4) ▸
       at 3 2 (Toff124 ∷ Sw01 ∷ []) (lem-nat-0-TOFF024 c4) ▸
       at 4 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 5 2 (Bx2-130 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·031⟩ c4) ▸
       at 0 6 (Bx1-2430 ∷ []) (refl) ▸ done


-- nat 0 SBOX(0;2;1;3): 3 steps
lem-nat-0-SBOX⟨0·2·1·3⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb0-2-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-0-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨0·2·1·3⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb0-2-1-3 ∷ []) (Sb1-2-0-3 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS12 ∷ []) (refl) ▸
       at 0 2 (CS02 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb1-2-0-3 ∷ []) (refl) ▸ done


-- nat 0 SBOXd(0;2;1;3): 3 steps
lem-nat-0-SBOXd⟨0·2·1·3⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb⁻0-2-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-2-0-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨0·2·1·3⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻0-2-1-3 ∷ []) (Sb⁻1-2-0-3 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS12⁻ ∷ []) (refl) ▸
       at 0 2 (CS02⁻ ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS12⁻ ∷ []) (CS02⁻ ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb⁻1-2-0-3 ∷ []) (refl) ▸ done


-- nat 0 SBOX(0;2;43;1): 7 steps
lem-nat-0-SBOX⟨0·2·43·1⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-43-0 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨0·2·43·1⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb0-2-43-1 ∷ []) (Sb1-2-43-0 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 0 2 (Bx1-2430 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·2431⟩ c4) ▸
       at 1 2 (Toff034 ∷ Sw01 ∷ []) (lem-nat-0-TOFF134 c4) ▸
       at 2 2 (Sb1-2-0-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·2·1·3⟩ c4) ▸
       at 3 2 (Toff034 ∷ Sw01 ∷ []) (lem-nat-0-TOFF134 c4) ▸
       at 4 2 (Sb⁻1-2-0-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨0·2·1·3⟩ c4) ▸
       at 0 5 (Sb1-2-43-0 ∷ []) (refl) ▸ done


-- nat 0 TOFF124: 70 steps
lem-nat-0-TOFF124 : Complete 4 → ⟪ (Sw01 ∷ Toff124 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-TOFF124 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (run b8))))))))
  where
  b0 : Chain (Sw01 ∷ Toff124 ∷ []) (Sw01 ∷ K1 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ Sw34 ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Toff123 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 4 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 2 3 (CS24 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 6 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CS24⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw01 ∷ K1 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ Sw34 ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw34 ∷ []) (K0 ∷ CS24 ∷ Sw01 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K1 ∷ ι1 ∷ [])
  b1 = at 5 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 6 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 8 2 (ι1 ∷ Sw34 ∷ []) (sym (c₂ (iI ↑) (Swap ↑))) ▸
       at 9 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 0 2 (K0 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ K1 ∷ []) (K0 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑)) ▸ done

  b2 : Chain (K0 ∷ CS24 ∷ Sw01 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K1 ∷ ι1 ∷ []) (K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ Sw01 ∷ K1 ∷ ι1 ∷ [])
  b2 = at 2 2 (CX02 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CX12 ∷ []) (CX02 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CS24⁻ ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • (CS • CS • CS) • Swap ↑)) ▸
       at 4 2 (CX02 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CX12 ∷ []) (CX02 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 6 2 (CS03 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS13 ∷ []) (CS03 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 5 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸ done

  b3 : Chain (K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ Sw01 ∷ K1 ∷ ι1 ∷ []) (Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ Sw12 ∷ CX02 ∷ CS04 ∷ K0 ∷ ι1 ∷ Sw01 ∷ [])
  b3 = at 6 2 (K0 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ K1 ∷ []) (K0 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (ι1 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ ι1 ∷ []) (ι1 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 2 2 (CS14 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS24 ∷ []) (CS14 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸
       at 4 2 (CS14⁻ ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS24⁻ ∷ []) (CS14⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸ done

  b4 : Chain (Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ Sw12 ∷ CX02 ∷ CS04 ∷ K0 ∷ ι1 ∷ Sw01 ∷ []) (Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ Sw12 ∷ ι1 ∷ Sw01 ∷ [])
  b4 = at 6 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸
       at 7 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 7 2 (CS03 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS03 ∷ []) (CS03 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 6 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸ done

  b5 : Chain (Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ Sw12 ∷ ι1 ∷ Sw01 ∷ []) (Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw34 ∷ CX01 ∷ CS04 ∷ K0 ∷ ι1 ∷ Sw12 ∷ Sw01 ∷ [])
  b5 = at 8 2 (ι1 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ ι1 ∷ []) (ι1 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 4 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 6 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done

  b6 : Chain (Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw34 ∷ CX01 ∷ CS04 ∷ K0 ∷ ι1 ∷ Sw12 ∷ Sw01 ∷ []) (Sw12 ∷ Sw34 ∷ Sw23 ∷ K0 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι1 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ [])
  b6 = at 6 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 8 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 9 2 (ι1 ∷ Sw34 ∷ []) (sym (c₂ (iI ↑) (Swap ↑))) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b7 : Chain (Sw12 ∷ Sw34 ∷ Sw23 ∷ K0 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι1 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ []) (Sw12 ∷ Sw34 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ Sw23 ∷ ι1 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ [])
  b7 = at 4 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 9 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸ done

  b8 : Chain (Sw12 ∷ Sw34 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ Sw23 ∷ ι1 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ []) (Toff024 ∷ Sw01 ∷ [])
  b8 = at 10 2 (ι1 ∷ Sw23 ∷ []) (sym (c₂ (iI ↑) (Swap))) ▸
       at 3 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (lw4 c4 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι1 ∷ []) (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) tt tt Eq.refl) ▸
       at 3 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff014 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Toff024 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 BOX(2;130): 8 steps
lem-nat-0-BOX⟨2·130⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx2-130 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-031 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·130⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx2-130 ∷ []) (Bx2-031 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff213 ∷ Bx1-20 ∷ Toff213 ∷ CCZ123 ∷ Bx1-20 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ123 ∷ []) (CCZ023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff203 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff213 ∷ []) (Toff203 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-21 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·20⟩ c4) ▸
       at 3 2 (Toff203 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff213 ∷ []) (Toff203 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ123 ∷ []) (CCZ023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx0-21 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·20⟩ c4) ▸
       at 0 6 (Bx2-031 ∷ []) (refl) ▸ done


-- nat 0 BOX(1;2430): 8 steps
lem-nat-0-BOX⟨1·2430⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx1-2430 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·2430⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-2430 ∷ []) (Bx0-2431 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff124 ∷ Bx2-130 ∷ Toff124 ∷ CCZ124 ∷ Bx2-130 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 1 2 (Toff024 ∷ Sw01 ∷ []) (lem-nat-0-TOFF124 c4) ▸
       at 2 2 (Bx2-031 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·130⟩ c4) ▸
       at 3 2 (Toff024 ∷ Sw01 ∷ []) (lem-nat-0-TOFF124 c4) ▸
       at 4 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 5 2 (Bx2-031 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·130⟩ c4) ▸
       at 0 6 (Bx0-2431 ∷ []) (refl) ▸ done


-- nat 0 SBOX(1;2;0;3): 3 steps
lem-nat-0-SBOX⟨1·2·0·3⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb1-2-0-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-1-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨1·2·0·3⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb1-2-0-3 ∷ []) (Sb0-2-1-3 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS02 ∷ []) (refl) ▸
       at 0 2 (CS12 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS02 ∷ []) (CS12 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb0-2-1-3 ∷ []) (refl) ▸ done


-- nat 0 SBOXd(1;2;0;3): 3 steps
lem-nat-0-SBOXd⟨1·2·0·3⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb⁻1-2-0-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-2-1-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨1·2·0·3⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻1-2-0-3 ∷ []) (Sb⁻0-2-1-3 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS02⁻ ∷ []) (refl) ▸
       at 0 2 (CS12⁻ ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS02⁻ ∷ []) (CS12⁻ ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸ done


-- nat 0 SBOX(1;2;43;0): 7 steps
lem-nat-0-SBOX⟨1·2·43·0⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb1-2-43-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨1·2·43·0⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb1-2-43-0 ∷ []) (Sb0-2-43-1 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx1-2430 ∷ Toff034 ∷ Sb1-2-0-3 ∷ Toff034 ∷ Sb⁻1-2-0-3 ∷ []) (refl) ▸
       at 0 2 (Bx0-2431 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·2430⟩ c4) ▸
       at 1 2 (Toff134 ∷ Sw01 ∷ []) (lem-nat-0-TOFF034 c4) ▸
       at 2 2 (Sb0-2-1-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·2·0·3⟩ c4) ▸
       at 3 2 (Toff134 ∷ Sw01 ∷ []) (lem-nat-0-TOFF034 c4) ▸
       at 4 2 (Sb⁻0-2-1-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·2·0·3⟩ c4) ▸
       at 0 5 (Sb0-2-43-1 ∷ []) (refl) ▸ done


-- nat 1 BOX(1;032): 8 steps
lem-nat-1-BOX⟨1·032⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx1-032 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-031 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·032⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx1-032 ∷ []) (Bx2-031 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff103 ∷ Bx0-12 ∷ Toff103 ∷ CCZ013 ∷ Bx0-12 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 1 2 (Toff203 ∷ Sw12 ∷ []) (lem-nat-1-TOFF103 c4) ▸
       at 2 2 (Bx0-21 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·12⟩ c4) ▸
       at 3 2 (Toff203 ∷ Sw12 ∷ []) (lem-nat-1-TOFF103 c4) ▸
       at 4 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 5 2 (Bx0-21 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·12⟩ c4) ▸
       at 0 6 (Bx2-031 ∷ []) (refl) ▸ done


-- nat 1 BOX(0;1432): 8 steps
lem-nat-1-BOX⟨0·1432⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx0-1432 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·1432⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-1432 ∷ []) (Bx0-2431 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff014 ∷ Bx1-032 ∷ Toff014 ∷ CCZ014 ∷ Bx1-032 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 1 2 (Toff024 ∷ Sw12 ∷ []) (lem-nat-1-TOFF014 c4) ▸
       at 2 2 (Bx2-031 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·032⟩ c4) ▸
       at 3 2 (Toff024 ∷ Sw12 ∷ []) (lem-nat-1-TOFF014 c4) ▸
       at 4 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 5 2 (Bx2-031 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·032⟩ c4) ▸
       at 0 6 (Bx0-2431 ∷ []) (refl) ▸ done


-- nat 1 SBOX(0;1;2;3): 3 steps
lem-nat-1-SBOX⟨0·1·2·3⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb0-1-2-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-1-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨0·1·2·3⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb0-1-2-3 ∷ []) (Sb0-2-1-3 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS12 ∷ []) (refl) ▸
       at 0 2 (CS12 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS12 ∷ []) (CS12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb0-2-1-3 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(0;1;2;3): 3 steps
lem-nat-1-SBOXd⟨0·1·2·3⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb⁻0-1-2-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-2-1-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨0·1·2·3⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻0-1-2-3 ∷ []) (Sb⁻0-2-1-3 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS12⁻ ∷ []) (refl) ▸
       at 0 2 (CS12⁻ ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸ done


-- nat 1 SBOX(0;1;43;2): 7 steps
lem-nat-1-SBOX⟨0·1·43·2⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨0·1·43·2⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb0-1-43-2 ∷ []) (Sb0-2-43-1 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx0-1432 ∷ Toff234 ∷ Sb0-1-2-3 ∷ Toff234 ∷ Sb⁻0-1-2-3 ∷ []) (refl) ▸
       at 0 2 (Bx0-2431 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1432⟩ c4) ▸
       at 1 2 (Toff134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff234 ∷ []) (Toff134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb0-2-1-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·2·3⟩ c4) ▸
       at 3 2 (Toff134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff234 ∷ []) (Toff134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Sb⁻0-2-1-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨0·1·2·3⟩ c4) ▸
       at 0 5 (Sb0-2-43-1 ∷ []) (refl) ▸ done


-- nat 1 BOX(2;031): 8 steps
lem-nat-1-BOX⟨2·031⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx2-031 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-032 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·031⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx2-031 ∷ []) (Bx1-032 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff203 ∷ Bx0-21 ∷ Toff203 ∷ CCZ023 ∷ Bx0-21 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 1 2 (Toff103 ∷ Sw12 ∷ []) (lem-nat-1-TOFF203 c4) ▸
       at 2 2 (Bx0-12 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·21⟩ c4) ▸
       at 3 2 (Toff103 ∷ Sw12 ∷ []) (lem-nat-1-TOFF203 c4) ▸
       at 4 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 5 2 (Bx0-12 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·21⟩ c4) ▸
       at 0 6 (Bx1-032 ∷ []) (refl) ▸ done


-- nat 1 BOX(0;2431): 8 steps
lem-nat-1-BOX⟨0·2431⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1432 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·2431⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-2431 ∷ []) (Bx0-1432 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff024 ∷ Bx2-031 ∷ Toff024 ∷ CCZ024 ∷ Bx2-031 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 1 2 (Toff014 ∷ Sw12 ∷ []) (lem-nat-1-TOFF024 c4) ▸
       at 2 2 (Bx1-032 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·031⟩ c4) ▸
       at 3 2 (Toff014 ∷ Sw12 ∷ []) (lem-nat-1-TOFF024 c4) ▸
       at 4 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 5 2 (Bx1-032 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·031⟩ c4) ▸
       at 0 6 (Bx0-1432 ∷ []) (refl) ▸ done


-- nat 1 SBOX(0;2;1;3): 3 steps
lem-nat-1-SBOX⟨0·2·1·3⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb0-2-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-2-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨0·2·1·3⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb0-2-1-3 ∷ []) (Sb0-1-2-3 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS12 ∷ []) (refl) ▸
       at 0 2 (CS12 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS12 ∷ []) (CS12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb0-1-2-3 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(0;2;1;3): 3 steps
lem-nat-1-SBOXd⟨0·2·1·3⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb⁻0-2-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-2-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨0·2·1·3⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻0-2-1-3 ∷ []) (Sb⁻0-1-2-3 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS12⁻ ∷ []) (refl) ▸
       at 0 2 (CS12⁻ ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb⁻0-1-2-3 ∷ []) (refl) ▸ done


-- nat 1 SBOX(0;2;43;1): 7 steps
lem-nat-1-SBOX⟨0·2·43·1⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-43-2 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨0·2·43·1⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb0-2-43-1 ∷ []) (Sb0-1-43-2 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 0 2 (Bx0-1432 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2431⟩ c4) ▸
       at 1 2 (Toff234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff134 ∷ []) (Toff234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb0-1-2-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·1·3⟩ c4) ▸
       at 3 2 (Toff234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff134 ∷ []) (Toff234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Sb⁻0-1-2-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨0·2·1·3⟩ c4) ▸
       at 0 5 (Sb0-1-43-2 ∷ []) (refl) ▸ done


-- nat 0 BOX(2;30): 3 steps
lem-nat-0-BOX⟨2·30⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx2-30 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-31 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·30⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx2-30 ∷ []) (Bx2-31 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CZ03 ∷ []) (refl) ▸
       at 0 2 (CZ13 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CZ03 ∷ []) (CZ13 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx2-31 ∷ []) (refl) ▸ done


-- nat 0 BOX(3;240): 8 steps
lem-nat-0-BOX⟨3·240⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx3-240 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-241 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·240⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx3-240 ∷ []) (Bx3-241 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff324 ∷ Bx2-30 ∷ Toff324 ∷ CCZ234 ∷ Bx2-30 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 1 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 2 2 (Bx2-31 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·30⟩ c4) ▸
       at 3 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 4 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 5 2 (Bx2-31 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·30⟩ c4) ▸
       at 0 6 (Bx3-241 ∷ []) (refl) ▸ done


-- nat 0 BOX(2;3140): 8 steps
lem-nat-0-BOX⟨2·3140⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx2-3140 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3041 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·3140⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx2-3140 ∷ []) (Bx2-3041 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff213 ∷ Bx3-240 ∷ Toff213 ∷ CCZ123 ∷ Bx3-240 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ123 ∷ []) (CCZ023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff203 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff213 ∷ []) (Toff203 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx3-241 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·240⟩ c4) ▸
       at 3 2 (Toff203 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff213 ∷ []) (Toff203 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ023 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ123 ∷ []) (CCZ023 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx3-241 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·240⟩ c4) ▸
       at 0 6 (Bx2-3041 ∷ []) (refl) ▸ done


-- nat 0 SBOX(2;3;0;4): 3 steps
lem-nat-0-SBOX⟨2·3·0·4⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb2-3-0-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-3-1-4 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨2·3·0·4⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb2-3-0-4 ∷ []) (Sb2-3-1-4 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS03 ∷ []) (refl) ▸
       at 0 2 (CS13 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS03 ∷ []) (CS13 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb2-3-1-4 ∷ []) (refl) ▸ done


-- nat 0 SBOXd(2;3;0;4): 3 steps
lem-nat-0-SBOXd⟨2·3·0·4⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb⁻2-3-0-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-3-1-4 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨2·3·0·4⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻2-3-0-4 ∷ []) (Sb⁻2-3-1-4 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS03⁻ ∷ []) (refl) ▸
       at 0 2 (CS13⁻ ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS03⁻ ∷ []) (CS13⁻ ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb⁻2-3-1-4 ∷ []) (refl) ▸ done


-- nat 0 SBOX(2;3;14;0): 7 steps
lem-nat-0-SBOX⟨2·3·14·0⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb2-3-14-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-3-04-1 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨2·3·14·0⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb2-3-14-0 ∷ []) (Sb2-3-04-1 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx2-3140 ∷ Toff014 ∷ Sb2-3-0-4 ∷ Toff014 ∷ Sb⁻2-3-0-4 ∷ []) (refl) ▸
       at 0 2 (Bx2-3041 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·3140⟩ c4) ▸
       at 1 2 (Toff104 ∷ Sw01 ∷ []) (lem-nat-0-TOFF014 c4) ▸
       at 2 2 (Sb2-3-1-4 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·3·0·4⟩ c4) ▸
       at 3 2 (Toff104 ∷ Sw01 ∷ []) (lem-nat-0-TOFF014 c4) ▸
       at 4 2 (Sb⁻2-3-1-4 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨2·3·0·4⟩ c4) ▸
       at 0 5 (Sb2-3-04-1 ∷ []) (refl) ▸ done


-- nat 0 BOX(2;31): 3 steps
lem-nat-0-BOX⟨2·31⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx2-31 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-30 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·31⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx2-31 ∷ []) (Bx2-30 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CZ13 ∷ []) (refl) ▸
       at 0 2 (CZ03 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CZ13 ∷ []) (CZ03 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx2-30 ∷ []) (refl) ▸ done


-- nat 0 BOX(3;241): 8 steps
lem-nat-0-BOX⟨3·241⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx3-241 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-240 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·241⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx3-241 ∷ []) (Bx3-240 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff324 ∷ Bx2-31 ∷ Toff324 ∷ CCZ234 ∷ Bx2-31 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 1 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 2 2 (Bx2-30 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·31⟩ c4) ▸
       at 3 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 4 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 5 2 (Bx2-30 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·31⟩ c4) ▸
       at 0 6 (Bx3-240 ∷ []) (refl) ▸ done


-- nat 0 BOX(2;3041): 8 steps
lem-nat-0-BOX⟨2·3041⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx2-3041 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3140 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·3041⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx2-3041 ∷ []) (Bx2-3140 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff203 ∷ Bx3-241 ∷ Toff203 ∷ CCZ023 ∷ Bx3-241 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ023 ∷ []) (CCZ123 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff213 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff203 ∷ []) (Toff213 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx3-240 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·241⟩ c4) ▸
       at 3 2 (Toff213 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff203 ∷ []) (Toff213 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ123 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ023 ∷ []) (CCZ123 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx3-240 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·241⟩ c4) ▸
       at 0 6 (Bx2-3140 ∷ []) (refl) ▸ done


-- nat 0 SBOX(2;3;1;4): 3 steps
lem-nat-0-SBOX⟨2·3·1·4⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb2-3-1-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-3-0-4 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨2·3·1·4⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb2-3-1-4 ∷ []) (Sb2-3-0-4 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS13 ∷ []) (refl) ▸
       at 0 2 (CS03 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS13 ∷ []) (CS03 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb2-3-0-4 ∷ []) (refl) ▸ done


-- nat 0 SBOXd(2;3;1;4): 3 steps
lem-nat-0-SBOXd⟨2·3·1·4⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb⁻2-3-1-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-3-0-4 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨2·3·1·4⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻2-3-1-4 ∷ []) (Sb⁻2-3-0-4 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS13⁻ ∷ []) (refl) ▸
       at 0 2 (CS03⁻ ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS13⁻ ∷ []) (CS03⁻ ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb⁻2-3-0-4 ∷ []) (refl) ▸ done


-- nat 0 SBOX(2;3;04;1): 7 steps
lem-nat-0-SBOX⟨2·3·04·1⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb2-3-04-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-3-14-0 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨2·3·04·1⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb2-3-04-1 ∷ []) (Sb2-3-14-0 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx2-3041 ∷ Toff104 ∷ Sb2-3-1-4 ∷ Toff104 ∷ Sb⁻2-3-1-4 ∷ []) (refl) ▸
       at 0 2 (Bx2-3140 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·3041⟩ c4) ▸
       at 1 2 (Toff014 ∷ Sw01 ∷ []) (lem-nat-0-TOFF104 c4) ▸
       at 2 2 (Sb2-3-0-4 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·3·1·4⟩ c4) ▸
       at 3 2 (Toff014 ∷ Sw01 ∷ []) (lem-nat-0-TOFF104 c4) ▸
       at 4 2 (Sb⁻2-3-0-4 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨2·3·1·4⟩ c4) ▸
       at 0 5 (Sb2-3-14-0 ∷ []) (refl) ▸ done


-- nat 1 BOX(1;30): 3 steps
lem-nat-1-BOX⟨1·30⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx1-30 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-30 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·30⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx1-30 ∷ []) (Bx2-30 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ03 ∷ []) (refl) ▸
       at 0 2 (CZ03 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CZ03 ∷ []) (CZ03 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx2-30 ∷ []) (refl) ▸ done


-- nat 1 BOX(3;140): 8 steps
lem-nat-1-BOX⟨3·140⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx3-140 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-240 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·140⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-140 ∷ []) (Bx3-240 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff314 ∷ Bx1-30 ∷ Toff314 ∷ CCZ134 ∷ Bx1-30 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ134 ∷ []) (CCZ234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff324 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff314 ∷ []) (Toff324 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx2-30 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·30⟩ c4) ▸
       at 3 2 (Toff324 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff314 ∷ []) (Toff324 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ134 ∷ []) (CCZ234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx2-30 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·30⟩ c4) ▸
       at 0 6 (Bx3-240 ∷ []) (refl) ▸ done


-- nat 1 BOX(1;3240): 8 steps
lem-nat-1-BOX⟨1·3240⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx1-3240 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3140 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·3240⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx1-3240 ∷ []) (Bx2-3140 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff123 ∷ Bx3-140 ∷ Toff123 ∷ CCZ123 ∷ Bx3-140 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff213 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff123 ∷ []) (Toff213 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx3-240 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·140⟩ c4) ▸
       at 3 2 (Toff213 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff123 ∷ []) (Toff213 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ123 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx3-240 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·140⟩ c4) ▸
       at 0 6 (Bx2-3140 ∷ []) (refl) ▸ done


-- nat 1 SBOX(1;3;0;4): 3 steps
lem-nat-1-SBOX⟨1·3·0·4⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb1-3-0-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-3-0-4 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨1·3·0·4⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb1-3-0-4 ∷ []) (Sb2-3-0-4 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS03 ∷ []) (refl) ▸
       at 0 2 (CS03 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS03 ∷ []) (CS03 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb2-3-0-4 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(1;3;0;4): 3 steps
lem-nat-1-SBOXd⟨1·3·0·4⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb⁻1-3-0-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-3-0-4 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨1·3·0·4⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻1-3-0-4 ∷ []) (Sb⁻2-3-0-4 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS03⁻ ∷ []) (refl) ▸
       at 0 2 (CS03⁻ ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb⁻2-3-0-4 ∷ []) (refl) ▸ done


-- nat 1 SBOX(1;3;24;0): 7 steps
lem-nat-1-SBOX⟨1·3·24·0⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb1-3-24-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-3-14-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨1·3·24·0⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb1-3-24-0 ∷ []) (Sb2-3-14-0 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx1-3240 ∷ Toff024 ∷ Sb1-3-0-4 ∷ Toff024 ∷ Sb⁻1-3-0-4 ∷ []) (refl) ▸
       at 0 2 (Bx2-3140 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·3240⟩ c4) ▸
       at 1 2 (Toff014 ∷ Sw12 ∷ []) (lem-nat-1-TOFF024 c4) ▸
       at 2 2 (Sb2-3-0-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·3·0·4⟩ c4) ▸
       at 3 2 (Toff014 ∷ Sw12 ∷ []) (lem-nat-1-TOFF024 c4) ▸
       at 4 2 (Sb⁻2-3-0-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·3·0·4⟩ c4) ▸
       at 0 5 (Sb2-3-14-0 ∷ []) (refl) ▸ done


-- nat 1 BOX(2;30): 3 steps
lem-nat-1-BOX⟨2·30⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx2-30 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-30 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·30⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx2-30 ∷ []) (Bx1-30 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ03 ∷ []) (refl) ▸
       at 0 2 (CZ03 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CZ03 ∷ []) (CZ03 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx1-30 ∷ []) (refl) ▸ done


-- nat 1 BOX(3;240): 8 steps
lem-nat-1-BOX⟨3·240⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx3-240 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-140 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·240⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-240 ∷ []) (Bx3-140 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff324 ∷ Bx2-30 ∷ Toff324 ∷ CCZ234 ∷ Bx2-30 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ234 ∷ []) (CCZ134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff314 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff324 ∷ []) (Toff314 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx1-30 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·30⟩ c4) ▸
       at 3 2 (Toff314 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff324 ∷ []) (Toff314 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ234 ∷ []) (CCZ134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx1-30 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·30⟩ c4) ▸
       at 0 6 (Bx3-140 ∷ []) (refl) ▸ done


-- nat 1 BOX(2;3140): 8 steps
lem-nat-1-BOX⟨2·3140⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx2-3140 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3240 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·3140⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx2-3140 ∷ []) (Bx1-3240 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff213 ∷ Bx3-240 ∷ Toff213 ∷ CCZ123 ∷ Bx3-240 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff123 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff213 ∷ []) (Toff123 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx3-140 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·240⟩ c4) ▸
       at 3 2 (Toff123 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff213 ∷ []) (Toff123 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ123 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx3-140 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·240⟩ c4) ▸
       at 0 6 (Bx1-3240 ∷ []) (refl) ▸ done


-- nat 1 SBOX(2;3;0;4): 3 steps
lem-nat-1-SBOX⟨2·3·0·4⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb2-3-0-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-3-0-4 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨2·3·0·4⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb2-3-0-4 ∷ []) (Sb1-3-0-4 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS03 ∷ []) (refl) ▸
       at 0 2 (CS03 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS03 ∷ []) (CS03 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb1-3-0-4 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(2;3;0;4): 3 steps
lem-nat-1-SBOXd⟨2·3·0·4⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb⁻2-3-0-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-3-0-4 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨2·3·0·4⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻2-3-0-4 ∷ []) (Sb⁻1-3-0-4 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS03⁻ ∷ []) (refl) ▸
       at 0 2 (CS03⁻ ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb⁻1-3-0-4 ∷ []) (refl) ▸ done


-- nat 1 SBOX(2;3;14;0): 7 steps
lem-nat-1-SBOX⟨2·3·14·0⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb2-3-14-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-3-24-0 ∷ Sw12 ∷ []) ⟫ʷ
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
lem-nat-2-BOX⟨1·20⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx1-20 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-30 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·20⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx1-20 ∷ []) (Bx1-30 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ02 ∷ []) (refl) ▸
       at 0 2 (CZ03 ∷ Sw23 ∷ []) (lem-nat-2-CZ02 c4) ▸
       at 0 1 (Bx1-30 ∷ []) (refl) ▸ done


-- nat 2 BOX(2;140): 8 steps
lem-nat-2-BOX⟨2·140⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx2-140 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-140 ∷ Sw23 ∷ []) ⟫ʷ
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
lem-nat-2-BOX⟨1·2340⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx1-2340 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3240 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·2340⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx1-2340 ∷ []) (Bx1-3240 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff123 ∷ Bx2-140 ∷ Toff123 ∷ CCZ123 ∷ Bx2-140 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff123 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff123 ∷ []) (Toff123 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx3-140 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·140⟩ c4) ▸
       at 3 2 (Toff123 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff123 ∷ []) (Toff123 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ123 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx3-140 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·140⟩ c4) ▸
       at 0 6 (Bx1-3240 ∷ []) (refl) ▸ done


-- nat 2 SBOX(1;2;0;4): 3 steps
lem-nat-2-SBOX⟨1·2·0·4⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb1-2-0-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-3-0-4 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨1·2·0·4⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb1-2-0-4 ∷ []) (Sb1-3-0-4 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS02 ∷ []) (refl) ▸
       at 0 2 (CS03 ∷ Sw23 ∷ []) (lem-nat-2-CS02 c4) ▸
       at 0 1 (Sb1-3-0-4 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(1;2;0;4): 3 steps
lem-nat-2-SBOXd⟨1·2·0·4⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb⁻1-2-0-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-3-0-4 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨1·2·0·4⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻1-2-0-4 ∷ []) (Sb⁻1-3-0-4 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS02⁻ ∷ []) (refl) ▸
       at 0 2 (CS03⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd02 c4) ▸
       at 0 1 (Sb⁻1-3-0-4 ∷ []) (refl) ▸ done


-- nat 2 SBOX(1;2;34;0): 7 steps
lem-nat-2-SBOX⟨1·2·34·0⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb1-2-34-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-3-24-0 ∷ Sw23 ∷ []) ⟫ʷ
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
lem-nat-2-BOX⟨1·30⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx1-30 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-20 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·30⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx1-30 ∷ []) (Bx1-20 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ03 ∷ []) (refl) ▸
       at 0 2 (CZ02 ∷ Sw23 ∷ []) (lem-nat-2-CZ03 c4) ▸
       at 0 1 (Bx1-20 ∷ []) (refl) ▸ done


-- nat 2 BOX(3;140): 8 steps
lem-nat-2-BOX⟨3·140⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx3-140 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-140 ∷ Sw23 ∷ []) ⟫ʷ
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
lem-nat-2-BOX⟨1·3240⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx1-3240 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2340 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·3240⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx1-3240 ∷ []) (Bx1-2340 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff123 ∷ Bx3-140 ∷ Toff123 ∷ CCZ123 ∷ Bx3-140 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff123 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff123 ∷ []) (Toff123 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx2-140 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·140⟩ c4) ▸
       at 3 2 (Toff123 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff123 ∷ []) (Toff123 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ123 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx2-140 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·140⟩ c4) ▸
       at 0 6 (Bx1-2340 ∷ []) (refl) ▸ done


-- nat 2 SBOX(1;3;0;4): 3 steps
lem-nat-2-SBOX⟨1·3·0·4⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb1-3-0-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-0-4 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨1·3·0·4⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb1-3-0-4 ∷ []) (Sb1-2-0-4 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS03 ∷ []) (refl) ▸
       at 0 2 (CS02 ∷ Sw23 ∷ []) (lem-nat-2-CS03 c4) ▸
       at 0 1 (Sb1-2-0-4 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(1;3;0;4): 3 steps
lem-nat-2-SBOXd⟨1·3·0·4⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb⁻1-3-0-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-2-0-4 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨1·3·0·4⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻1-3-0-4 ∷ []) (Sb⁻1-2-0-4 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS03⁻ ∷ []) (refl) ▸
       at 0 2 (CS02⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd03 c4) ▸
       at 0 1 (Sb⁻1-2-0-4 ∷ []) (refl) ▸ done


-- nat 2 SBOX(1;3;24;0): 7 steps
lem-nat-2-SBOX⟨1·3·24·0⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb1-3-24-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-34-0 ∷ Sw23 ∷ []) ⟫ʷ
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
lem-nat-3-BOX⟨1·042⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx1-042 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-032 ∷ Sw34 ∷ []) ⟫ʷ
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
lem-nat-3-BOX⟨0·1342⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx0-1342 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1432 ∷ Sw34 ∷ []) ⟫ʷ
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
lem-nat-0-BOX⟨1·032⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx1-032 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-132 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·032⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-032 ∷ []) (Bx0-132 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff103 ∷ Bx0-12 ∷ Toff103 ∷ CCZ013 ∷ Bx0-12 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff103 ∷ []) (Toff013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx1-02 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·12⟩ c4) ▸
       at 3 2 (Toff013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff103 ∷ []) (Toff013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx1-02 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·12⟩ c4) ▸
       at 0 6 (Bx0-132 ∷ []) (refl) ▸ done


-- nat 0 BOX(0;1432): 8 steps
lem-nat-0-BOX⟨0·1432⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx0-1432 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0432 ∷ Sw01 ∷ []) ⟫ʷ
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
lem-nat-1-BOX⟨0·132⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx0-132 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-231 ∷ Sw12 ∷ []) ⟫ʷ
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
lem-nat-1-BOX⟨1·0432⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx1-0432 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0431 ∷ Sw12 ∷ []) ⟫ʷ
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
lem-nat-0-BOX⟨0·132⟩ : Complete 4 → ⟪ (Sw01 ∷ Bx0-132 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-032 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·132⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-132 ∷ []) (Bx1-032 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff013 ∷ Bx1-02 ∷ Toff013 ∷ CCZ013 ∷ Bx1-02 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff103 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff013 ∷ []) (Toff103 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx0-12 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·02⟩ c4) ▸
       at 3 2 (Toff103 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff013 ∷ []) (Toff103 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ013 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CCZ013 ∷ []) (CCZ013 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx0-12 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·02⟩ c4) ▸
       at 0 6 (Bx1-032 ∷ []) (refl) ▸ done

