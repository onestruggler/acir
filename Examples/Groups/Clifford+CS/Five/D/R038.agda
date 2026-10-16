{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.R038 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Lits using (lw0 ; lw1 ; lw2 ; lw3 ; lw4)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-1-BOX⟨0·2413⟩ ; lem-nat-1-CCZ024 ; lem-nat-3-CCZ024 ; lem-nat-3-CCZ034)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-1-BOX⟨0·1423⟩ ; lem-nat-1-CCZ014 ; lem-nat-3-CCZ023)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-2-CCZ134)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-1-TOFF104 ; lem-nat-3-TOFF402)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-3-CZ23 ; lem-nat-3-TOFF214 ; lem-nat-3-TOFF302 ; lem-nat-3-TOFF304)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-3-TOFF023)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-nat-3-CCZ123 ; lem-nat-3-CCZ124)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-nat-2-CCZ014 ; lem-nat-2-CZ12 ; lem-nat-3-CZ24)
open import Examples.Groups.Clifford+CS.Five.D.R017 using (lem-nat-1-TOFF402 ; lem-nat-2-TOFF401 ; lem-nat-3-TOFF024)
open import Examples.Groups.Clifford+CS.Five.D.R020 using (lem-nat-3-TOFF213)
open import Examples.Groups.Clifford+CS.Five.D.R023 using (lem-nat-2-TOFF134)
open import Examples.Groups.Clifford+CS.Five.D.R030 using (lem-nat-1-BOX⟨4·12⟩ ; lem-nat-1-BOX⟨4·21⟩)
open import Examples.Groups.Clifford+CS.Five.D.R037 using (lem-nat-1-SBOX⟨0·1·3·2⟩ ; lem-nat-1-SBOX⟨0·2·3·1⟩ ; lem-nat-1-SBOXd⟨0·1·3·2⟩ ; lem-nat-1-SBOXd⟨0·2·3·1⟩ ; lem-nat-2-BOX⟨1·423⟩)
-- nat 2 BOX(4;1023): 8 steps
lem-nat-2-BOX⟨4·1023⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx4-1023 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1032 ∷ Sw23 ∷ []) ⟫ʷ
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
lem-nat-1-BOX⟨2·431⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx2-431 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-432 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·431⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx2-431 ∷ []) (Bx1-432 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff234 ∷ Bx4-21 ∷ Toff234 ∷ CCZ234 ∷ Bx4-21 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ234 ∷ []) (CCZ134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff234 ∷ []) (Toff134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx4-12 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·21⟩ c4) ▸
       at 3 2 (Toff134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff234 ∷ []) (Toff134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ234 ∷ []) (CCZ134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx4-12 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·21⟩ c4) ▸
       at 0 6 (Bx1-432 ∷ []) (refl) ▸ done


-- nat 1 BOX(4;2031): 8 steps
lem-nat-1-BOX⟨4·2031⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx4-2031 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1032 ∷ Sw12 ∷ []) ⟫ʷ
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


-- nat 1 BOX(1;402): 8 steps
lem-nat-1-BOX⟨1·402⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx1-402 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-401 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·402⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx1-402 ∷ []) (Bx2-401 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff104 ∷ Bx4-12 ∷ Toff104 ∷ CCZ014 ∷ Bx4-12 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 1 2 (Toff204 ∷ Sw12 ∷ []) (lem-nat-1-TOFF104 c4) ▸
       at 2 2 (Bx4-21 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·12⟩ c4) ▸
       at 3 2 (Toff204 ∷ Sw12 ∷ []) (lem-nat-1-TOFF104 c4) ▸
       at 4 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 5 2 (Bx4-21 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·12⟩ c4) ▸
       at 0 6 (Bx2-401 ∷ []) (refl) ▸ done


-- nat 1 BOX(4;1302): 8 steps
lem-nat-1-BOX⟨4·1302⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx4-1302 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2301 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·1302⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx4-1302 ∷ []) (Bx4-2301 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff413 ∷ Bx1-402 ∷ Toff413 ∷ CCZ134 ∷ Bx1-402 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ134 ∷ []) (CCZ234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff423 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff413 ∷ []) (Toff423 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx2-401 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·402⟩ c4) ▸
       at 3 2 (Toff423 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff413 ∷ []) (Toff423 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ134 ∷ []) (CCZ234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx2-401 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·402⟩ c4) ▸
       at 0 6 (Bx4-2301 ∷ []) (refl) ▸ done


-- nat 3 TOFF403: 144 steps
lem-nat-3-TOFF403 : Complete 4 → ⟪ (Sw34 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-TOFF403 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (run b17)))))))))))))))))
  where
  b0 : Chain (Sw34 ∷ Toff403 ∷ []) (Sw34 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K3 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Toff402 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw12 ∷ Toff401 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw34 ∷ Toff301 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (K3 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ K2 ∷ []) (K3 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K3 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b1 = at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 7 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 9 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (K3 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ K2 ∷ []) (K3 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸ done

  b2 : Chain (Sw34 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ Sw12 ∷ K4 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b2 = at 12 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 3 2 (K4 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ K3 ∷ []) (K4 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 6 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 6 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸ done

  b3 : Chain (Sw34 ∷ Sw23 ∷ Sw12 ∷ K4 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ K4 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K4 ∷ ι ∷ Sw12 ∷ Sw23 ∷ [])
  b3 = at 10 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 8 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K4 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ K3 ∷ []) (K4 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 11 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 2 2 (K4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K ↑)) ▸
       at 3 2 (CS24 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS14 ∷ []) (CS24 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 6 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸ done

  b4 : Chain (Sw34 ∷ Sw23 ∷ K4 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K4 ∷ ι ∷ Sw12 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ K4 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ K4 ∷ ι ∷ Sw12 ∷ Sw23 ∷ [])
  b4 = at 4 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS24⁻ ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS14⁻ ∷ []) (CS24⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 8 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 6 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 8 2 (CS03 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS03 ∷ []) (CS03 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸ done

  b5 : Chain (Sw34 ∷ Sw23 ∷ K4 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ K4 ∷ ι ∷ Sw12 ∷ Sw23 ∷ []) (Sw34 ∷ K4 ∷ CS34 ∷ CX03 ∷ Sw23 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K4 ∷ ι ∷ Sw23 ∷ [])
  b5 = at 7 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K ↑)) ▸
       at 9 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 10 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸
       at 1 2 (K4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K)) ▸
       at 2 2 (CS34 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS24 ∷ []) (CS34 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸ done

  b6 : Chain (Sw34 ∷ K4 ∷ CS34 ∷ CX03 ∷ Sw23 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K4 ∷ ι ∷ Sw23 ∷ []) (Sw34 ∷ K4 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Sw34 ∷ K4 ∷ ι ∷ Sw23 ∷ [])
  b6 = at 4 2 (CS34⁻ ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS24⁻ ∷ []) (CS34⁻ ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (lw0 c4 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 9 2 (CS01 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸
       at 10 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸ done

  b7 : Chain (Sw34 ∷ K4 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Sw34 ∷ K4 ∷ ι ∷ Sw23 ∷ []) (K3 ∷ CS34 ∷ Sw34 ∷ CX03 ∷ Sw34 ∷ Sw34 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K4 ∷ ι ∷ [])
  b7 = at 11 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (lw0 c4 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 6 7 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K)) ▸
       at 8 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 9 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 0 2 (K3 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ K4 ∷ []) (K3 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS34 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ CS34 ∷ []) (CS34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 4 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸ done

  b8 : Chain (K3 ∷ CS34 ∷ Sw34 ∷ CX03 ∷ Sw34 ∷ Sw34 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K4 ∷ ι ∷ []) (K3 ∷ CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ K3 ∷ ι ∷ Sw34 ∷ [])
  b8 = at 2 3 (CX04 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS34⁻ ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 6 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CX04 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 6 2 (K3 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ K4 ∷ []) (K3 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸ done

  b9 : Chain (K3 ∷ CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ K3 ∷ ι ∷ Sw34 ∷ []) (Sw23 ∷ K2 ∷ CS24 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Sw34 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ K3 ∷ ι ∷ Sw34 ∷ [])
  b9 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (K2 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ K3 ∷ []) (K2 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CS24 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS34 ∷ []) (CS24 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (lw0 c4 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 6 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 7 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸ done

  b10 : Chain (Sw23 ∷ K2 ∷ CS24 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Sw34 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ K3 ∷ ι ∷ Sw34 ∷ []) (Sw23 ∷ K2 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Sw34 ∷ CS03 ∷ K3 ∷ ι ∷ Sw34 ∷ [])
  b10 = at 8 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (lw0 c4 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 3 7 (CX04 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS24⁻ ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS34⁻ ∷ []) (CS24⁻ ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (lw0 c4 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 8 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 9 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸ done

  b11 : Chain (Sw23 ∷ K2 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Sw34 ∷ CS03 ∷ K3 ∷ ι ∷ Sw34 ∷ []) (Sw23 ∷ Sw12 ∷ K1 ∷ Sw12 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw34 ∷ [])
  b11 = at 10 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (lw0 c4 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 7 (CX04 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 (K2 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ K3 ∷ []) (K2 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 1 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (K1 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ K2 ∷ []) (K1 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸ done

  b12 : Chain (Sw23 ∷ Sw12 ∷ K1 ∷ Sw12 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw34 ∷ []) (Sw23 ∷ Sw12 ∷ K1 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ Sw12 ∷ Sw34 ∷ CX03 ∷ Sw34 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw34 ∷ [])
  b12 = at 3 2 (CS14 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS24 ∷ []) (CS14 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Sw34 ∷ CX03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 5 2 (CX03 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CX03 ∷ []) (CX03 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 4 3 (CX04 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS14⁻ ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS24⁻ ∷ []) (CS14⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (Sw34 ∷ CX03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b13 : Chain (Sw23 ∷ Sw12 ∷ K1 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ Sw12 ∷ Sw34 ∷ CX03 ∷ Sw34 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw34 ∷ []) (Sw23 ∷ Sw12 ∷ K1 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ [])
  b13 = at 6 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 7 2 (CX03 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CX03 ∷ []) (CX03 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 6 3 (CX04 ∷ []) (by-assoc Eq.refl) ▸
       at 8 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸
       at 8 2 (K1 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ K2 ∷ []) (K1 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸ done

  b14 : Chain (Sw23 ∷ Sw12 ∷ K1 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ CX03 ∷ CS13⁻ ∷ Sw34 ∷ CX04 ∷ CS01 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ [])
  b14 = at 2 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 5 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 6 1 (Sw34 ∷ CX03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 7 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done

  b15 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ CX03 ∷ CS13⁻ ∷ Sw34 ∷ CX04 ∷ CS01 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K1 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ [])
  b15 = at 8 1 (Sw34 ∷ CX03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 8 2 (CS01 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸
       at 9 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 10 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b16 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K1 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K1 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ Sw23 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ [])
  b16 = at 5 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 7 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 9 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 9 2 (CS01 ∷ Sw23 ∷ []) (sym (c₂ (CS) (Swap))) ▸ done

  b17 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K1 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ Sw23 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (Toff304 ∷ Sw34 ∷ [])
  b17 = at 10 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 11 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 4 8 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (lw4 c4 (K1 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K1 ∷ ι ∷ []) (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) tt tt Eq.refl) ▸
       at 4 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸
       at 3 3 (Toff103 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (Toff104 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff204 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Toff304 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 3 BOX(4;01): 2 steps
lem-nat-3-BOX⟨4·01⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx4-01 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-01 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨4·01⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx4-01 ∷ []) (Bx3-01 ∷ Sw34 ∷ [])
  b0 = at 0 2 (Bx4-01 ∷ Sw34 ∷ []) (sym (c₂ (CZ) (Swap ↑))) ▸
       at 0 1 (Bx3-01 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 3 BOX(0;421): 8 steps
lem-nat-3-BOX⟨0·421⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx0-421 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-321 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·421⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx0-421 ∷ []) (Bx0-321 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff024 ∷ Bx4-01 ∷ Toff024 ∷ CCZ024 ∷ Bx4-01 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 c4) ▸
       at 1 2 (Toff023 ∷ Sw34 ∷ []) (lem-nat-3-TOFF024 c4) ▸
       at 2 2 (Bx3-01 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·01⟩ c4) ▸
       at 3 2 (Toff023 ∷ Sw34 ∷ []) (lem-nat-3-TOFF024 c4) ▸
       at 4 2 (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 c4) ▸
       at 5 2 (Bx3-01 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·01⟩ c4) ▸
       at 0 6 (Bx0-321 ∷ []) (refl) ▸ done


-- nat 3 BOX(4;0321): 8 steps
lem-nat-3-BOX⟨4·0321⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx4-0321 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0421 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨4·0321⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx4-0321 ∷ []) (Bx3-0421 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff403 ∷ Bx0-421 ∷ Toff403 ∷ CCZ034 ∷ Bx0-421 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw34 ∷ []) (lem-nat-3-CCZ034 c4) ▸
       at 1 2 (Toff304 ∷ Sw34 ∷ []) (lem-nat-3-TOFF403 c4) ▸
       at 2 2 (Bx0-321 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·421⟩ c4) ▸
       at 3 2 (Toff304 ∷ Sw34 ∷ []) (lem-nat-3-TOFF403 c4) ▸
       at 4 2 (CCZ034 ∷ Sw34 ∷ []) (lem-nat-3-CCZ034 c4) ▸
       at 5 2 (Bx0-321 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·421⟩ c4) ▸
       at 0 6 (Bx3-0421 ∷ []) (refl) ▸ done


-- nat 3 BOX(3;01): 2 steps
lem-nat-3-BOX⟨3·01⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx3-01 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-01 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨3·01⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx3-01 ∷ []) (Bx4-01 ∷ Sw34 ∷ [])
  b0 = at 0 2 (Bx3-01 ∷ Sw34 ∷ []) (sym (c₂ (CZ) (Swap ↑))) ▸
       at 0 1 (Bx4-01 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 3 BOX(0;321): 8 steps
lem-nat-3-BOX⟨0·321⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx0-321 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-421 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·321⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx0-321 ∷ []) (Bx0-421 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff023 ∷ Bx3-01 ∷ Toff023 ∷ CCZ023 ∷ Bx3-01 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw34 ∷ []) (lem-nat-3-CCZ023 c4) ▸
       at 1 2 (Toff024 ∷ Sw34 ∷ []) (lem-nat-3-TOFF023 c4) ▸
       at 2 2 (Bx4-01 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·01⟩ c4) ▸
       at 3 2 (Toff024 ∷ Sw34 ∷ []) (lem-nat-3-TOFF023 c4) ▸
       at 4 2 (CCZ024 ∷ Sw34 ∷ []) (lem-nat-3-CCZ023 c4) ▸
       at 5 2 (Bx4-01 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·01⟩ c4) ▸
       at 0 6 (Bx0-421 ∷ []) (refl) ▸ done


-- nat 3 BOX(3;0421): 8 steps
lem-nat-3-BOX⟨3·0421⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx3-0421 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0321 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨3·0421⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx3-0421 ∷ []) (Bx4-0321 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff304 ∷ Bx0-321 ∷ Toff304 ∷ CCZ034 ∷ Bx0-321 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw34 ∷ []) (lem-nat-3-CCZ034 c4) ▸
       at 1 2 (Toff403 ∷ Sw34 ∷ []) (lem-nat-3-TOFF304 c4) ▸
       at 2 2 (Bx0-421 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·321⟩ c4) ▸
       at 3 2 (Toff403 ∷ Sw34 ∷ []) (lem-nat-3-TOFF304 c4) ▸
       at 4 2 (CCZ034 ∷ Sw34 ∷ []) (lem-nat-3-CCZ034 c4) ▸
       at 5 2 (Bx0-421 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·321⟩ c4) ▸
       at 0 6 (Bx4-0321 ∷ []) (refl) ▸ done


-- nat 2 BOX(3;24): 3 steps
lem-nat-2-BOX⟨3·24⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx3-24 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-34 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·24⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx3-24 ∷ []) (Bx2-34 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ24 ∷ []) (refl) ▸
       at 0 2 (CZ34 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CZ24 ∷ []) (CZ34 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx2-34 ∷ []) (refl) ▸ done


-- nat 2 BOX(2;314): 8 steps
lem-nat-2-BOX⟨2·314⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx2-314 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-214 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·314⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx2-314 ∷ []) (Bx3-214 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff213 ∷ Bx3-24 ∷ Toff213 ∷ CCZ123 ∷ Bx3-24 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff312 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff213 ∷ []) (Toff312 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx2-34 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·24⟩ c4) ▸
       at 3 2 (Toff312 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff213 ∷ []) (Toff312 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ123 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx2-34 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·24⟩ c4) ▸
       at 0 6 (Bx3-214 ∷ []) (refl) ▸ done


-- nat 2 BOX(3;2014): 8 steps
lem-nat-2-BOX⟨3·2014⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx3-2014 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3014 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·2014⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx3-2014 ∷ []) (Bx2-3014 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff302 ∷ Bx2-314 ∷ Toff302 ∷ CCZ023 ∷ Bx2-314 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ023 ∷ []) (CCZ023 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff203 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff302 ∷ []) (Toff203 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx3-214 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·314⟩ c4) ▸
       at 3 2 (Toff203 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff302 ∷ []) (Toff203 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ023 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ023 ∷ []) (CCZ023 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx3-214 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·314⟩ c4) ▸
       at 0 6 (Bx2-3014 ∷ []) (refl) ▸ done


-- nat 2 BOX(2;34): 3 steps
lem-nat-2-BOX⟨2·34⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx2-34 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-24 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·34⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx2-34 ∷ []) (Bx3-24 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ34 ∷ []) (refl) ▸
       at 0 2 (CZ24 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CZ34 ∷ []) (CZ24 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx3-24 ∷ []) (refl) ▸ done


-- nat 2 BOX(3;214): 8 steps
lem-nat-2-BOX⟨3·214⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx3-214 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-314 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·214⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx3-214 ∷ []) (Bx2-314 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff312 ∷ Bx2-34 ∷ Toff312 ∷ CCZ123 ∷ Bx2-34 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff213 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff312 ∷ []) (Toff213 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx3-24 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·34⟩ c4) ▸
       at 3 2 (Toff213 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff312 ∷ []) (Toff213 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ123 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ123 ∷ []) (CCZ123 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx3-24 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·34⟩ c4) ▸
       at 0 6 (Bx2-314 ∷ []) (refl) ▸ done


-- nat 2 BOX(2;3014): 8 steps
lem-nat-2-BOX⟨2·3014⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx2-3014 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2014 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·3014⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx2-3014 ∷ []) (Bx3-2014 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff203 ∷ Bx3-214 ∷ Toff203 ∷ CCZ023 ∷ Bx3-214 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ023 ∷ []) (CCZ023 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff302 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff203 ∷ []) (Toff302 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx2-314 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·214⟩ c4) ▸
       at 3 2 (Toff302 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff203 ∷ []) (Toff302 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ023 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ023 ∷ []) (CCZ023 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx2-314 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·214⟩ c4) ▸
       at 0 6 (Bx3-2014 ∷ []) (refl) ▸ done


-- nat 3 BOX(4;23): 3 steps
lem-nat-3-BOX⟨4·23⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx4-23 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-24 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨4·23⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx4-23 ∷ []) (Bx3-24 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CZ23 ∷ []) (refl) ▸
       at 0 2 (CZ24 ∷ Sw34 ∷ []) (lem-nat-3-CZ23 c4) ▸
       at 0 1 (Bx3-24 ∷ []) (refl) ▸ done


-- nat 3 BOX(2;413): 8 steps
lem-nat-3-BOX⟨2·413⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx2-413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-314 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨2·413⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx2-413 ∷ []) (Bx2-314 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff214 ∷ Bx4-23 ∷ Toff214 ∷ CCZ124 ∷ Bx4-23 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw34 ∷ []) (lem-nat-3-CCZ124 c4) ▸
       at 1 2 (Toff213 ∷ Sw34 ∷ []) (lem-nat-3-TOFF214 c4) ▸
       at 2 2 (Bx3-24 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·23⟩ c4) ▸
       at 3 2 (Toff213 ∷ Sw34 ∷ []) (lem-nat-3-TOFF214 c4) ▸
       at 4 2 (CCZ123 ∷ Sw34 ∷ []) (lem-nat-3-CCZ124 c4) ▸
       at 5 2 (Bx3-24 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·23⟩ c4) ▸
       at 0 6 (Bx2-314 ∷ []) (refl) ▸ done


-- nat 3 BOX(4;2013): 8 steps
lem-nat-3-BOX⟨4·2013⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx4-2013 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2014 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨4·2013⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx4-2013 ∷ []) (Bx3-2014 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff402 ∷ Bx2-413 ∷ Toff402 ∷ CCZ024 ∷ Bx2-413 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 c4) ▸
       at 1 2 (Toff302 ∷ Sw34 ∷ []) (lem-nat-3-TOFF402 c4) ▸
       at 2 2 (Bx2-314 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·413⟩ c4) ▸
       at 3 2 (Toff302 ∷ Sw34 ∷ []) (lem-nat-3-TOFF402 c4) ▸
       at 4 2 (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 c4) ▸
       at 5 2 (Bx2-314 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·413⟩ c4) ▸
       at 0 6 (Bx3-2014 ∷ []) (refl) ▸ done


-- nat 3 BOX(3;24): 3 steps
lem-nat-3-BOX⟨3·24⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx3-24 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-23 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨3·24⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx3-24 ∷ []) (Bx4-23 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CZ24 ∷ []) (refl) ▸
       at 0 2 (CZ23 ∷ Sw34 ∷ []) (lem-nat-3-CZ24 c4) ▸
       at 0 1 (Bx4-23 ∷ []) (refl) ▸ done


-- nat 3 BOX(2;314): 8 steps
lem-nat-3-BOX⟨2·314⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx2-314 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-413 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨2·314⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx2-314 ∷ []) (Bx2-413 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff213 ∷ Bx3-24 ∷ Toff213 ∷ CCZ123 ∷ Bx3-24 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw34 ∷ []) (lem-nat-3-CCZ123 c4) ▸
       at 1 2 (Toff214 ∷ Sw34 ∷ []) (lem-nat-3-TOFF213 c4) ▸
       at 2 2 (Bx4-23 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·24⟩ c4) ▸
       at 3 2 (Toff214 ∷ Sw34 ∷ []) (lem-nat-3-TOFF213 c4) ▸
       at 4 2 (CCZ124 ∷ Sw34 ∷ []) (lem-nat-3-CCZ123 c4) ▸
       at 5 2 (Bx4-23 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·24⟩ c4) ▸
       at 0 6 (Bx2-413 ∷ []) (refl) ▸ done


-- nat 3 BOX(3;2014): 8 steps
lem-nat-3-BOX⟨3·2014⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx3-2014 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2013 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨3·2014⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx3-2014 ∷ []) (Bx4-2013 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff302 ∷ Bx2-314 ∷ Toff302 ∷ CCZ023 ∷ Bx2-314 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw34 ∷ []) (lem-nat-3-CCZ023 c4) ▸
       at 1 2 (Toff402 ∷ Sw34 ∷ []) (lem-nat-3-TOFF302 c4) ▸
       at 2 2 (Bx2-413 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·314⟩ c4) ▸
       at 3 2 (Toff402 ∷ Sw34 ∷ []) (lem-nat-3-TOFF302 c4) ▸
       at 4 2 (CCZ024 ∷ Sw34 ∷ []) (lem-nat-3-CCZ023 c4) ▸
       at 5 2 (Bx2-413 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·314⟩ c4) ▸
       at 0 6 (Bx4-2013 ∷ []) (refl) ▸ done


-- nat 2 BOX(4;12): 3 steps
lem-nat-2-BOX⟨4·12⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx4-12 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-13 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·12⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx4-12 ∷ []) (Bx4-13 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ12 ∷ []) (refl) ▸
       at 0 2 (CZ13 ∷ Sw23 ∷ []) (lem-nat-2-CZ12 c4) ▸
       at 0 1 (Bx4-13 ∷ []) (refl) ▸ done


-- nat 2 BOX(1;432): 8 steps
lem-nat-2-BOX⟨1·432⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx1-432 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-423 ∷ Sw23 ∷ []) ⟫ʷ
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
lem-nat-2-BOX⟨4·1032⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx4-1032 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1023 ∷ Sw23 ∷ []) ⟫ʷ
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


-- nat 1 SBOX(0;1;42;3): 7 steps
lem-nat-1-SBOX⟨0·1·42·3⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-41-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨0·1·42·3⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb0-1-42-3 ∷ []) (Sb0-2-41-3 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 0 2 (Bx0-2413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1423⟩ c4) ▸
       at 1 2 (Toff314 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff324 ∷ []) (Toff314 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb0-2-3-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·3·2⟩ c4) ▸
       at 3 2 (Toff314 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff324 ∷ []) (Toff314 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Sb⁻0-2-3-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨0·1·3·2⟩ c4) ▸
       at 0 5 (Sb0-2-41-3 ∷ []) (refl) ▸ done


-- nat 1 SBOX(0;2;41;3): 7 steps
lem-nat-1-SBOX⟨0·2·41·3⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb0-2-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨0·2·41·3⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb0-2-41-3 ∷ []) (Sb0-1-42-3 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx0-2413 ∷ Toff314 ∷ Sb0-2-3-1 ∷ Toff314 ∷ Sb⁻0-2-3-1 ∷ []) (refl) ▸
       at 0 2 (Bx0-1423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2413⟩ c4) ▸
       at 1 2 (Toff324 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff314 ∷ []) (Toff324 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb0-1-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·3·1⟩ c4) ▸
       at 3 2 (Toff324 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff314 ∷ []) (Toff324 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Sb⁻0-1-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨0·2·3·1⟩ c4) ▸
       at 0 5 (Sb0-1-42-3 ∷ []) (refl) ▸ done


-- nat 2 SBOX(4;0;1;3): 2 steps
lem-nat-2-SBOX⟨4·0·1·3⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb4-0-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-0-1-2 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨4·0·1·3⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb4-0-1-3 ∷ []) (Sb4-0-1-2 ∷ Sw23 ∷ [])
  b0 = at 0 2 (Sb4-0-1-3 ∷ Sw23 ∷ []) (sym (c₂ (CS) (Swap))) ▸
       at 0 1 (Sb4-0-1-2 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 3 SBOX(3;0;1;2): 2 steps
lem-nat-3-SBOX⟨3·0·1·2⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb3-0-1-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-0-1-2 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨3·0·1·2⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb3-0-1-2 ∷ []) (Sb4-0-1-2 ∷ Sw34 ∷ [])
  b0 = at 0 2 (Sb3-0-1-2 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸
       at 0 1 (Sb4-0-1-2 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 3 SBOX(4;0;1;2): 2 steps
lem-nat-3-SBOX⟨4·0·1·2⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb4-0-1-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-1-2 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨4·0·1·2⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb4-0-1-2 ∷ []) (Sb3-0-1-2 ∷ Sw34 ∷ [])
  b0 = at 0 2 (Sb4-0-1-2 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸
       at 0 1 (Sb3-0-1-2 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 SBOX(3;1;0;2): 3 steps
lem-nat-0-SBOX⟨3·1·0·2⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb3-1-0-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-1-2 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨3·1·0·2⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb3-1-0-2 ∷ []) (Sb3-0-1-2 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS01 ∷ []) (refl) ▸
       at 0 2 (CS01 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS01 ∷ []) (CS01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb3-0-1-2 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(4;0;1;3): 2 steps
lem-nat-2-SBOXd⟨4·0·1·3⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb⁻4-0-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻4-0-1-2 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨4·0·1·3⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻4-0-1-3 ∷ []) (Sb⁻4-0-1-2 ∷ Sw23 ∷ [])
  b0 = at 0 2 (Sb⁻4-0-1-3 ∷ Sw23 ∷ []) (sym (c₂ (CS • CS • CS) (Swap))) ▸
       at 0 1 (Sb⁻4-0-1-2 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 3 SBOXd(3;0;1;2): 2 steps
lem-nat-3-SBOXd⟨3·0·1·2⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb⁻3-0-1-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻4-0-1-2 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨3·0·1·2⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb⁻3-0-1-2 ∷ []) (Sb⁻4-0-1-2 ∷ Sw34 ∷ [])
  b0 = at 0 2 (Sb⁻3-0-1-2 ∷ Sw34 ∷ []) (sym (c₂ (CS • CS • CS) (Swap ↑))) ▸
       at 0 1 (Sb⁻4-0-1-2 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 3 SBOXd(4;0;1;2): 2 steps
lem-nat-3-SBOXd⟨4·0·1·2⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb⁻4-0-1-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻3-0-1-2 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨4·0·1·2⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb⁻4-0-1-2 ∷ []) (Sb⁻3-0-1-2 ∷ Sw34 ∷ [])
  b0 = at 0 2 (Sb⁻4-0-1-2 ∷ Sw34 ∷ []) (sym (c₂ (CS • CS • CS) (Swap ↑))) ▸
       at 0 1 (Sb⁻3-0-1-2 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 SBOXd(3;1;0;2): 3 steps
lem-nat-0-SBOXd⟨3·1·0·2⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb⁻3-1-0-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻3-0-1-2 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨3·1·0·2⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻3-1-0-2 ∷ []) (Sb⁻3-0-1-2 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS01⁻ ∷ []) (refl) ▸
       at 0 2 (CS01⁻ ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb⁻3-0-1-2 ∷ []) (refl) ▸ done

