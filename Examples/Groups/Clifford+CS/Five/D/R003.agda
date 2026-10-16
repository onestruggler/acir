{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.R003 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (WsL ; wl0001 ; wl0006 ; wl0007 ; wl0008 ; wl0009 ; wl0010 ; wl0011 ; wl0012 ; wl0013 ; wl0014 ; wl0015 ; wl0016 ; wl0017 ; wl0018 ; wl0019 ; wl0020 ; wl0021 ; wl0022 ; wl0028 ; wl0030 ; wl0031 ; wl0037 ; wl0038 ; wl0039 ; wl0040 ; wl0048 ; wl0056 ; wl0057 ; wl0058 ; wl0059 ; wl0061 ; wl0062 ; wl0067 ; wl0068 ; wl0070 ; wl0071 ; wl0072 ; wl0073 ; wl0074 ; wl0075 ; wl0076 ; wl0077 ; wl0078 ; wl0079 ; wl0080 ; wl0081 ; wl0082 ; wl0083)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-nat-1-CCZ024 ; lem-nat-2-CCZ012 ; lem-nat-2-CCZ024 ; lem-nat-2-CCZ034 ; lem-nat-2-TOFF012 ; lem-nat-3-CCZ014 ; lem-nat-3-CCZ034 ; lem-nat-3-TOFF013 ; lem-nat-3-TOFF014)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-0-CCZ124 ; lem-nat-1-BOX⟨0·13⟩ ; lem-nat-1-CCZ014 ; lem-nat-2-BOX⟨0·23⟩ ; lem-nat-2-CCZ134 ; lem-nat-2-TOFF204 ; lem-nat-2-TOFF304 ; lem-nat-3-BOX⟨4·023⟩ ; lem-nat-3-CCZ013)
-- nat 3 BOX(0;4123): 8 steps
lem-nat-3-BOX⟨0·4123⟩ : WsL → ⟪ (Sw34 ∷ Bx0-4123 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3124 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·4123⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx0-4123 ∷ []) (Bx0-3124 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff014 ∷ Bx4-023 ∷ Toff014 ∷ CCZ014 ∷ Bx4-023 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4) ▸
       at 1 2 (Toff013 ∷ Sw34 ∷ []) (lem-nat-3-TOFF014 c4) ▸
       at 2 2 (Bx3-024 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·023⟩ c4) ▸
       at 3 2 (Toff013 ∷ Sw34 ∷ []) (lem-nat-3-TOFF014 c4) ▸
       at 4 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4) ▸
       at 5 2 (Bx3-024 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·023⟩ c4) ▸
       at 0 6 (Bx0-3124 ∷ []) (refl) ▸ done


-- nat 0 CCZ014: 60 steps
lem-nat-0-CCZ014 : WsL → ⟪ (Sw01 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-CCZ014 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (run b7)))))))
  where
  b0 : Chain (Sw01 ∷ CCZ014 ∷ []) (Sw01 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ CCZ013 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 2 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 4 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw01 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw34 ∷ []) (Sw01 ∷ CS14 ∷ CX01 ∷ Sw34 ∷ CS13⁻ ∷ Sw34 ∷ Sw34 ∷ CX01 ∷ CS03 ∷ Sw34 ∷ [])
  b1 = at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 6 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0006 c4) ▸
       at 3 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 1 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 5 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸ done

  b2 : Chain (Sw01 ∷ CS14 ∷ CX01 ∷ Sw34 ∷ CS13⁻ ∷ Sw34 ∷ Sw34 ∷ CX01 ∷ CS03 ∷ Sw34 ∷ []) (Sw34 ∷ CS03 ∷ Sw01 ∷ Sw34 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ [])
  b2 = at 3 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 5 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0007 c4) ▸
       at 1 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 1 2 (CS03 ∷ Sw01 ∷ []) (sym (wl0019 c4)) ▸ done

  b3 : Chain (Sw34 ∷ CS03 ∷ Sw01 ∷ Sw34 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ []) (CS04 ∷ CX10 ∷ CS04⁻ ∷ Sw01 ∷ CX01 ∷ CS04 ∷ [])
  b3 = at 2 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 0 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (CX10 ∷ Sw01 ∷ []) (sym (wl0070 c4)) ▸
       at 3 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 3 2 (CS03⁻ ∷ Sw01 ∷ []) (sym (wl0022 c4)) ▸
       at 4 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 2 3 (CS04⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b4 : Chain (CS04 ∷ CX10 ∷ CS04⁻ ∷ Sw01 ∷ CX01 ∷ CS04 ∷ []) (Sw34 ∷ Sw34 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ CX10 ∷ CS04⁻ ∷ CX10 ∷ CS14 ∷ Sw01 ∷ [])
  b4 = at 3 2 (CX10 ∷ Sw01 ∷ []) (sym (wl0070 c4)) ▸
       at 5 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 5 2 (CS13 ∷ Sw01 ∷ []) (sym (wl0061 c4)) ▸
       at 6 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 4 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 2 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b5 : Chain (Sw34 ∷ Sw34 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ CX10 ∷ CS04⁻ ∷ CX10 ∷ CS14 ∷ Sw01 ∷ []) (Sw34 ∷ Sw23 ∷ Sw23 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ Sw34 ∷ Sw01 ∷ [])
  b5 = at 1 2 [] (wl0007 c4) ▸
       at 2 2 (CX10 ∷ Sw34 ∷ []) (sym (c₂ (CX₁₀) (Swap ↑))) ▸
       at 4 1 (Sw34 ∷ CS03⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0007 c4) ▸
       at 4 2 (CX10 ∷ Sw34 ∷ []) (sym (c₂ (CX₁₀) (Swap ↑))) ▸
       at 6 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0007 c4) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸ done

  b6 : Chain (Sw34 ∷ Sw23 ∷ Sw23 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ Sw34 ∷ Sw01 ∷ []) (Sw34 ∷ Sw23 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ Sw23 ∷ Sw34 ∷ Sw01 ∷ [])
  b6 = at 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (wl0006 c4) ▸
       at 3 2 (CX10 ∷ Sw23 ∷ []) (sym (c₂ (CX₁₀) (Swap))) ▸
       at 5 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0006 c4) ▸
       at 5 2 (CX10 ∷ Sw23 ∷ []) (sym (c₂ (CX₁₀) (Swap))) ▸
       at 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0006 c4) ▸ done

  b7 : Chain (Sw34 ∷ Sw23 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ Sw23 ∷ Sw34 ∷ Sw01 ∷ []) (CCZ014 ∷ Sw01 ∷ [])
  b7 = at 2 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wl0071 c4) ▸
       at 2 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (CCZ014 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 TOFF104: 75 steps
lem-nat-0-TOFF104 : WsL → ⟪ (Sw01 ∷ Toff104 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-TOFF104 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (run b9)))))))))
  where
  b0 : Chain (Sw01 ∷ Toff104 ∷ []) (Sw01 ∷ Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Toff103 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 3 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸ done

  b1 : Chain (Sw01 ∷ Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw34 ∷ []) (Sw01 ∷ K1 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw34 ∷ [])
  b1 = at 5 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 7 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 10 2 [] (wl0006 c4) ▸
       at 1 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸ done

  b2 : Chain (Sw01 ∷ K1 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw34 ∷ []) (Sw01 ∷ K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw34 ∷ K1 ∷ ι ∷ Sw34 ∷ [])
  b2 = at 4 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 2 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 6 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 4 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 6 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸ done

  b3 : Chain (Sw01 ∷ K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw34 ∷ K1 ∷ ι ∷ Sw34 ∷ []) (K0 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw01 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K1 ∷ ι ∷ [])
  b3 = at 7 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 8 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 9 2 [] (wl0007 c4) ▸
       at 0 2 (K0 ∷ Sw01 ∷ []) (sym (wl0031 c4)) ▸
       at 2 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 2 2 (CS03 ∷ Sw01 ∷ []) (sym (wl0019 c4)) ▸
       at 3 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸ done

  b4 : Chain (K0 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw01 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K1 ∷ ι ∷ []) (K0 ∷ CS04 ∷ CX10 ∷ CS04⁻ ∷ CX10 ∷ Sw01 ∷ CS04 ∷ K1 ∷ ι ∷ [])
  b4 = at 1 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CX10 ∷ Sw01 ∷ []) (sym (wl0070 c4)) ▸
       at 4 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 4 2 (CS03⁻ ∷ Sw01 ∷ []) (sym (wl0022 c4)) ▸
       at 5 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 3 3 (CS04⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX10 ∷ Sw01 ∷ []) (sym (wl0070 c4)) ▸ done

  b5 : Chain (K0 ∷ CS04 ∷ CX10 ∷ CS04⁻ ∷ CX10 ∷ Sw01 ∷ CS04 ∷ K1 ∷ ι ∷ []) (Sw34 ∷ Sw34 ∷ K0 ∷ CS04 ∷ CX10 ∷ CS04⁻ ∷ CX10 ∷ CS14 ∷ K0 ∷ ι ∷ Sw01 ∷ [])
  b5 = at 6 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 6 2 (CS13 ∷ Sw01 ∷ []) (sym (wl0061 c4)) ▸
       at 7 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 5 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K0 ∷ Sw01 ∷ []) (sym (wl0031 c4)) ▸
       at 7 2 (ι ∷ Sw01 ∷ []) (wl0030 c4) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸ done

  b6 : Chain (Sw34 ∷ Sw34 ∷ K0 ∷ CS04 ∷ CX10 ∷ CS04⁻ ∷ CX10 ∷ CS14 ∷ K0 ∷ ι ∷ Sw01 ∷ []) (Sw34 ∷ K0 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ Sw34 ∷ Sw34 ∷ CS13 ∷ Sw34 ∷ K0 ∷ ι ∷ Sw01 ∷ [])
  b6 = at 1 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 3 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (wl0007 c4) ▸
       at 3 2 (CX10 ∷ Sw34 ∷ []) (sym (c₂ (CX₁₀) (Swap ↑))) ▸
       at 5 1 (Sw34 ∷ CS03⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0007 c4) ▸
       at 5 2 (CX10 ∷ Sw34 ∷ []) (sym (c₂ (CX₁₀) (Swap ↑))) ▸
       at 7 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b7 : Chain (Sw34 ∷ K0 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ Sw34 ∷ Sw34 ∷ CS13 ∷ Sw34 ∷ K0 ∷ ι ∷ Sw01 ∷ []) (Sw34 ∷ Sw23 ∷ K0 ∷ CS02 ∷ CX10 ∷ Sw23 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw01 ∷ [])
  b7 = at 6 2 [] (wl0007 c4) ▸
       at 7 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 8 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 2 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0006 c4) ▸
       at 4 2 (CX10 ∷ Sw23 ∷ []) (sym (c₂ (CX₁₀) (Swap))) ▸ done

  b8 : Chain (Sw34 ∷ Sw23 ∷ K0 ∷ CS02 ∷ CX10 ∷ Sw23 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw01 ∷ []) (Sw34 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw01 ∷ [])
  b8 = at 6 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0006 c4) ▸
       at 6 2 (CX10 ∷ Sw23 ∷ []) (sym (c₂ (CX₁₀) (Swap))) ▸
       at 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0006 c4) ▸
       at 8 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 2 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (wl0072 c4) ▸ done

  b9 : Chain (Sw34 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw01 ∷ []) (Toff014 ∷ Sw01 ∷ [])
  b9 = at 2 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Toff014 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 TOFF412: 70 steps
lem-nat-0-TOFF412 : WsL → ⟪ (Sw01 ∷ Toff412 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-TOFF412 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (run b8))))))))
  where
  b0 : Chain (Sw01 ∷ Toff412 ∷ []) (Sw01 ∷ K4 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ Sw34 ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Toff312 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (K4 ∷ Sw34 ∷ []) (sym (wl0067 c4)) ▸
       at 4 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 2 3 (CS24 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 6 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 4 3 (CS24⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw01 ∷ K4 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ Sw34 ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ Sw34 ∷ []) (K4 ∷ CS24 ∷ Sw01 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K4 ∷ ι1 ∷ [])
  b1 = at 5 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 6 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K4 ∷ Sw34 ∷ []) (sym (wl0067 c4)) ▸
       at 8 2 (ι1 ∷ Sw34 ∷ []) (sym (c₂ (iI ↑) (Swap ↑))) ▸
       at 9 2 [] (wl0007 c4) ▸
       at 0 2 (K4 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ ↑)) ▸
       at 1 2 (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑)) ▸ done

  b2 : Chain (K4 ∷ CS24 ∷ Sw01 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K4 ∷ ι1 ∷ []) (K4 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ Sw01 ∷ K4 ∷ ι1 ∷ [])
  b2 = at 2 2 (CX02 ∷ Sw01 ∷ []) (sym (wl0048 c4)) ▸
       at 3 2 (CS24⁻ ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • (CS • CS • CS) • Swap ↑)) ▸
       at 4 2 (CX02 ∷ Sw01 ∷ []) (sym (wl0048 c4)) ▸
       at 6 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 6 2 (CS03 ∷ Sw01 ∷ []) (sym (wl0019 c4)) ▸
       at 7 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 5 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸ done

  b3 : Chain (K4 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ Sw01 ∷ K4 ∷ ι1 ∷ []) (Sw12 ∷ K4 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ Sw12 ∷ CX02 ∷ CS04 ∷ K4 ∷ ι1 ∷ Sw01 ∷ [])
  b3 = at 6 2 (K4 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ ↑)) ▸
       at 7 2 (ι1 ∷ Sw01 ∷ []) (wl0073 c4) ▸
       at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 1 2 (K4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K ↑)) ▸
       at 2 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0017 c4)) ▸
       at 4 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0001 c4) ▸
       at 4 2 (CS14⁻ ∷ Sw12 ∷ []) (sym (wl0018 c4)) ▸ done

  b4 : Chain (Sw12 ∷ K4 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ Sw12 ∷ CX02 ∷ CS04 ∷ K4 ∷ ι1 ∷ Sw01 ∷ []) (Sw12 ∷ K4 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K4 ∷ Sw12 ∷ ι1 ∷ Sw01 ∷ [])
  b4 = at 6 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0001 c4) ▸
       at 7 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 7 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 c4)) ▸
       at 8 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 6 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K ↑)) ▸ done

  b5 : Chain (Sw12 ∷ K4 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K4 ∷ Sw12 ∷ ι1 ∷ Sw01 ∷ []) (Sw12 ∷ Sw34 ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw34 ∷ CX01 ∷ CS04 ∷ K4 ∷ ι1 ∷ Sw12 ∷ Sw01 ∷ [])
  b5 = at 8 2 (ι1 ∷ Sw12 ∷ []) (wl0074 c4) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 2 2 (K3 ∷ Sw34 ∷ []) (sym (wl0068 c4)) ▸
       at 4 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0007 c4) ▸
       at 4 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 6 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0007 c4) ▸ done

  b6 : Chain (Sw12 ∷ Sw34 ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw34 ∷ CX01 ∷ CS04 ∷ K4 ∷ ι1 ∷ Sw12 ∷ Sw01 ∷ []) (Sw12 ∷ Sw34 ∷ Sw23 ∷ K2 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι1 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ [])
  b6 = at 6 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0007 c4) ▸
       at 8 2 (K3 ∷ Sw34 ∷ []) (sym (wl0068 c4)) ▸
       at 9 2 (ι1 ∷ Sw34 ∷ []) (sym (c₂ (iI ↑) (Swap ↑))) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 3 2 (K2 ∷ Sw23 ∷ []) (sym (wl0058 c4)) ▸
       at 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b7 : Chain (Sw12 ∷ Sw34 ∷ Sw23 ∷ K2 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι1 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ []) (Sw12 ∷ Sw34 ∷ Sw23 ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ Sw23 ∷ ι1 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ [])
  b7 = at 4 2 [] (wl0006 c4) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0006 c4) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0006 c4) ▸
       at 9 2 (K2 ∷ Sw23 ∷ []) (sym (wl0058 c4)) ▸ done

  b8 : Chain (Sw12 ∷ Sw34 ∷ Sw23 ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ Sw23 ∷ ι1 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ []) (Toff402 ∷ Sw01 ∷ [])
  b8 = at 10 2 (ι1 ∷ Sw23 ∷ []) (sym (c₂ (iI ↑) (Swap))) ▸
       at 3 8 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (sym (wl0075 c4)) ▸
       at 3 8 (Toff201 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (Toff301 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff401 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Toff402 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 BOX(1;43): 2 steps
lem-nat-0-BOX⟨1·43⟩ : WsL → ⟪ (Sw01 ∷ Bx1-43 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-43 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·43⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-43 ∷ []) (Bx0-43 ∷ Sw01 ∷ [])
  b0 = at 0 2 (Bx1-43 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑)) ▸
       at 0 1 (Bx0-43 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 BOX(4;123): 8 steps
lem-nat-0-BOX⟨4·123⟩ : WsL → ⟪ (Sw01 ∷ Bx4-123 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-023 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·123⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx4-123 ∷ []) (Bx4-023 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff412 ∷ Bx1-43 ∷ Toff412 ∷ CCZ124 ∷ Bx1-43 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 1 2 (Toff402 ∷ Sw01 ∷ []) (lem-nat-0-TOFF412 c4) ▸
       at 2 2 (Bx0-43 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·43⟩ c4) ▸
       at 3 2 (Toff402 ∷ Sw01 ∷ []) (lem-nat-0-TOFF412 c4) ▸
       at 4 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 5 2 (Bx0-43 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·43⟩ c4) ▸
       at 0 6 (Bx4-023 ∷ []) (refl) ▸ done


-- nat 0 BOX(1;4023): 8 steps
lem-nat-0-BOX⟨1·4023⟩ : WsL → ⟪ (Sw01 ∷ Bx1-4023 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4123 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·4023⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-4023 ∷ []) (Bx0-4123 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff104 ∷ Bx4-123 ∷ Toff104 ∷ CCZ014 ∷ Bx4-123 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 1 2 (Toff014 ∷ Sw01 ∷ []) (lem-nat-0-TOFF104 c4) ▸
       at 2 2 (Bx4-023 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·123⟩ c4) ▸
       at 3 2 (Toff014 ∷ Sw01 ∷ []) (lem-nat-0-TOFF104 c4) ▸
       at 4 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 5 2 (Bx4-023 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·123⟩ c4) ▸
       at 0 6 (Bx0-4123 ∷ []) (refl) ▸ done


-- nat 0 TOFF014: 75 steps
lem-nat-0-TOFF014 : WsL → ⟪ (Sw01 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff104 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-TOFF014 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (run b9)))))))))
  where
  b0 : Chain (Sw01 ∷ Toff014 ∷ []) (Sw01 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Toff013 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 3 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸ done

  b1 : Chain (Sw01 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ []) (Sw01 ∷ K0 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ [])
  b1 = at 5 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 7 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 10 2 [] (wl0006 c4) ▸
       at 1 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸ done

  b2 : Chain (Sw01 ∷ K0 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ []) (Sw01 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw34 ∷ K0 ∷ ι ∷ Sw34 ∷ [])
  b2 = at 4 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 2 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 6 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 4 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 6 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸ done

  b3 : Chain (Sw01 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw34 ∷ K0 ∷ ι ∷ Sw34 ∷ []) (K1 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw01 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ [])
  b3 = at 7 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 8 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 9 2 [] (wl0007 c4) ▸
       at 0 2 (K1 ∷ Sw01 ∷ []) (sym (wl0076 c4)) ▸
       at 2 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 2 2 (CS03 ∷ Sw01 ∷ []) (sym (wl0019 c4)) ▸
       at 3 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸ done

  b4 : Chain (K1 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw01 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ []) (K1 ∷ CS04 ∷ CX10 ∷ CS04⁻ ∷ CX10 ∷ Sw01 ∷ CS04 ∷ K0 ∷ ι ∷ [])
  b4 = at 1 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CX10 ∷ Sw01 ∷ []) (sym (wl0070 c4)) ▸
       at 4 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 4 2 (CS03⁻ ∷ Sw01 ∷ []) (sym (wl0022 c4)) ▸
       at 5 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 3 3 (CS04⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX10 ∷ Sw01 ∷ []) (sym (wl0070 c4)) ▸ done

  b5 : Chain (K1 ∷ CS04 ∷ CX10 ∷ CS04⁻ ∷ CX10 ∷ Sw01 ∷ CS04 ∷ K0 ∷ ι ∷ []) (Sw34 ∷ Sw34 ∷ K1 ∷ CS04 ∷ CX10 ∷ CS04⁻ ∷ CX10 ∷ CS14 ∷ K1 ∷ ι ∷ Sw01 ∷ [])
  b5 = at 6 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 6 2 (CS13 ∷ Sw01 ∷ []) (sym (wl0061 c4)) ▸
       at 7 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 5 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K1 ∷ Sw01 ∷ []) (sym (wl0076 c4)) ▸
       at 7 2 (ι ∷ Sw01 ∷ []) (wl0030 c4) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸ done

  b6 : Chain (Sw34 ∷ Sw34 ∷ K1 ∷ CS04 ∷ CX10 ∷ CS04⁻ ∷ CX10 ∷ CS14 ∷ K1 ∷ ι ∷ Sw01 ∷ []) (Sw34 ∷ K1 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ Sw34 ∷ Sw34 ∷ CS13 ∷ Sw34 ∷ K1 ∷ ι ∷ Sw01 ∷ [])
  b6 = at 1 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 3 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (wl0007 c4) ▸
       at 3 2 (CX10 ∷ Sw34 ∷ []) (sym (c₂ (CX₁₀) (Swap ↑))) ▸
       at 5 1 (Sw34 ∷ CS03⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0007 c4) ▸
       at 5 2 (CX10 ∷ Sw34 ∷ []) (sym (c₂ (CX₁₀) (Swap ↑))) ▸
       at 7 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b7 : Chain (Sw34 ∷ K1 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ Sw34 ∷ Sw34 ∷ CS13 ∷ Sw34 ∷ K1 ∷ ι ∷ Sw01 ∷ []) (Sw34 ∷ Sw23 ∷ K1 ∷ CS02 ∷ CX10 ∷ Sw23 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw01 ∷ [])
  b7 = at 6 2 [] (wl0007 c4) ▸
       at 7 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 8 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 2 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0006 c4) ▸
       at 4 2 (CX10 ∷ Sw23 ∷ []) (sym (c₂ (CX₁₀) (Swap))) ▸ done

  b8 : Chain (Sw34 ∷ Sw23 ∷ K1 ∷ CS02 ∷ CX10 ∷ Sw23 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw01 ∷ []) (Sw34 ∷ Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw01 ∷ [])
  b8 = at 6 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0006 c4) ▸
       at 6 2 (CX10 ∷ Sw23 ∷ []) (sym (c₂ (CX₁₀) (Swap))) ▸
       at 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0006 c4) ▸
       at 8 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 2 8 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (wl0077 c4) ▸ done

  b9 : Chain (Sw34 ∷ Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw01 ∷ []) (Toff104 ∷ Sw01 ∷ [])
  b9 = at 2 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff103 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Toff104 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 1 TOFF204: 2 steps
lem-nat-1-TOFF204 : WsL → ⟪ (Sw12 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff104 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-TOFF204 c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Toff204 ∷ []) (Toff104 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sw12 ∷ Toff104 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0001 c4) ▸ done


-- nat 1 BOX(2;43): 2 steps
lem-nat-1-BOX⟨2·43⟩ : WsL → ⟪ (Sw12 ∷ Bx2-43 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-43 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·43⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx2-43 ∷ []) (Bx1-43 ∷ Sw12 ∷ [])
  b0 = at 0 2 (Bx2-43 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CZ)) ▸
       at 0 1 (Bx1-43 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 1 BOX(4;213): 8 steps
lem-nat-1-BOX⟨4·213⟩ : WsL → ⟪ (Sw12 ∷ Bx4-213 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-123 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·213⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx4-213 ∷ []) (Bx4-123 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff412 ∷ Bx2-43 ∷ Toff412 ∷ CCZ124 ∷ Bx2-43 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw12 ∷ []) (sym (wl0078 c4)) ▸
       at 1 2 (Toff412 ∷ Sw12 ∷ []) (wl0079 c4) ▸
       at 2 2 (Bx1-43 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·43⟩ c4) ▸
       at 3 2 (Toff412 ∷ Sw12 ∷ []) (wl0079 c4) ▸
       at 4 2 (CCZ124 ∷ Sw12 ∷ []) (sym (wl0078 c4)) ▸
       at 5 2 (Bx1-43 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·43⟩ c4) ▸
       at 0 6 (Bx4-123 ∷ []) (refl) ▸ done


-- nat 1 BOX(2;4013): 8 steps
lem-nat-1-BOX⟨2·4013⟩ : WsL → ⟪ (Sw12 ∷ Bx2-4013 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-4023 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·4013⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx2-4013 ∷ []) (Bx1-4023 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff204 ∷ Bx4-213 ∷ Toff204 ∷ CCZ024 ∷ Bx4-213 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 1 2 (Toff104 ∷ Sw12 ∷ []) (lem-nat-1-TOFF204 c4) ▸
       at 2 2 (Bx4-123 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·213⟩ c4) ▸
       at 3 2 (Toff104 ∷ Sw12 ∷ []) (lem-nat-1-TOFF204 c4) ▸
       at 4 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 5 2 (Bx4-123 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·213⟩ c4) ▸
       at 0 6 (Bx1-4023 ∷ []) (refl) ▸ done


-- nat 1 TOFF104: 2 steps
lem-nat-1-TOFF104 : WsL → ⟪ (Sw12 ∷ Toff104 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-TOFF104 c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Toff104 ∷ []) (Toff204 ∷ Sw12 ∷ [])
  b0 = at 2 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 0 3 (Toff204 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 2 TOFF413: 2 steps
lem-nat-2-TOFF413 : WsL → ⟪ (Sw23 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-TOFF413 c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Toff413 ∷ []) (Toff412 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Toff412 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0006 c4) ▸ done


-- nat 2 BOX(3;42): 3 steps
lem-nat-2-BOX⟨3·42⟩ : WsL → ⟪ (Sw23 ∷ Bx3-42 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-43 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·42⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx3-42 ∷ []) (Bx2-43 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ24 ∷ []) (refl) ▸
       at 0 2 (CZ34 ∷ Sw23 ∷ []) (sym (wl0028 c4)) ▸
       at 0 1 (Bx2-43 ∷ []) (refl) ▸ done


-- nat 2 BOX(4;312): 8 steps
lem-nat-2-BOX⟨4·312⟩ : WsL → ⟪ (Sw23 ∷ Bx4-312 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-213 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·312⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx4-312 ∷ []) (Bx4-213 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff413 ∷ Bx3-42 ∷ Toff413 ∷ CCZ134 ∷ Bx3-42 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 1 2 (Toff412 ∷ Sw23 ∷ []) (lem-nat-2-TOFF413 c4) ▸
       at 2 2 (Bx2-43 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·42⟩ c4) ▸
       at 3 2 (Toff412 ∷ Sw23 ∷ []) (lem-nat-2-TOFF413 c4) ▸
       at 4 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 5 2 (Bx2-43 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·42⟩ c4) ▸
       at 0 6 (Bx4-213 ∷ []) (refl) ▸ done


-- nat 2 BOX(3;4012): 8 steps
lem-nat-2-BOX⟨3·4012⟩ : WsL → ⟪ (Sw23 ∷ Bx3-4012 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4013 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·4012⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx3-4012 ∷ []) (Bx2-4013 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff304 ∷ Bx4-312 ∷ Toff304 ∷ CCZ034 ∷ Bx4-312 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 1 2 (Toff204 ∷ Sw23 ∷ []) (lem-nat-2-TOFF304 c4) ▸
       at 2 2 (Bx4-213 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·312⟩ c4) ▸
       at 3 2 (Toff204 ∷ Sw23 ∷ []) (lem-nat-2-TOFF304 c4) ▸
       at 4 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 5 2 (Bx4-213 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·312⟩ c4) ▸
       at 0 6 (Bx2-4013 ∷ []) (refl) ▸ done


-- nat 0 CCZ134: 78 steps
lem-nat-0-CCZ134 : WsL → ⟪ (Sw01 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-CCZ134 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (run b9)))))))))
  where
  b0 : Chain (Sw01 ∷ CCZ134 ∷ []) (Sw01 ∷ Sw23 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ Sw34 ∷ CX12 ∷ CS13 ∷ Sw34 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ CCZ123 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 2 3 (CS24 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 6 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 4 3 (CS24⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw01 ∷ Sw23 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ Sw34 ∷ CX12 ∷ CS13 ∷ Sw34 ∷ Sw23 ∷ []) (Sw01 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ Sw23 ∷ CX12 ∷ CS14 ∷ Sw23 ∷ [])
  b1 = at 5 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 6 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0007 c4) ▸
       at 1 2 (CS34 ∷ Sw23 ∷ []) (sym (wl0011 c4)) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 2 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS34⁻ ∷ Sw23 ∷ []) (sym (wl0012 c4)) ▸ done

  b2 : Chain (Sw01 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ Sw23 ∷ CX12 ∷ CS14 ∷ Sw23 ∷ []) (CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw01 ∷ CS14 ∷ [])
  b2 = at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 4 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS14 ∷ Sw23 ∷ []) (sym (wl0021 c4)) ▸
       at 6 2 [] (wl0006 c4) ▸
       at 0 2 (CS34 ∷ Sw01 ∷ []) (c₂ (Swap) (CS ↑)) ▸
       at 1 2 (CX03 ∷ Sw01 ∷ []) (sym (wl0020 c4)) ▸
       at 2 2 (CS34⁻ ∷ Sw01 ∷ []) (c₂ (Swap) ((CS • CS • CS) ↑)) ▸
       at 3 2 (CX03 ∷ Sw01 ∷ []) (sym (wl0020 c4)) ▸ done

  b3 : Chain (CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw01 ∷ CS14 ∷ []) (Sw23 ∷ CS24 ∷ Sw23 ∷ Sw23 ∷ CX02 ∷ Sw23 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ Sw01 ∷ [])
  b3 = at 5 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 5 2 (CS03 ∷ Sw01 ∷ []) (sym (wl0019 c4)) ▸
       at 6 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 4 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 1 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0015 c4)) ▸
       at 3 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b4 : Chain (Sw23 ∷ CS24 ∷ Sw23 ∷ Sw23 ∷ CX02 ∷ Sw23 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ Sw01 ∷ []) (Sw23 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw01 ∷ [])
  b4 = at 2 2 [] (wl0006 c4) ▸
       at 3 2 (CS24⁻ ∷ Sw23 ∷ []) (sym (wl0016 c4)) ▸
       at 5 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0006 c4) ▸
       at 6 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (wl0013 c4) ▸
       at 7 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 8 2 (CS01 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸ done

  b5 : Chain (Sw23 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw01 ∷ []) (Sw23 ∷ Sw12 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ Sw12 ∷ CX02 ∷ CS04 ∷ Sw23 ∷ Sw01 ∷ [])
  b5 = at 9 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 10 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (sym (wl0013 c4)) ▸
       at 5 7 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 2 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0017 c4)) ▸
       at 4 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0001 c4) ▸
       at 4 2 (CS14⁻ ∷ Sw12 ∷ []) (sym (wl0018 c4)) ▸ done

  b6 : Chain (Sw23 ∷ Sw12 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ Sw12 ∷ CX02 ∷ CS04 ∷ Sw23 ∷ Sw01 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw34 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ [])
  b6 = at 6 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0001 c4) ▸
       at 7 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 7 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 c4)) ▸
       at 8 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 6 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸ done

  b7 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw34 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ [])
  b7 = at 4 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0007 c4) ▸
       at 4 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 6 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0007 c4) ▸
       at 6 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0007 c4) ▸ done

  b8 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw23 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ [])
  b8 = at 3 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0006 c4) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0006 c4) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b9 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw23 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ []) (CCZ034 ∷ Sw01 ∷ [])
  b9 = at 8 2 [] (wl0006 c4) ▸
       at 4 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 3 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (CCZ014 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (CCZ024 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (CCZ034 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 TOFF314: 100 steps
lem-nat-0-TOFF314 : WsL → ⟪ (Sw01 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-TOFF314 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (run b12))))))))))))
  where
  b0 : Chain (Sw01 ∷ Toff314 ∷ []) (Sw01 ∷ Sw23 ∷ K2 ∷ CS24 ∷ CX12 ∷ Sw34 ∷ CS23⁻ ∷ Sw34 ∷ Sw34 ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ Sw34 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Toff214 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ Toff213 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (K2 ∷ Sw34 ∷ []) (sym (c₃ (K ↑ ↑) (Swap))) ▸
       at 5 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 3 3 (CS24 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸ done

  b1 : Chain (Sw01 ∷ Sw23 ∷ K2 ∷ CS24 ∷ CX12 ∷ Sw34 ∷ CS23⁻ ∷ Sw34 ∷ Sw34 ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ Sw34 ∷ Sw23 ∷ []) (Sw01 ∷ K3 ∷ Sw23 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2 ∷ ι1 ∷ Sw23 ∷ [])
  b1 = at 5 3 (CS24⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 9 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 7 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K2 ∷ Sw34 ∷ []) (sym (c₃ (K ↑ ↑) (Swap))) ▸
       at 9 2 (ι1 ∷ Sw34 ∷ []) (sym (c₂ (iI ↑) (Swap ↑))) ▸
       at 10 2 [] (wl0007 c4) ▸
       at 1 2 (K3 ∷ Sw23 ∷ []) (sym (wl0057 c4)) ▸ done

  b2 : Chain (Sw01 ∷ K3 ∷ Sw23 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2 ∷ ι1 ∷ Sw23 ∷ []) (Sw01 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3 ∷ Sw23 ∷ ι1 ∷ Sw23 ∷ [])
  b2 = at 2 2 (CS34 ∷ Sw23 ∷ []) (sym (wl0011 c4)) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 3 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS34⁻ ∷ Sw23 ∷ []) (sym (wl0012 c4)) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 5 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CS14 ∷ Sw23 ∷ []) (sym (wl0021 c4)) ▸
       at 7 2 (K3 ∷ Sw23 ∷ []) (sym (wl0057 c4)) ▸ done

  b3 : Chain (Sw01 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3 ∷ Sw23 ∷ ι1 ∷ Sw23 ∷ []) (K3 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw01 ∷ Sw34 ∷ CS13 ∷ Sw34 ∷ K3 ∷ ι1 ∷ [])
  b3 = at 8 2 (ι1 ∷ Sw23 ∷ []) (sym (c₂ (iI ↑) (Swap))) ▸
       at 9 2 [] (wl0006 c4) ▸
       at 0 2 (K3 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑)) ▸
       at 1 2 (CS34 ∷ Sw01 ∷ []) (c₂ (Swap) (CS ↑)) ▸
       at 2 2 (CX03 ∷ Sw01 ∷ []) (sym (wl0020 c4)) ▸
       at 3 2 (CS34⁻ ∷ Sw01 ∷ []) (c₂ (Swap) ((CS • CS • CS) ↑)) ▸
       at 4 2 (CX03 ∷ Sw01 ∷ []) (sym (wl0020 c4)) ▸
       at 6 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b4 : Chain (K3 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw01 ∷ Sw34 ∷ CS13 ∷ Sw34 ∷ K3 ∷ ι1 ∷ []) (Sw23 ∷ K2 ∷ Sw23 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K3 ∷ ι1 ∷ Sw01 ∷ [])
  b4 = at 5 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 6 2 (CS03 ∷ Sw01 ∷ []) (sym (wl0019 c4)) ▸
       at 7 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 5 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K3 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑)) ▸
       at 7 2 (ι1 ∷ Sw01 ∷ []) (wl0073 c4) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 1 2 (K2 ∷ Sw23 ∷ []) (sym (wl0058 c4)) ▸ done

  b5 : Chain (Sw23 ∷ K2 ∷ Sw23 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K3 ∷ ι1 ∷ Sw01 ∷ []) (Sw23 ∷ K2 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ K3 ∷ ι1 ∷ Sw01 ∷ [])
  b5 = at 2 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0015 c4)) ▸
       at 4 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0006 c4) ▸
       at 4 2 (CS24⁻ ∷ Sw23 ∷ []) (sym (wl0016 c4)) ▸
       at 6 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0006 c4) ▸
       at 7 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (wl0013 c4) ▸ done

  b6 : Chain (Sw23 ∷ K2 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ K3 ∷ ι1 ∷ Sw01 ∷ []) (Sw23 ∷ Sw12 ∷ Sw12 ∷ K2 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K2 ∷ ι1 ∷ Sw23 ∷ Sw01 ∷ [])
  b6 = at 8 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 9 2 (CS01 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸
       at 10 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 11 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (sym (wl0013 c4)) ▸
       at 6 7 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K2 ∷ Sw23 ∷ []) (sym (wl0058 c4)) ▸
       at 8 2 (ι1 ∷ Sw23 ∷ []) (sym (c₂ (iI ↑) (Swap))) ▸
       at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸ done

  b7 : Chain (Sw23 ∷ Sw12 ∷ Sw12 ∷ K2 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K2 ∷ ι1 ∷ Sw23 ∷ Sw01 ∷ []) (Sw23 ∷ Sw12 ∷ K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw12 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ K2 ∷ ι1 ∷ Sw23 ∷ Sw01 ∷ [])
  b7 = at 2 2 (K1 ∷ Sw12 ∷ []) (sym (wl0062 c4)) ▸
       at 3 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0017 c4)) ▸
       at 5 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0001 c4) ▸
       at 5 2 (CS14⁻ ∷ Sw12 ∷ []) (sym (wl0018 c4)) ▸
       at 7 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0001 c4) ▸
       at 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b8 : Chain (Sw23 ∷ Sw12 ∷ K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw12 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ K2 ∷ ι1 ∷ Sw23 ∷ Sw01 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ Sw34 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K1 ∷ ι1 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ [])
  b8 = at 7 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 8 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 c4)) ▸
       at 9 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 7 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K1 ∷ Sw12 ∷ []) (sym (wl0062 c4)) ▸
       at 9 2 (ι1 ∷ Sw12 ∷ []) (wl0074 c4) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 3 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸ done

  b9 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ Sw34 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K1 ∷ ι1 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw34 ∷ K1 ∷ ι1 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ [])
  b9 = at 5 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0007 c4) ▸
       at 5 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 7 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0007 c4) ▸
       at 7 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 9 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0007 c4) ▸ done

  b10 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw34 ∷ K1 ∷ ι1 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ Sw23 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ K1 ∷ ι1 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ [])
  b10 = at 9 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 10 2 (ι1 ∷ Sw34 ∷ []) (sym (c₂ (iI ↑) (Swap ↑))) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 4 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0006 c4) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b11 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ Sw23 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ K1 ∷ ι1 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ [])
  b11 = at 7 2 [] (wl0006 c4) ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (wl0006 c4) ▸
       at 10 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 11 2 (ι1 ∷ Sw23 ∷ []) (sym (c₂ (iI ↑) (Swap))) ▸
       at 4 8 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (sym (wl0080 c4)) ▸
       at 4 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸ done

  b12 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ []) (Toff304 ∷ Sw01 ∷ [])
  b12 = at 3 3 (Toff103 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (Toff104 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff204 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Toff304 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 CCZ034: 78 steps
lem-nat-0-CCZ034 : WsL → ⟪ (Sw01 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-CCZ034 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (run b9)))))))))
  where
  b0 : Chain (Sw01 ∷ CCZ034 ∷ []) (Sw01 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ CCZ024 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw12 ∷ CCZ014 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw34 ∷ CCZ013 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸ done

  b1 : Chain (Sw01 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (Sw01 ∷ Sw23 ∷ Sw12 ∷ CS14 ∷ Sw34 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b1 = at 8 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 6 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (wl0006 c4) ▸
       at 5 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 3 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (Sw01 ∷ Sw23 ∷ Sw12 ∷ CS14 ∷ Sw34 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (Sw01 ∷ Sw23 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw12 ∷ Sw23 ∷ [])
  b2 = at 4 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 5 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 9 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 7 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0007 c4) ▸
       at 2 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0008 c4)) ▸ done

  b3 : Chain (Sw01 ∷ Sw23 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw12 ∷ Sw23 ∷ []) (Sw01 ∷ Sw23 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ CS03 ∷ Sw12 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b3 = at 5 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 3 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS24⁻ ∷ Sw12 ∷ []) (sym (wl0009 c4)) ▸
       at 7 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 5 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 7 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 c4)) ▸ done

  b4 : Chain (Sw01 ∷ Sw23 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ CS03 ∷ Sw12 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (Sw01 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ Sw23 ∷ CX02 ∷ Sw23 ∷ Sw23 ∷ CS04 ∷ Sw23 ∷ [])
  b4 = at 8 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 6 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0001 c4) ▸
       at 1 2 (CS34 ∷ Sw23 ∷ []) (sym (wl0011 c4)) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 2 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS34⁻ ∷ Sw23 ∷ []) (sym (wl0012 c4)) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸ done

  b5 : Chain (Sw01 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ Sw23 ∷ CX02 ∷ Sw23 ∷ Sw23 ∷ CS04 ∷ Sw23 ∷ []) (Sw01 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ Sw23 ∷ Sw23 ∷ [])
  b5 = at 4 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (wl0013 c4) ▸
       at 7 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 8 2 (CS01 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸
       at 9 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 10 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (sym (wl0013 c4)) ▸
       at 5 7 (CS04 ∷ []) (by-assoc Eq.refl) ▸ done

  b6 : Chain (Sw01 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ Sw23 ∷ Sw23 ∷ []) (CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ Sw34 ∷ CS13 ∷ Sw01 ∷ Sw34 ∷ [])
  b6 = at 6 2 [] (wl0006 c4) ▸
       at 0 2 (CS34 ∷ Sw01 ∷ []) (c₂ (Swap) (CS ↑)) ▸
       at 1 2 (CX13 ∷ Sw01 ∷ []) (sym (wl0081 c4)) ▸
       at 2 2 (CS34⁻ ∷ Sw01 ∷ []) (c₂ (Swap) ((CS • CS • CS) ↑)) ▸
       at 3 2 (CX13 ∷ Sw01 ∷ []) (sym (wl0081 c4)) ▸
       at 5 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 5 2 (CS13 ∷ Sw01 ∷ []) (sym (wl0061 c4)) ▸ done

  b7 : Chain (CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ Sw34 ∷ CS13 ∷ Sw01 ∷ Sw34 ∷ []) (Sw23 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ Sw23 ∷ Sw23 ∷ CX12 ∷ Sw23 ∷ CS14 ∷ Sw01 ∷ [])
  b7 = at 6 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 4 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 1 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0015 c4)) ▸
       at 3 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (wl0006 c4) ▸
       at 3 2 (CS24⁻ ∷ Sw23 ∷ []) (sym (wl0016 c4)) ▸
       at 5 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b8 : Chain (Sw23 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ Sw23 ∷ Sw23 ∷ CX12 ∷ Sw23 ∷ CS14 ∷ Sw01 ∷ []) (Sw23 ∷ Sw34 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ Sw34 ∷ CX12 ∷ CS14 ∷ Sw23 ∷ Sw01 ∷ [])
  b8 = at 4 2 [] (wl0006 c4) ▸
       at 5 2 (CS14 ∷ Sw23 ∷ []) (sym (wl0021 c4)) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 3 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (wl0007 c4) ▸
       at 3 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 5 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0007 c4) ▸ done

  b9 : Chain (Sw23 ∷ Sw34 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ Sw34 ∷ CX12 ∷ CS14 ∷ Sw23 ∷ Sw01 ∷ []) (CCZ134 ∷ Sw01 ∷ [])
  b9 = at 5 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 7 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0007 c4) ▸
       at 2 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (CCZ124 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (CCZ134 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 TOFF403: 100 steps
lem-nat-0-TOFF403 : WsL → ⟪ (Sw01 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-TOFF403 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (run b12))))))))))))
  where
  b0 : Chain (Sw01 ∷ Toff403 ∷ []) (Sw01 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K3 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Toff402 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw12 ∷ Toff401 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw34 ∷ Toff301 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (K3 ∷ Sw23 ∷ []) (sym (wl0057 c4)) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 5 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw01 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K3 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (Sw01 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b1 = at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 7 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 9 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (K3 ∷ Sw23 ∷ []) (sym (wl0057 c4)) ▸
       at 11 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸ done

  b2 : Chain (Sw01 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (Sw01 ∷ Sw23 ∷ Sw12 ∷ K4 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b2 = at 12 2 [] (wl0006 c4) ▸
       at 3 2 (K4 ∷ Sw34 ∷ []) (sym (wl0067 c4)) ▸
       at 6 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 4 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 6 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸ done

  b3 : Chain (Sw01 ∷ Sw23 ∷ Sw12 ∷ K4 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (Sw01 ∷ Sw23 ∷ K4 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K4 ∷ ι ∷ Sw12 ∷ Sw23 ∷ [])
  b3 = at 10 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 8 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K4 ∷ Sw34 ∷ []) (sym (wl0067 c4)) ▸
       at 10 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 11 2 [] (wl0007 c4) ▸
       at 2 2 (K4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K ↑)) ▸
       at 3 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0008 c4)) ▸
       at 6 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸ done

  b4 : Chain (Sw01 ∷ Sw23 ∷ K4 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K4 ∷ ι ∷ Sw12 ∷ Sw23 ∷ []) (Sw01 ∷ Sw23 ∷ K4 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ K4 ∷ ι ∷ Sw12 ∷ Sw23 ∷ [])
  b4 = at 4 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS24⁻ ∷ Sw12 ∷ []) (sym (wl0009 c4)) ▸
       at 8 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 6 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 8 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 c4)) ▸
       at 9 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸ done

  b5 : Chain (Sw01 ∷ Sw23 ∷ K4 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ K4 ∷ ι ∷ Sw12 ∷ Sw23 ∷ []) (Sw01 ∷ K4 ∷ CS34 ∷ CX03 ∷ Sw23 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K4 ∷ ι ∷ Sw23 ∷ [])
  b5 = at 7 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K ↑)) ▸
       at 9 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 10 2 [] (wl0001 c4) ▸
       at 1 2 (K4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K)) ▸
       at 2 2 (CS34 ∷ Sw23 ∷ []) (sym (wl0011 c4)) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 3 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸ done

  b6 : Chain (Sw01 ∷ K4 ∷ CS34 ∷ CX03 ∷ Sw23 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K4 ∷ ι ∷ Sw23 ∷ []) (Sw01 ∷ K4 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Sw34 ∷ K4 ∷ ι ∷ Sw23 ∷ [])
  b6 = at 4 2 (CS34⁻ ∷ Sw23 ∷ []) (sym (wl0012 c4)) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 5 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (wl0013 c4) ▸
       at 8 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 9 2 (CS01 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸
       at 10 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸ done

  b7 : Chain (Sw01 ∷ K4 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Sw34 ∷ K4 ∷ ι ∷ Sw23 ∷ []) (K4 ∷ CS34 ∷ CX13 ∷ Sw01 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K4 ∷ ι ∷ [])
  b7 = at 11 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (sym (wl0013 c4)) ▸
       at 6 7 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K)) ▸
       at 8 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 9 2 [] (wl0006 c4) ▸
       at 0 2 (K4 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ ↑)) ▸
       at 1 2 (CS34 ∷ Sw01 ∷ []) (c₂ (Swap) (CS ↑)) ▸
       at 2 2 (CX13 ∷ Sw01 ∷ []) (sym (wl0081 c4)) ▸ done

  b8 : Chain (K4 ∷ CS34 ∷ CX13 ∷ Sw01 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K4 ∷ ι ∷ []) (K4 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K4 ∷ Sw01 ∷ ι ∷ [])
  b8 = at 3 2 (CS34⁻ ∷ Sw01 ∷ []) (c₂ (Swap) ((CS • CS • CS) ↑)) ▸
       at 4 2 (CX13 ∷ Sw01 ∷ []) (sym (wl0081 c4)) ▸
       at 6 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 6 2 (CS13 ∷ Sw01 ∷ []) (sym (wl0061 c4)) ▸
       at 7 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 5 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K4 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ ↑)) ▸ done

  b9 : Chain (K4 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K4 ∷ Sw01 ∷ ι ∷ []) (Sw23 ∷ K4 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ Sw23 ∷ Sw23 ∷ CX12 ∷ Sw23 ∷ CS14 ∷ K4 ∷ ι ∷ Sw01 ∷ [])
  b9 = at 7 2 (ι ∷ Sw01 ∷ []) (wl0030 c4) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 1 2 (K4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K)) ▸
       at 2 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0015 c4)) ▸
       at 4 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0006 c4) ▸
       at 4 2 (CS24⁻ ∷ Sw23 ∷ []) (sym (wl0016 c4)) ▸
       at 6 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b10 : Chain (Sw23 ∷ K4 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ Sw23 ∷ Sw23 ∷ CX12 ∷ Sw23 ∷ CS14 ∷ K4 ∷ ι ∷ Sw01 ∷ []) (Sw23 ∷ Sw34 ∷ K3 ∷ CS23 ∷ Sw34 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K4 ∷ ι ∷ Sw23 ∷ Sw01 ∷ [])
  b10 = at 5 2 [] (wl0006 c4) ▸
       at 6 2 (CS14 ∷ Sw23 ∷ []) (sym (wl0021 c4)) ▸
       at 7 2 (K4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K)) ▸
       at 8 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 2 2 (K3 ∷ Sw34 ∷ []) (sym (wl0068 c4)) ▸
       at 4 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0007 c4) ▸ done

  b11 : Chain (Sw23 ∷ Sw34 ∷ K3 ∷ CS23 ∷ Sw34 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K4 ∷ ι ∷ Sw23 ∷ Sw01 ∷ []) (Sw23 ∷ Sw34 ∷ K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw23 ∷ Sw01 ∷ [])
  b11 = at 4 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 6 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0007 c4) ▸
       at 6 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 8 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0007 c4) ▸
       at 8 2 (K3 ∷ Sw34 ∷ []) (sym (wl0068 c4)) ▸
       at 9 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸ done

  b12 : Chain (Sw23 ∷ Sw34 ∷ K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw23 ∷ Sw01 ∷ []) (Toff413 ∷ Sw01 ∷ [])
  b12 = at 2 8 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) (wl0082 c4) ▸
       at 2 8 (Toff312 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff412 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Toff413 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 BOX(4;302): 8 steps
lem-nat-0-BOX⟨4·302⟩ : WsL → ⟪ (Sw01 ∷ Bx4-302 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-312 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·302⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx4-302 ∷ []) (Bx4-312 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff403 ∷ Bx3-42 ∷ Toff403 ∷ CCZ034 ∷ Bx3-42 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4) ▸
       at 1 2 (Toff413 ∷ Sw01 ∷ []) (lem-nat-0-TOFF403 c4) ▸
       at 2 2 (Bx3-42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CZ • Swap ↑)) ▸
       at 3 2 (Toff413 ∷ Sw01 ∷ []) (lem-nat-0-TOFF403 c4) ▸
       at 4 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4) ▸
       at 5 2 (Bx3-42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CZ • Swap ↑)) ▸
       at 0 6 (Bx4-312 ∷ []) (refl) ▸ done


-- nat 0 BOX(3;4102): 8 steps
lem-nat-0-BOX⟨3·4102⟩ : WsL → ⟪ (Sw01 ∷ Bx3-4102 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4012 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·4102⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx3-4102 ∷ []) (Bx3-4012 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff314 ∷ Bx4-302 ∷ Toff314 ∷ CCZ134 ∷ Bx4-302 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 1 2 (Toff304 ∷ Sw01 ∷ []) (lem-nat-0-TOFF314 c4) ▸
       at 2 2 (Bx4-312 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·302⟩ c4) ▸
       at 3 2 (Toff304 ∷ Sw01 ∷ []) (lem-nat-0-TOFF314 c4) ▸
       at 4 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 5 2 (Bx4-312 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·302⟩ c4) ▸
       at 0 6 (Bx3-4012 ∷ []) (refl) ▸ done


-- nat 0 TOFF304: 100 steps
lem-nat-0-TOFF304 : WsL → ⟪ (Sw01 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-TOFF304 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (run b12))))))))))))
  where
  b0 : Chain (Sw01 ∷ Toff304 ∷ []) (Sw01 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Toff204 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw12 ∷ Toff104 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw34 ∷ Toff103 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 5 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw01 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (Sw01 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b1 = at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 7 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 9 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 11 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸ done

  b2 : Chain (Sw01 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (Sw01 ∷ Sw23 ∷ Sw12 ∷ K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b2 = at 12 2 [] (wl0006 c4) ▸
       at 3 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 6 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 4 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 6 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸ done

  b3 : Chain (Sw01 ∷ Sw23 ∷ Sw12 ∷ K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (Sw01 ∷ Sw23 ∷ K2 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw23 ∷ [])
  b3 = at 10 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 8 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 10 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 11 2 [] (wl0007 c4) ▸
       at 2 2 (K2 ∷ Sw12 ∷ []) (sym (wl0056 c4)) ▸
       at 3 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0008 c4)) ▸
       at 6 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸ done

  b4 : Chain (Sw01 ∷ Sw23 ∷ K2 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw23 ∷ []) (Sw01 ∷ Sw23 ∷ K2 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw23 ∷ [])
  b4 = at 4 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS24⁻ ∷ Sw12 ∷ []) (sym (wl0009 c4)) ▸
       at 8 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 6 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 8 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 c4)) ▸
       at 9 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸ done

  b5 : Chain (Sw01 ∷ Sw23 ∷ K2 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw23 ∷ []) (Sw01 ∷ K3 ∷ CS34 ∷ CX03 ∷ Sw23 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K2 ∷ ι ∷ Sw23 ∷ [])
  b5 = at 7 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K2 ∷ Sw12 ∷ []) (sym (wl0056 c4)) ▸
       at 9 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 10 2 [] (wl0001 c4) ▸
       at 1 2 (K3 ∷ Sw23 ∷ []) (sym (wl0057 c4)) ▸
       at 2 2 (CS34 ∷ Sw23 ∷ []) (sym (wl0011 c4)) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 3 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸ done

  b6 : Chain (Sw01 ∷ K3 ∷ CS34 ∷ CX03 ∷ Sw23 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K2 ∷ ι ∷ Sw23 ∷ []) (Sw01 ∷ K3 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Sw34 ∷ K2 ∷ ι ∷ Sw23 ∷ [])
  b6 = at 4 2 (CS34⁻ ∷ Sw23 ∷ []) (sym (wl0012 c4)) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 5 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (wl0013 c4) ▸
       at 8 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 9 2 (CS01 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸
       at 10 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸ done

  b7 : Chain (Sw01 ∷ K3 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Sw34 ∷ K2 ∷ ι ∷ Sw23 ∷ []) (K3 ∷ CS34 ∷ CX13 ∷ Sw01 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K3 ∷ ι ∷ [])
  b7 = at 11 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (sym (wl0013 c4)) ▸
       at 6 7 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K3 ∷ Sw23 ∷ []) (sym (wl0057 c4)) ▸
       at 8 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 9 2 [] (wl0006 c4) ▸
       at 0 2 (K3 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑)) ▸
       at 1 2 (CS34 ∷ Sw01 ∷ []) (c₂ (Swap) (CS ↑)) ▸
       at 2 2 (CX13 ∷ Sw01 ∷ []) (sym (wl0081 c4)) ▸ done

  b8 : Chain (K3 ∷ CS34 ∷ CX13 ∷ Sw01 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K3 ∷ ι ∷ []) (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3 ∷ Sw01 ∷ ι ∷ [])
  b8 = at 3 2 (CS34⁻ ∷ Sw01 ∷ []) (c₂ (Swap) ((CS • CS • CS) ↑)) ▸
       at 4 2 (CX13 ∷ Sw01 ∷ []) (sym (wl0081 c4)) ▸
       at 6 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 6 2 (CS13 ∷ Sw01 ∷ []) (sym (wl0061 c4)) ▸
       at 7 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 5 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K3 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑)) ▸ done

  b9 : Chain (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3 ∷ Sw01 ∷ ι ∷ []) (Sw23 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ Sw23 ∷ Sw23 ∷ CX12 ∷ Sw23 ∷ CS14 ∷ K3 ∷ ι ∷ Sw01 ∷ [])
  b9 = at 7 2 (ι ∷ Sw01 ∷ []) (wl0030 c4) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 1 2 (K2 ∷ Sw23 ∷ []) (sym (wl0058 c4)) ▸
       at 2 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0015 c4)) ▸
       at 4 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0006 c4) ▸
       at 4 2 (CS24⁻ ∷ Sw23 ∷ []) (sym (wl0016 c4)) ▸
       at 6 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b10 : Chain (Sw23 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ Sw23 ∷ Sw23 ∷ CX12 ∷ Sw23 ∷ CS14 ∷ K3 ∷ ι ∷ Sw01 ∷ []) (Sw23 ∷ Sw34 ∷ K2 ∷ CS23 ∷ Sw34 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw01 ∷ [])
  b10 = at 5 2 [] (wl0006 c4) ▸
       at 6 2 (CS14 ∷ Sw23 ∷ []) (sym (wl0021 c4)) ▸
       at 7 2 (K2 ∷ Sw23 ∷ []) (sym (wl0058 c4)) ▸
       at 8 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 2 2 (K2 ∷ Sw34 ∷ []) (sym (c₃ (K ↑ ↑) (Swap))) ▸
       at 4 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0007 c4) ▸ done

  b11 : Chain (Sw23 ∷ Sw34 ∷ K2 ∷ CS23 ∷ Sw34 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw01 ∷ []) (Sw23 ∷ Sw34 ∷ K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι ∷ Sw34 ∷ Sw23 ∷ Sw01 ∷ [])
  b11 = at 4 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 6 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0007 c4) ▸
       at 6 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 8 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0007 c4) ▸
       at 8 2 (K2 ∷ Sw34 ∷ []) (sym (c₃ (K ↑ ↑) (Swap))) ▸
       at 9 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸ done

  b12 : Chain (Sw23 ∷ Sw34 ∷ K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι ∷ Sw34 ∷ Sw23 ∷ Sw01 ∷ []) (Toff314 ∷ Sw01 ∷ [])
  b12 = at 2 8 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) (wl0059 c4) ▸
       at 2 8 (Toff213 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff214 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Toff314 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 1 BOX(1;043): 8 steps
lem-nat-1-BOX⟨1·043⟩ : WsL → ⟪ (Sw12 ∷ Bx1-043 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-043 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·043⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx1-043 ∷ []) (Bx2-043 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff104 ∷ Bx0-13 ∷ Toff104 ∷ CCZ014 ∷ Bx0-13 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 1 2 (Toff204 ∷ Sw12 ∷ []) (lem-nat-1-TOFF104 c4) ▸
       at 2 2 (Bx0-23 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·13⟩ c4) ▸
       at 3 2 (Toff204 ∷ Sw12 ∷ []) (lem-nat-1-TOFF104 c4) ▸
       at 4 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 5 2 (Bx0-23 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·13⟩ c4) ▸
       at 0 6 (Bx2-043 ∷ []) (refl) ▸ done


-- nat 1 BOX(0;1243): 8 steps
lem-nat-1-BOX⟨0·1243⟩ : WsL → ⟪ (Sw12 ∷ Bx0-1243 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2143 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·1243⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-1243 ∷ []) (Bx0-2143 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff012 ∷ Bx1-043 ∷ Toff012 ∷ CCZ012 ∷ Bx1-043 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw12 ∷ []) (sym (wl0037 c4)) ▸
       at 1 2 (Toff012 ∷ Sw12 ∷ []) (wl0038 c4) ▸
       at 2 2 (Bx2-043 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·043⟩ c4) ▸
       at 3 2 (Toff012 ∷ Sw12 ∷ []) (wl0038 c4) ▸
       at 4 2 (CCZ012 ∷ Sw12 ∷ []) (sym (wl0037 c4)) ▸
       at 5 2 (Bx2-043 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·043⟩ c4) ▸
       at 0 6 (Bx0-2143 ∷ []) (refl) ▸ done


-- nat 2 BOX(2;043): 8 steps
lem-nat-2-BOX⟨2·043⟩ : WsL → ⟪ (Sw23 ∷ Bx2-043 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-042 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·043⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx2-043 ∷ []) (Bx3-042 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff204 ∷ Bx0-23 ∷ Toff204 ∷ CCZ024 ∷ Bx0-23 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 1 2 (Toff304 ∷ Sw23 ∷ []) (lem-nat-2-TOFF204 c4) ▸
       at 2 2 (Bx0-32 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·23⟩ c4) ▸
       at 3 2 (Toff304 ∷ Sw23 ∷ []) (lem-nat-2-TOFF204 c4) ▸
       at 4 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 5 2 (Bx0-32 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·23⟩ c4) ▸
       at 0 6 (Bx3-042 ∷ []) (refl) ▸ done


-- nat 2 BOX(0;2143): 8 steps
lem-nat-2-BOX⟨0·2143⟩ : WsL → ⟪ (Sw23 ∷ Bx0-2143 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3142 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·2143⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-2143 ∷ []) (Bx0-3142 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff012 ∷ Bx2-043 ∷ Toff012 ∷ CCZ012 ∷ Bx2-043 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 1 2 (Toff013 ∷ Sw23 ∷ []) (lem-nat-2-TOFF012 c4) ▸
       at 2 2 (Bx3-042 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·043⟩ c4) ▸
       at 3 2 (Toff013 ∷ Sw23 ∷ []) (lem-nat-2-TOFF012 c4) ▸
       at 4 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 5 2 (Bx3-042 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·043⟩ c4) ▸
       at 0 6 (Bx0-3142 ∷ []) (refl) ▸ done


-- nat 3 TOFF304: 144 steps
lem-nat-3-TOFF304 : WsL → ⟪ (Sw34 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-TOFF304 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (run b17)))))))))))))))))
  where
  b0 : Chain (Sw34 ∷ Toff304 ∷ []) (Sw34 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Toff204 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw12 ∷ Toff104 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw34 ∷ Toff103 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 5 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b1 = at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 7 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 9 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 11 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸ done

  b2 : Chain (Sw34 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ Sw12 ∷ K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b2 = at 12 2 [] (wl0006 c4) ▸
       at 3 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 6 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 4 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 6 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸ done

  b3 : Chain (Sw34 ∷ Sw23 ∷ Sw12 ∷ K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ K2 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw23 ∷ [])
  b3 = at 10 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 8 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 10 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 11 2 [] (wl0007 c4) ▸
       at 2 2 (K2 ∷ Sw12 ∷ []) (sym (wl0056 c4)) ▸
       at 3 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0008 c4)) ▸
       at 6 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸ done

  b4 : Chain (Sw34 ∷ Sw23 ∷ K2 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ K2 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw23 ∷ [])
  b4 = at 4 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS24⁻ ∷ Sw12 ∷ []) (sym (wl0009 c4)) ▸
       at 8 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 6 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 8 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 c4)) ▸
       at 9 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸ done

  b5 : Chain (Sw34 ∷ Sw23 ∷ K2 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw23 ∷ []) (Sw34 ∷ K3 ∷ CS34 ∷ CX03 ∷ Sw23 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K2 ∷ ι ∷ Sw23 ∷ [])
  b5 = at 7 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K2 ∷ Sw12 ∷ []) (sym (wl0056 c4)) ▸
       at 9 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 10 2 [] (wl0001 c4) ▸
       at 1 2 (K3 ∷ Sw23 ∷ []) (sym (wl0057 c4)) ▸
       at 2 2 (CS34 ∷ Sw23 ∷ []) (sym (wl0011 c4)) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 3 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸ done

  b6 : Chain (Sw34 ∷ K3 ∷ CS34 ∷ CX03 ∷ Sw23 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K2 ∷ ι ∷ Sw23 ∷ []) (Sw34 ∷ K3 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Sw34 ∷ K2 ∷ ι ∷ Sw23 ∷ [])
  b6 = at 4 2 (CS34⁻ ∷ Sw23 ∷ []) (sym (wl0012 c4)) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 5 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (wl0013 c4) ▸
       at 8 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 9 2 (CS01 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸
       at 10 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸ done

  b7 : Chain (Sw34 ∷ K3 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Sw34 ∷ K2 ∷ ι ∷ Sw23 ∷ []) (K4 ∷ CS34 ∷ Sw34 ∷ CX03 ∷ Sw34 ∷ Sw34 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K3 ∷ ι ∷ [])
  b7 = at 11 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (sym (wl0013 c4)) ▸
       at 6 7 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K3 ∷ Sw23 ∷ []) (sym (wl0057 c4)) ▸
       at 8 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 9 2 [] (wl0006 c4) ▸
       at 0 2 (K4 ∷ Sw34 ∷ []) (sym (wl0067 c4)) ▸
       at 1 2 (CS34 ∷ Sw34 ∷ []) (sym (wl0039 c4)) ▸
       at 4 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸ done

  b8 : Chain (K4 ∷ CS34 ∷ Sw34 ∷ CX03 ∷ Sw34 ∷ Sw34 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K3 ∷ ι ∷ []) (K4 ∷ CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ K4 ∷ ι ∷ Sw34 ∷ [])
  b8 = at 2 3 (CX04 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS34⁻ ∷ Sw34 ∷ []) (sym (wl0040 c4)) ▸
       at 6 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 4 3 (CX04 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0007 c4) ▸
       at 6 2 (K4 ∷ Sw34 ∷ []) (sym (wl0067 c4)) ▸
       at 7 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸ done

  b9 : Chain (K4 ∷ CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ K4 ∷ ι ∷ Sw34 ∷ []) (Sw23 ∷ K4 ∷ CS24 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Sw34 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ K4 ∷ ι ∷ Sw34 ∷ [])
  b9 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 1 2 (K4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K)) ▸
       at 2 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0015 c4)) ▸
       at 4 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (wl0013 c4) ▸
       at 5 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 6 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 7 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸ done

  b10 : Chain (Sw23 ∷ K4 ∷ CS24 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Sw34 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ K4 ∷ ι ∷ Sw34 ∷ []) (Sw23 ∷ K4 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Sw34 ∷ CS03 ∷ K4 ∷ ι ∷ Sw34 ∷ [])
  b10 = at 8 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (sym (wl0013 c4)) ▸
       at 3 7 (CX04 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS24⁻ ∷ Sw23 ∷ []) (sym (wl0016 c4)) ▸
       at 6 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (wl0013 c4) ▸
       at 7 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 8 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 9 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸ done

  b11 : Chain (Sw23 ∷ K4 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Sw34 ∷ CS03 ∷ K4 ∷ ι ∷ Sw34 ∷ []) (Sw23 ∷ Sw12 ∷ K4 ∷ Sw12 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ K4 ∷ ι ∷ Sw23 ∷ Sw34 ∷ [])
  b11 = at 10 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (sym (wl0013 c4)) ▸
       at 5 7 (CX04 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0006 c4) ▸
       at 7 2 (K4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K)) ▸
       at 8 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 2 2 (K4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K ↑)) ▸ done

  b12 : Chain (Sw23 ∷ Sw12 ∷ K4 ∷ Sw12 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ K4 ∷ ι ∷ Sw23 ∷ Sw34 ∷ []) (Sw23 ∷ Sw12 ∷ K4 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ Sw12 ∷ Sw34 ∷ CX03 ∷ Sw34 ∷ CS02 ∷ K4 ∷ ι ∷ Sw23 ∷ Sw34 ∷ [])
  b12 = at 3 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0017 c4)) ▸
       at 5 1 (Sw34 ∷ CX03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 5 2 (CX03 ∷ Sw12 ∷ []) (sym (wl0014 c4)) ▸
       at 6 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 4 3 (CX04 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS14⁻ ∷ Sw12 ∷ []) (sym (wl0018 c4)) ▸
       at 7 1 (Sw34 ∷ CX03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b13 : Chain (Sw23 ∷ Sw12 ∷ K4 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ Sw12 ∷ Sw34 ∷ CX03 ∷ Sw34 ∷ CS02 ∷ K4 ∷ ι ∷ Sw23 ∷ Sw34 ∷ []) (Sw23 ∷ Sw12 ∷ K4 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ K4 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ [])
  b13 = at 6 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 7 2 (CX03 ∷ Sw12 ∷ []) (sym (wl0014 c4)) ▸
       at 8 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 6 3 (CX04 ∷ []) (by-assoc Eq.refl) ▸
       at 8 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0001 c4) ▸
       at 8 2 (K4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K ↑)) ▸
       at 9 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸ done

  b14 : Chain (Sw23 ∷ Sw12 ∷ K4 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ K4 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ K3 ∷ CS13 ∷ CX03 ∷ CS13⁻ ∷ Sw34 ∷ CX04 ∷ CS01 ∷ K4 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ [])
  b14 = at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 3 2 (K3 ∷ Sw34 ∷ []) (sym (wl0068 c4)) ▸
       at 5 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0007 c4) ▸
       at 6 1 (Sw34 ∷ CX03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0007 c4) ▸
       at 7 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0007 c4) ▸ done

  b15 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ K3 ∷ CS13 ∷ CX03 ∷ CS13⁻ ∷ Sw34 ∷ CX04 ∷ CS01 ∷ K4 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K2 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ [])
  b15 = at 8 1 (Sw34 ∷ CX03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0007 c4) ▸
       at 8 2 (CS01 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸
       at 9 2 (K3 ∷ Sw34 ∷ []) (sym (wl0068 c4)) ▸
       at 10 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 4 2 (K2 ∷ Sw23 ∷ []) (sym (wl0058 c4)) ▸
       at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b16 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K2 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K2 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ Sw23 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ [])
  b16 = at 5 2 [] (wl0006 c4) ▸
       at 7 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0006 c4) ▸
       at 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0006 c4) ▸
       at 9 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0006 c4) ▸
       at 9 2 (CS01 ∷ Sw23 ∷ []) (sym (c₂ (CS) (Swap))) ▸ done

  b17 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K2 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ Sw23 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (Toff403 ∷ Sw34 ∷ [])
  b17 = at 10 2 (K2 ∷ Sw23 ∷ []) (sym (wl0058 c4)) ▸
       at 11 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 4 8 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (sym (wl0083 c4)) ▸
       at 4 8 (Toff201 ∷ []) (by-assoc Eq.refl) ▸
       at 3 3 (Toff301 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (Toff401 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff402 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Toff403 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 3 CZ23: 2 steps
lem-nat-3-CZ23 : WsL → ⟪ (Sw34 ∷ CZ23 ∷ []) ⟫ʷ ≈ ⟪ (CZ24 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-CZ23 c4 = run b0
  where
  b0 : Chain (Sw34 ∷ CZ23 ∷ []) (CZ24 ∷ Sw34 ∷ [])
  b0 = at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 0 3 (CZ24 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 3 BOX(0;32): 3 steps
lem-nat-3-BOX⟨0·32⟩ : WsL → ⟪ (Sw34 ∷ Bx0-32 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-42 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·32⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx0-32 ∷ []) (Bx0-42 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CZ23 ∷ []) (refl) ▸
       at 0 2 (CZ24 ∷ Sw34 ∷ []) (lem-nat-3-CZ23 c4) ▸
       at 0 1 (Bx0-42 ∷ []) (refl) ▸ done


-- nat 3 BOX(3;042): 8 steps
lem-nat-3-BOX⟨3·042⟩ : WsL → ⟪ (Sw34 ∷ Bx3-042 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-032 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨3·042⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx3-042 ∷ []) (Bx4-032 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff304 ∷ Bx0-32 ∷ Toff304 ∷ CCZ034 ∷ Bx0-32 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw34 ∷ []) (lem-nat-3-CCZ034 c4) ▸
       at 1 2 (Toff403 ∷ Sw34 ∷ []) (lem-nat-3-TOFF304 c4) ▸
       at 2 2 (Bx0-42 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·32⟩ c4) ▸
       at 3 2 (Toff403 ∷ Sw34 ∷ []) (lem-nat-3-TOFF304 c4) ▸
       at 4 2 (CCZ034 ∷ Sw34 ∷ []) (lem-nat-3-CCZ034 c4) ▸
       at 5 2 (Bx0-42 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·32⟩ c4) ▸
       at 0 6 (Bx4-032 ∷ []) (refl) ▸ done


-- nat 3 BOX(0;3142): 8 steps
lem-nat-3-BOX⟨0·3142⟩ : WsL → ⟪ (Sw34 ∷ Bx0-3142 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4132 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·3142⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx0-3142 ∷ []) (Bx0-4132 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff013 ∷ Bx3-042 ∷ Toff013 ∷ CCZ013 ∷ Bx3-042 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4) ▸
       at 1 2 (Toff014 ∷ Sw34 ∷ []) (lem-nat-3-TOFF013 c4) ▸
       at 2 2 (Bx4-032 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·042⟩ c4) ▸
       at 3 2 (Toff014 ∷ Sw34 ∷ []) (lem-nat-3-TOFF013 c4) ▸
       at 4 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4) ▸
       at 5 2 (Bx4-032 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·042⟩ c4) ▸
       at 0 6 (Bx0-4132 ∷ []) (refl) ▸ done


-- nat 0 BOX(0;42): 2 steps
lem-nat-0-BOX⟨0·42⟩ : WsL → ⟪ (Sw01 ∷ Bx0-42 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-42 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·42⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-42 ∷ []) (Bx1-42 ∷ Sw01 ∷ [])
  b0 = at 0 2 (Bx0-42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CZ • Swap ↑)) ▸
       at 0 1 (Bx1-42 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 BOX(4;032): 8 steps
lem-nat-0-BOX⟨4·032⟩ : WsL → ⟪ (Sw01 ∷ Bx4-032 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-132 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·032⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx4-032 ∷ []) (Bx4-132 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff403 ∷ Bx0-42 ∷ Toff403 ∷ CCZ034 ∷ Bx0-42 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4) ▸
       at 1 2 (Toff413 ∷ Sw01 ∷ []) (lem-nat-0-TOFF403 c4) ▸
       at 2 2 (Bx1-42 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·42⟩ c4) ▸
       at 3 2 (Toff413 ∷ Sw01 ∷ []) (lem-nat-0-TOFF403 c4) ▸
       at 4 2 (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4) ▸
       at 5 2 (Bx1-42 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·42⟩ c4) ▸
       at 0 6 (Bx4-132 ∷ []) (refl) ▸ done

