{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.R007 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (WsL ; wl0001 ; wl0002 ; wl0006 ; wl0007 ; wl0008 ; wl0009 ; wl0010 ; wl0011 ; wl0012 ; wl0013 ; wl0015 ; wl0016 ; wl0017 ; wl0018 ; wl0019 ; wl0020 ; wl0021 ; wl0022 ; wl0023 ; wl0027 ; wl0028 ; wl0030 ; wl0031 ; wl0032 ; wl0033 ; wl0034 ; wl0035 ; wl0036 ; wl0048 ; wl0061 ; wl0063 ; wl0064 ; wl0065 ; wl0073 ; wl0074 ; wl0078 ; wl0087 ; wl0088 ; wl0089 ; wl0091 ; wl0092 ; wl0093 ; wl0095 ; wl0096 ; wl0097 ; wl0099 ; wl0100 ; wl0101 ; wl0103 ; wl0104 ; wl0105 ; wl0111 ; wl0112 ; wl0119 ; wl0120 ; wl0121 ; wl0122 ; wl0123 ; wl0124 ; wl0125 ; wl0126 ; wl0127 ; wl0128 ; wl0129 ; wl0130 ; wl0131 ; wl0132 ; wl0133 ; wl0134 ; wl0135 ; wl0136)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-nat-1-CCZ024 ; lem-nat-1-CCZ034 ; lem-nat-2-BOX⟨0·1234⟩ ; lem-nat-2-BOX⟨0·1324⟩ ; lem-nat-2-CCZ013 ; lem-nat-2-CCZ024 ; lem-nat-2-CCZ034 ; lem-nat-2-TOFF013 ; lem-nat-2-TOFF103 ; lem-nat-3-BOX⟨0·1423⟩ ; lem-nat-3-CCZ014 ; lem-nat-3-CCZ024 ; lem-nat-3-TOFF014)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-0-CCZ024 ; lem-nat-0-CCZ124 ; lem-nat-1-CCZ013 ; lem-nat-2-TOFF304 ; lem-nat-3-BOX⟨0·1324⟩ ; lem-nat-3-CCZ013 ; lem-nat-3-CCZ023 ; lem-nat-3-TOFF204)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-0-CCZ014 ; lem-nat-0-CCZ134 ; lem-nat-0-TOFF104 ; lem-nat-0-TOFF412 ; lem-nat-1-TOFF204)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-0-CZ04 ; lem-nat-0-TOFF204 ; lem-nat-0-TOFF214 ; lem-nat-0-TOFF413 ; lem-nat-1-TOFF013 ; lem-nat-1-TOFF304 ; lem-nat-2-TOFF104 ; lem-nat-3-TOFF023)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-0-BOX⟨0·1423⟩ ; lem-nat-0-BOX⟨1·0423⟩ ; lem-nat-0-TOFF024 ; lem-nat-1-BOX⟨1·0423⟩ ; lem-nat-1-BOX⟨2·0413⟩ ; lem-nat-2-CCZ014 ; lem-nat-2-CZ02 ; lem-nat-2-TOFF402 ; lem-nat-3-TOFF103)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-1-BOX⟨0·2341⟩ ; lem-nat-1-CS02 ; lem-nat-1-CZ01 ; lem-nat-1-CZ02 ; lem-nat-2-BOX⟨0·12⟩ ; lem-nat-3-CS13 ; lem-nat-3-CS14 ; lem-nat-3-CSd13 ; lem-nat-3-CSd14)
-- nat 2 TOFF014: 68 steps
lem-nat-2-TOFF014 : WsL → ⟪ (Sw23 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-TOFF014 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (run b8))))))))
  where
  b0 : Chain (Sw23 ∷ Toff014 ∷ []) (Sw23 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Toff013 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 3 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸ done

  b1 : Chain (Sw23 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ []) (Sw23 ∷ K0 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ [])
  b1 = at 5 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 7 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 10 2 [] (wl0006 c4) ▸
       at 1 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸ done

  b2 : Chain (Sw23 ∷ K0 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ []) (Sw23 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw34 ∷ K0 ∷ ι ∷ Sw34 ∷ [])
  b2 = at 4 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 2 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 6 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 4 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 6 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸ done

  b3 : Chain (Sw23 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw34 ∷ K0 ∷ ι ∷ Sw34 ∷ []) (K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw23 ∷ CS04 ∷ K0 ∷ ι ∷ [])
  b3 = at 7 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 8 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 9 2 [] (wl0007 c4) ▸
       at 0 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 1 2 (CS14 ∷ Sw23 ∷ []) (sym (wl0021 c4)) ▸
       at 2 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 3 2 (CS14⁻ ∷ Sw23 ∷ []) (sym (wl0033 c4)) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸ done

  b4 : Chain (K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw23 ∷ CS04 ∷ K0 ∷ ι ∷ []) (K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ Sw23 ∷ ι ∷ [])
  b4 = at 6 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (wl0013 c4) ▸
       at 7 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 8 2 (CS01 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸
       at 9 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 10 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (sym (wl0013 c4)) ▸
       at 5 7 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸ done

  b5 : Chain (K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ Sw23 ∷ ι ∷ []) (Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw34 ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ Sw23 ∷ [])
  b5 = at 7 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 1 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 3 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (wl0007 c4) ▸
       at 3 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 5 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0007 c4) ▸ done

  b6 : Chain (Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw34 ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ K0 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw23 ∷ [])
  b6 = at 5 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 7 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0007 c4) ▸
       at 7 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 8 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 2 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b7 : Chain (Sw34 ∷ Sw23 ∷ K0 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ Sw23 ∷ ι ∷ Sw34 ∷ Sw23 ∷ [])
  b7 = at 3 2 [] (wl0006 c4) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0006 c4) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0006 c4) ▸
       at 8 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸ done

  b8 : Chain (Sw34 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ Sw23 ∷ ι ∷ Sw34 ∷ Sw23 ∷ []) (Toff014 ∷ Sw23 ∷ [])
  b8 = at 9 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 2 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Toff014 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 2 TOFF403: 2 steps
lem-nat-2-TOFF403 : WsL → ⟪ (Sw23 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-TOFF403 c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Toff403 ∷ []) (Toff402 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Toff402 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0006 c4) ▸ done


-- nat 2 BOX(0;42): 3 steps
lem-nat-2-BOX⟨0·42⟩ : WsL → ⟪ (Sw23 ∷ Bx0-42 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-43 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·42⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-42 ∷ []) (Bx0-43 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ24 ∷ []) (refl) ▸
       at 0 2 (CZ34 ∷ Sw23 ∷ []) (sym (wl0028 c4)) ▸
       at 0 1 (Bx0-43 ∷ []) (refl) ▸ done


-- nat 2 BOX(4;032): 8 steps
lem-nat-2-BOX⟨4·032⟩ : WsL → ⟪ (Sw23 ∷ Bx4-032 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-023 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·032⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx4-032 ∷ []) (Bx4-023 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff403 ∷ Bx0-42 ∷ Toff403 ∷ CCZ034 ∷ Bx0-42 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 1 2 (Toff402 ∷ Sw23 ∷ []) (lem-nat-2-TOFF403 c4) ▸
       at 2 2 (Bx0-43 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·42⟩ c4) ▸
       at 3 2 (Toff402 ∷ Sw23 ∷ []) (lem-nat-2-TOFF403 c4) ▸
       at 4 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 5 2 (Bx0-43 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·42⟩ c4) ▸
       at 0 6 (Bx4-023 ∷ []) (refl) ▸ done


-- nat 2 BOX(0;4132): 8 steps
lem-nat-2-BOX⟨0·4132⟩ : WsL → ⟪ (Sw23 ∷ Bx0-4132 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4123 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·4132⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-4132 ∷ []) (Bx0-4123 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff014 ∷ Bx4-032 ∷ Toff014 ∷ CCZ014 ∷ Bx4-032 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 1 2 (Toff014 ∷ Sw23 ∷ []) (lem-nat-2-TOFF014 c4) ▸
       at 2 2 (Bx4-023 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·032⟩ c4) ▸
       at 3 2 (Toff014 ∷ Sw23 ∷ []) (lem-nat-2-TOFF014 c4) ▸
       at 4 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 5 2 (Bx4-023 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·032⟩ c4) ▸
       at 0 6 (Bx0-4123 ∷ []) (refl) ▸ done


-- nat 2 BOX(0;43): 3 steps
lem-nat-2-BOX⟨0·43⟩ : WsL → ⟪ (Sw23 ∷ Bx0-43 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-42 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·43⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-43 ∷ []) (Bx0-42 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ34 ∷ []) (refl) ▸
       at 0 2 (CZ24 ∷ Sw23 ∷ []) (sym (wl0027 c4)) ▸
       at 0 1 (Bx0-42 ∷ []) (refl) ▸ done


-- nat 2 BOX(4;023): 8 steps
lem-nat-2-BOX⟨4·023⟩ : WsL → ⟪ (Sw23 ∷ Bx4-023 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-032 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·023⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx4-023 ∷ []) (Bx4-032 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff402 ∷ Bx0-43 ∷ Toff402 ∷ CCZ024 ∷ Bx0-43 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 1 2 (Toff403 ∷ Sw23 ∷ []) (lem-nat-2-TOFF402 c4) ▸
       at 2 2 (Bx0-42 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·43⟩ c4) ▸
       at 3 2 (Toff403 ∷ Sw23 ∷ []) (lem-nat-2-TOFF402 c4) ▸
       at 4 2 (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4) ▸
       at 5 2 (Bx0-42 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·43⟩ c4) ▸
       at 0 6 (Bx4-032 ∷ []) (refl) ▸ done


-- nat 2 BOX(0;4123): 8 steps
lem-nat-2-BOX⟨0·4123⟩ : WsL → ⟪ (Sw23 ∷ Bx0-4123 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4132 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·4123⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-4123 ∷ []) (Bx0-4132 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff014 ∷ Bx4-023 ∷ Toff014 ∷ CCZ014 ∷ Bx4-023 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 1 2 (Toff014 ∷ Sw23 ∷ []) (lem-nat-2-TOFF014 c4) ▸
       at 2 2 (Bx4-032 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·023⟩ c4) ▸
       at 3 2 (Toff014 ∷ Sw23 ∷ []) (lem-nat-2-TOFF014 c4) ▸
       at 4 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 5 2 (Bx4-032 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·023⟩ c4) ▸
       at 0 6 (Bx0-4132 ∷ []) (refl) ▸ done


-- nat 0 BOX(1;42): 2 steps
lem-nat-0-BOX⟨1·42⟩ : WsL → ⟪ (Sw01 ∷ Bx1-42 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-42 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·42⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-42 ∷ []) (Bx0-42 ∷ Sw01 ∷ [])
  b0 = at 0 2 (Bx1-42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CZ • Swap ↑)) ▸
       at 0 1 (Bx0-42 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 BOX(4;132): 8 steps
lem-nat-0-BOX⟨4·132⟩ : WsL → ⟪ (Sw01 ∷ Bx4-132 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-032 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·132⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx4-132 ∷ []) (Bx4-032 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff413 ∷ Bx1-42 ∷ Toff413 ∷ CCZ134 ∷ Bx1-42 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 1 2 (Toff403 ∷ Sw01 ∷ []) (lem-nat-0-TOFF413 c4) ▸
       at 2 2 (Bx0-42 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·42⟩ c4) ▸
       at 3 2 (Toff403 ∷ Sw01 ∷ []) (lem-nat-0-TOFF413 c4) ▸
       at 4 2 (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4) ▸
       at 5 2 (Bx0-42 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·42⟩ c4) ▸
       at 0 6 (Bx4-032 ∷ []) (refl) ▸ done


-- nat 0 BOX(1;4032): 8 steps
lem-nat-0-BOX⟨1·4032⟩ : WsL → ⟪ (Sw01 ∷ Bx1-4032 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4132 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·4032⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-4032 ∷ []) (Bx0-4132 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff104 ∷ Bx4-132 ∷ Toff104 ∷ CCZ014 ∷ Bx4-132 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 1 2 (Toff014 ∷ Sw01 ∷ []) (lem-nat-0-TOFF104 c4) ▸
       at 2 2 (Bx4-032 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·132⟩ c4) ▸
       at 3 2 (Toff014 ∷ Sw01 ∷ []) (lem-nat-0-TOFF104 c4) ▸
       at 4 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 5 2 (Bx4-032 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·132⟩ c4) ▸
       at 0 6 (Bx0-4132 ∷ []) (refl) ▸ done


-- nat 1 BOX(2;41): 3 steps
lem-nat-1-BOX⟨2·41⟩ : WsL → ⟪ (Sw12 ∷ Bx2-41 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-42 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·41⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx2-41 ∷ []) (Bx1-42 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ14 ∷ []) (refl) ▸
       at 0 2 (CZ24 ∷ Sw12 ∷ []) (sym (wl0089 c4)) ▸
       at 0 1 (Bx1-42 ∷ []) (refl) ▸ done


-- nat 1 BOX(4;231): 8 steps
lem-nat-1-BOX⟨4·231⟩ : WsL → ⟪ (Sw12 ∷ Bx4-231 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-132 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·231⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx4-231 ∷ []) (Bx4-132 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff423 ∷ Bx2-41 ∷ Toff423 ∷ CCZ234 ∷ Bx2-41 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0034 c4)) ▸
       at 1 2 (Toff413 ∷ Sw12 ∷ []) (wl0091 c4) ▸
       at 2 2 (Bx1-42 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·41⟩ c4) ▸
       at 3 2 (Toff413 ∷ Sw12 ∷ []) (wl0091 c4) ▸
       at 4 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0034 c4)) ▸
       at 5 2 (Bx1-42 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·41⟩ c4) ▸
       at 0 6 (Bx4-132 ∷ []) (refl) ▸ done


-- nat 1 BOX(2;4031): 8 steps
lem-nat-1-BOX⟨2·4031⟩ : WsL → ⟪ (Sw12 ∷ Bx2-4031 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-4032 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·4031⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx2-4031 ∷ []) (Bx1-4032 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff204 ∷ Bx4-231 ∷ Toff204 ∷ CCZ024 ∷ Bx4-231 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 1 2 (Toff104 ∷ Sw12 ∷ []) (lem-nat-1-TOFF204 c4) ▸
       at 2 2 (Bx4-132 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·231⟩ c4) ▸
       at 3 2 (Toff104 ∷ Sw12 ∷ []) (lem-nat-1-TOFF204 c4) ▸
       at 4 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 5 2 (Bx4-132 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·231⟩ c4) ▸
       at 0 6 (Bx1-4032 ∷ []) (refl) ▸ done


-- nat 0 BOX(2;40): 3 steps
lem-nat-0-BOX⟨2·40⟩ : WsL → ⟪ (Sw01 ∷ Bx2-40 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-41 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·40⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx2-40 ∷ []) (Bx2-41 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CZ04 ∷ []) (refl) ▸
       at 0 2 (CZ14 ∷ Sw01 ∷ []) (lem-nat-0-CZ04 c4) ▸
       at 0 1 (Bx2-41 ∷ []) (refl) ▸ done


-- nat 0 BOX(4;230): 8 steps
lem-nat-0-BOX⟨4·230⟩ : WsL → ⟪ (Sw01 ∷ Bx4-230 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-231 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·230⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx4-230 ∷ []) (Bx4-231 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff423 ∷ Bx2-40 ∷ Toff423 ∷ CCZ234 ∷ Bx2-40 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 1 2 (Toff423 ∷ Sw01 ∷ []) (c₂ (Swap) (Toffᵗ)) ▸
       at 2 2 (Bx2-41 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·40⟩ c4) ▸
       at 3 2 (Toff423 ∷ Sw01 ∷ []) (c₂ (Swap) (Toffᵗ)) ▸
       at 4 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 5 2 (Bx2-41 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·40⟩ c4) ▸
       at 0 6 (Bx4-231 ∷ []) (refl) ▸ done


-- nat 0 BOX(2;4130): 8 steps
lem-nat-0-BOX⟨2·4130⟩ : WsL → ⟪ (Sw01 ∷ Bx2-4130 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4031 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·4130⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx2-4130 ∷ []) (Bx2-4031 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff214 ∷ Bx4-230 ∷ Toff214 ∷ CCZ124 ∷ Bx4-230 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 1 2 (Toff204 ∷ Sw01 ∷ []) (lem-nat-0-TOFF214 c4) ▸
       at 2 2 (Bx4-231 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·230⟩ c4) ▸
       at 3 2 (Toff204 ∷ Sw01 ∷ []) (lem-nat-0-TOFF214 c4) ▸
       at 4 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 5 2 (Bx4-231 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·230⟩ c4) ▸
       at 0 6 (Bx2-4031 ∷ []) (refl) ▸ done


-- nat 0 BOX(4;213): 8 steps
lem-nat-0-BOX⟨4·213⟩ : WsL → ⟪ (Sw01 ∷ Bx4-213 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-203 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·213⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx4-213 ∷ []) (Bx4-203 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff412 ∷ Bx2-43 ∷ Toff412 ∷ CCZ124 ∷ Bx2-43 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 1 2 (Toff402 ∷ Sw01 ∷ []) (lem-nat-0-TOFF412 c4) ▸
       at 2 2 (Bx2-43 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑)) ▸
       at 3 2 (Toff402 ∷ Sw01 ∷ []) (lem-nat-0-TOFF412 c4) ▸
       at 4 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 5 2 (Bx2-43 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑)) ▸
       at 0 6 (Bx4-203 ∷ []) (refl) ▸ done


-- nat 0 BOX(2;4013): 8 steps
lem-nat-0-BOX⟨2·4013⟩ : WsL → ⟪ (Sw01 ∷ Bx2-4013 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4103 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·4013⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx2-4013 ∷ []) (Bx2-4103 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff204 ∷ Bx4-213 ∷ Toff204 ∷ CCZ024 ∷ Bx4-213 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 1 2 (Toff214 ∷ Sw01 ∷ []) (lem-nat-0-TOFF204 c4) ▸
       at 2 2 (Bx4-203 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·213⟩ c4) ▸
       at 3 2 (Toff214 ∷ Sw01 ∷ []) (lem-nat-0-TOFF204 c4) ▸
       at 4 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 5 2 (Bx4-203 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·213⟩ c4) ▸
       at 0 6 (Bx2-4103 ∷ []) (refl) ▸ done


-- nat 2 SBOX(0;1;4;2): 3 steps
lem-nat-2-SBOX⟨0·1·4·2⟩ : WsL → ⟪ (Sw23 ∷ Sb0-1-4-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-4-3 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨0·1·4·2⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb0-1-4-2 ∷ []) (Sb0-1-4-3 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS14 ∷ []) (refl) ▸
       at 0 2 (CS14 ∷ Sw23 ∷ []) (sym (wl0021 c4)) ▸
       at 0 1 (Sb0-1-4-3 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(0;1;4;2): 3 steps
lem-nat-2-SBOXd⟨0·1·4·2⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻0-1-4-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-4-3 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨0·1·4·2⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻0-1-4-2 ∷ []) (Sb⁻0-1-4-3 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS14⁻ ∷ []) (refl) ▸
       at 0 2 (CS14⁻ ∷ Sw23 ∷ []) (sym (wl0033 c4)) ▸
       at 0 1 (Sb⁻0-1-4-3 ∷ []) (refl) ▸ done


-- nat 2 SBOX(0;1;32;4): 7 steps
lem-nat-2-SBOX⟨0·1·32·4⟩ : WsL → ⟪ (Sw23 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-23-4 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨0·1·32·4⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb0-1-32-4 ∷ []) (Sb0-1-23-4 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ []) (refl) ▸
       at 0 2 (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ c4) ▸
       at 1 2 (Toff423 ∷ Sw23 ∷ []) (wl0087 c4) ▸
       at 2 2 (Sb0-1-4-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·4·2⟩ c4) ▸
       at 3 2 (Toff423 ∷ Sw23 ∷ []) (wl0087 c4) ▸
       at 4 2 (Sb⁻0-1-4-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·4·2⟩ c4) ▸
       at 0 5 (Sb0-1-23-4 ∷ []) (refl) ▸ done


-- nat 2 SBOX(0;1;4;3): 3 steps
lem-nat-2-SBOX⟨0·1·4·3⟩ : WsL → ⟪ (Sw23 ∷ Sb0-1-4-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-4-2 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨0·1·4·3⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb0-1-4-3 ∷ []) (Sb0-1-4-2 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS14 ∷ []) (refl) ▸
       at 0 2 (CS14 ∷ Sw23 ∷ []) (sym (wl0021 c4)) ▸
       at 0 1 (Sb0-1-4-2 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(0;1;4;3): 3 steps
lem-nat-2-SBOXd⟨0·1·4·3⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻0-1-4-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-4-2 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨0·1·4·3⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻0-1-4-3 ∷ []) (Sb⁻0-1-4-2 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS14⁻ ∷ []) (refl) ▸
       at 0 2 (CS14⁻ ∷ Sw23 ∷ []) (sym (wl0033 c4)) ▸
       at 0 1 (Sb⁻0-1-4-2 ∷ []) (refl) ▸ done


-- nat 2 SBOX(0;1;23;4): 7 steps
lem-nat-2-SBOX⟨0·1·23·4⟩ : WsL → ⟪ (Sw23 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-32-4 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨0·1·23·4⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb0-1-23-4 ∷ []) (Sb0-1-32-4 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) (refl) ▸
       at 0 2 (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ c4) ▸
       at 1 2 (Toff423 ∷ Sw23 ∷ []) (wl0087 c4) ▸
       at 2 2 (Sb0-1-4-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·4·3⟩ c4) ▸
       at 3 2 (Toff423 ∷ Sw23 ∷ []) (wl0087 c4) ▸
       at 4 2 (Sb⁻0-1-4-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·4·3⟩ c4) ▸
       at 0 5 (Sb0-1-32-4 ∷ []) (refl) ▸ done


-- nat 3 SBOX(0;1;3;2): 3 steps
lem-nat-3-SBOX⟨0·1·3·2⟩ : WsL → ⟪ (Sw34 ∷ Sb0-1-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-4-2 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨0·1·3·2⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb0-1-3-2 ∷ []) (Sb0-1-4-2 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS13 ∷ []) (refl) ▸
       at 0 2 (CS14 ∷ Sw34 ∷ []) (lem-nat-3-CS13 c4) ▸
       at 0 1 (Sb0-1-4-2 ∷ []) (refl) ▸ done


-- nat 3 SBOXd(0;1;3;2): 3 steps
lem-nat-3-SBOXd⟨0·1·3·2⟩ : WsL → ⟪ (Sw34 ∷ Sb⁻0-1-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-4-2 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨0·1·3·2⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb⁻0-1-3-2 ∷ []) (Sb⁻0-1-4-2 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS13⁻ ∷ []) (refl) ▸
       at 0 2 (CS14⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd13 c4) ▸
       at 0 1 (Sb⁻0-1-4-2 ∷ []) (refl) ▸ done


-- nat 3 SBOX(0;1;42;3): 7 steps
lem-nat-3-SBOX⟨0·1·42·3⟩ : WsL → ⟪ (Sw34 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-32-4 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨0·1·42·3⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-32-4 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 0 2 (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ c4) ▸
       at 1 2 (Toff423 ∷ Sw34 ∷ []) (wl0119 c4) ▸
       at 2 2 (Sb0-1-4-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·3·2⟩ c4) ▸
       at 3 2 (Toff423 ∷ Sw34 ∷ []) (wl0119 c4) ▸
       at 4 2 (Sb⁻0-1-4-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·3·2⟩ c4) ▸
       at 0 5 (Sb0-1-32-4 ∷ []) (refl) ▸ done


-- nat 3 SBOX(0;1;4;2): 3 steps
lem-nat-3-SBOX⟨0·1·4·2⟩ : WsL → ⟪ (Sw34 ∷ Sb0-1-4-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-3-2 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨0·1·4·2⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb0-1-4-2 ∷ []) (Sb0-1-3-2 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS14 ∷ []) (refl) ▸
       at 0 2 (CS13 ∷ Sw34 ∷ []) (lem-nat-3-CS14 c4) ▸
       at 0 1 (Sb0-1-3-2 ∷ []) (refl) ▸ done


-- nat 3 SBOXd(0;1;4;2): 3 steps
lem-nat-3-SBOXd⟨0·1·4·2⟩ : WsL → ⟪ (Sw34 ∷ Sb⁻0-1-4-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-3-2 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨0·1·4·2⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb⁻0-1-4-2 ∷ []) (Sb⁻0-1-3-2 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS14⁻ ∷ []) (refl) ▸
       at 0 2 (CS13⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd14 c4) ▸
       at 0 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸ done


-- nat 3 SBOX(0;1;32;4): 7 steps
lem-nat-3-SBOX⟨0·1·32·4⟩ : WsL → ⟪ (Sw34 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨0·1·32·4⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb0-1-32-4 ∷ []) (Sb0-1-42-3 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ []) (refl) ▸
       at 0 2 (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ c4) ▸
       at 1 2 (Toff324 ∷ Sw34 ∷ []) (wl0120 c4) ▸
       at 2 2 (Sb0-1-3-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·4·2⟩ c4) ▸
       at 3 2 (Toff324 ∷ Sw34 ∷ []) (wl0120 c4) ▸
       at 4 2 (Sb⁻0-1-3-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·4·2⟩ c4) ▸
       at 0 5 (Sb0-1-42-3 ∷ []) (refl) ▸ done


-- nat 0 SBOX(1;0;3;2): 3 steps
lem-nat-0-SBOX⟨1·0·3·2⟩ : WsL → ⟪ (Sw01 ∷ Sb1-0-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-3-2 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨1·0·3·2⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb1-0-3-2 ∷ []) (Sb0-1-3-2 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS03 ∷ []) (refl) ▸
       at 0 2 (CS13 ∷ Sw01 ∷ []) (sym (wl0061 c4)) ▸
       at 0 1 (Sb0-1-3-2 ∷ []) (refl) ▸ done


-- nat 0 SBOXd(1;0;3;2): 3 steps
lem-nat-0-SBOXd⟨1·0·3·2⟩ : WsL → ⟪ (Sw01 ∷ Sb⁻1-0-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-3-2 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨1·0·3·2⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻1-0-3-2 ∷ []) (Sb⁻0-1-3-2 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS03⁻ ∷ []) (refl) ▸
       at 0 2 (CS13⁻ ∷ Sw01 ∷ []) (sym (wl0121 c4)) ▸
       at 0 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸ done


-- nat 0 SBOX(1;0;42;3): 7 steps
lem-nat-0-SBOX⟨1·0·42·3⟩ : WsL → ⟪ (Sw01 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨1·0·42·3⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb1-0-42-3 ∷ []) (Sb0-1-42-3 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (refl) ▸
       at 0 2 (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ c4) ▸
       at 1 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 2 2 (Sb0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·3·2⟩ c4) ▸
       at 3 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 4 2 (Sb⁻0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·3·2⟩ c4) ▸
       at 0 5 (Sb0-1-42-3 ∷ []) (refl) ▸ done


-- nat 0 CS04: 5 steps
lem-nat-0-CS04 : WsL → ⟪ (Sw01 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-CS04 c4 = run b0
  where
  b0 : Chain (Sw01 ∷ CS04 ∷ []) (CS14 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 1 2 (CS13 ∷ Sw01 ∷ []) (sym (wl0061 c4)) ▸
       at 2 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 0 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 CS14: 5 steps
lem-nat-0-CS14 : WsL → ⟪ (Sw01 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-CS14 c4 = run b0
  where
  b0 : Chain (Sw01 ∷ CS14 ∷ []) (CS04 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 1 2 (CS03 ∷ Sw01 ∷ []) (sym (wl0019 c4)) ▸
       at 2 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 0 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 SBOX(0;1;3;2): 3 steps
lem-nat-0-SBOX⟨0·1·3·2⟩ : WsL → ⟪ (Sw01 ∷ Sb0-1-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-3-2 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨0·1·3·2⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb0-1-3-2 ∷ []) (Sb1-0-3-2 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS13 ∷ []) (refl) ▸
       at 0 2 (CS03 ∷ Sw01 ∷ []) (sym (wl0019 c4)) ▸
       at 0 1 (Sb1-0-3-2 ∷ []) (refl) ▸ done


-- nat 0 SBOXd(0;1;3;2): 3 steps
lem-nat-0-SBOXd⟨0·1·3·2⟩ : WsL → ⟪ (Sw01 ∷ Sb⁻0-1-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-3-2 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨0·1·3·2⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻0-1-3-2 ∷ []) (Sb⁻1-0-3-2 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS13⁻ ∷ []) (refl) ▸
       at 0 2 (CS03⁻ ∷ Sw01 ∷ []) (sym (wl0022 c4)) ▸
       at 0 1 (Sb⁻1-0-3-2 ∷ []) (refl) ▸ done


-- nat 0 SBOX(0;1;42;3): 7 steps
lem-nat-0-SBOX⟨0·1·42·3⟩ : WsL → ⟪ (Sw01 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-42-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨0·1·42·3⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb0-1-42-3 ∷ []) (Sb1-0-42-3 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 0 2 (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ c4) ▸
       at 1 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 2 2 (Sb1-0-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·3·2⟩ c4) ▸
       at 3 2 (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 4 2 (Sb⁻1-0-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨0·1·3·2⟩ c4) ▸
       at 0 5 (Sb1-0-42-3 ∷ []) (refl) ▸ done


-- nat 1 SBOX(2;0;3;1): 3 steps
lem-nat-1-SBOX⟨2·0·3·1⟩ : WsL → ⟪ (Sw12 ∷ Sb2-0-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-3-2 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨2·0·3·1⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb2-0-3-1 ∷ []) (Sb1-0-3-2 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS03 ∷ []) (refl) ▸
       at 0 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 c4)) ▸
       at 0 1 (Sb1-0-3-2 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(2;0;3;1): 3 steps
lem-nat-1-SBOXd⟨2·0·3·1⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻2-0-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-3-2 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨2·0·3·1⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻2-0-3-1 ∷ []) (Sb⁻1-0-3-2 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS03⁻ ∷ []) (refl) ▸
       at 0 2 (CS03⁻ ∷ Sw12 ∷ []) (sym (wl0023 c4)) ▸
       at 0 1 (Sb⁻1-0-3-2 ∷ []) (refl) ▸ done


-- nat 1 SBOX(2;0;41;3): 7 steps
lem-nat-1-SBOX⟨2·0·41·3⟩ : WsL → ⟪ (Sw12 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-42-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨2·0·41·3⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb2-0-41-3 ∷ []) (Sb1-0-42-3 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 0 2 (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ c4) ▸
       at 1 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 c4) ▸
       at 2 2 (Sb1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·3·1⟩ c4) ▸
       at 3 2 (Toff324 ∷ Sw12 ∷ []) (wl0064 c4) ▸
       at 4 2 (Sb⁻1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·3·1⟩ c4) ▸
       at 0 5 (Sb1-0-42-3 ∷ []) (refl) ▸ done


-- nat 1 CS04: 5 steps
lem-nat-1-CS04 : WsL → ⟪ (Sw12 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-CS04 c4 = run b0
  where
  b0 : Chain (Sw12 ∷ CS04 ∷ []) (CS04 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 1 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 c4)) ▸
       at 2 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 0 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 1 SBOX(1;0;3;2): 3 steps
lem-nat-1-SBOX⟨1·0·3·2⟩ : WsL → ⟪ (Sw12 ∷ Sb1-0-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-3-1 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨1·0·3·2⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb1-0-3-2 ∷ []) (Sb2-0-3-1 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS03 ∷ []) (refl) ▸
       at 0 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 c4)) ▸
       at 0 1 (Sb2-0-3-1 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(1;0;3;2): 3 steps
lem-nat-1-SBOXd⟨1·0·3·2⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻1-0-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-0-3-1 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨1·0·3·2⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻1-0-3-2 ∷ []) (Sb⁻2-0-3-1 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS03⁻ ∷ []) (refl) ▸
       at 0 2 (CS03⁻ ∷ Sw12 ∷ []) (sym (wl0023 c4)) ▸
       at 0 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸ done


-- nat 1 SBOX(1;0;42;3): 7 steps
lem-nat-1-SBOX⟨1·0·42·3⟩ : WsL → ⟪ (Sw12 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨1·0·42·3⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb1-0-42-3 ∷ []) (Sb2-0-41-3 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) (refl) ▸
       at 0 2 (Bx2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0423⟩ c4) ▸
       at 1 2 (Toff314 ∷ Sw12 ∷ []) (wl0063 c4) ▸
       at 2 2 (Sb2-0-3-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·3·2⟩ c4) ▸
       at 3 2 (Toff314 ∷ Sw12 ∷ []) (wl0063 c4) ▸
       at 4 2 (Sb⁻2-0-3-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·0·3·2⟩ c4) ▸
       at 0 5 (Sb2-0-41-3 ∷ []) (refl) ▸ done


-- nat 3 CS24: 2 steps
lem-nat-3-CS24 : WsL → ⟪ (Sw34 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-CS24 c4 = run b0
  where
  b0 : Chain (Sw34 ∷ CS24 ∷ []) (CS23 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0007 c4) ▸ done


-- nat 3 CS23: 2 steps
lem-nat-3-CS23 : WsL → ⟪ (Sw34 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-CS23 c4 = run b0
  where
  b0 : Chain (Sw34 ∷ CS23 ∷ []) (CS24 ∷ Sw34 ∷ [])
  b0 = at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 0 3 (CS24 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp CX40 at 1: 6 steps
lem-resp-CX40-at-1 : WsL → ⟪ (CX40 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CX41 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CX40-at-1 c4 = run b0
  where
  b0 : Chain (CX40 ∷ []) (Sw01 ∷ CX41 ∷ Sw01 ∷ [])
  b0 = at 1 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 c4)) ▸
       at 0 1 (Sw34 ∷ CX30 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 1 2 (Sw01 ∷ CX31 ∷ []) (wl0122 c4) ▸
       at 0 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 1 3 (CX41 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 BOX(2;03): 3 steps
lem-nat-0-BOX⟨2·03⟩ : WsL → ⟪ (Sw01 ∷ Bx2-03 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-13 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·03⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx2-03 ∷ []) (Bx2-13 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CZ03 ∷ []) (refl) ▸
       at 0 2 (CZ13 ∷ Sw01 ∷ []) (sym (wl0092 c4)) ▸
       at 0 1 (Bx2-13 ∷ []) (refl) ▸ done


-- nat 0 BOX(0;213): 8 steps
lem-nat-0-BOX⟨0·213⟩ : WsL → ⟪ (Sw01 ∷ Bx0-213 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-203 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·213⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-213 ∷ []) (Bx1-203 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw01 ∷ []) (sym (wl0096 c4)) ▸
       at 1 2 (Toff102 ∷ Sw01 ∷ []) (wl0099 c4) ▸
       at 2 2 (Bx2-13 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·03⟩ c4) ▸
       at 3 2 (Toff102 ∷ Sw01 ∷ []) (wl0099 c4) ▸
       at 4 2 (CCZ012 ∷ Sw01 ∷ []) (sym (wl0096 c4)) ▸
       at 5 2 (Bx2-13 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·03⟩ c4) ▸
       at 0 6 (Bx1-203 ∷ []) (refl) ▸ done


-- nat 0 BOX(2;0413): 8 steps
lem-nat-0-BOX⟨2·0413⟩ : WsL → ⟪ (Sw01 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1403 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·0413⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx2-0413 ∷ []) (Bx2-1403 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff204 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 1 2 (Toff214 ∷ Sw01 ∷ []) (lem-nat-0-TOFF204 c4) ▸
       at 2 2 (Bx1-203 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·213⟩ c4) ▸
       at 3 2 (Toff214 ∷ Sw01 ∷ []) (lem-nat-0-TOFF204 c4) ▸
       at 4 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 5 2 (Bx1-203 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·213⟩ c4) ▸
       at 0 6 (Bx2-1403 ∷ []) (refl) ▸ done


-- nat 3 CX42: 2 steps
lem-nat-3-CX42 : WsL → ⟪ (Sw34 ∷ CX42 ∷ []) ⟫ʷ ≈ ⟪ (CX32 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-CX42 c4 = run b0
  where
  b0 : Chain (Sw34 ∷ CX42 ∷ []) (CX32 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ CX32 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0007 c4) ▸ done


-- nat 0 CX40: 5 steps
lem-nat-0-CX40 : WsL → ⟪ (Sw01 ∷ CX40 ∷ []) ⟫ʷ ≈ ⟪ (CX41 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-CX40 c4 = run b0
  where
  b0 : Chain (Sw01 ∷ CX40 ∷ []) (CX41 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Sw34 ∷ CX30 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 1 2 (CX31 ∷ Sw01 ∷ []) (sym (wl0123 c4)) ▸
       at 2 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 0 3 (CX41 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 BOX(2;13): 3 steps
lem-nat-0-BOX⟨2·13⟩ : WsL → ⟪ (Sw01 ∷ Bx2-13 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-03 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·13⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx2-13 ∷ []) (Bx2-03 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CZ13 ∷ []) (refl) ▸
       at 0 2 (CZ03 ∷ Sw01 ∷ []) (sym (wl0088 c4)) ▸
       at 0 1 (Bx2-03 ∷ []) (refl) ▸ done


-- nat 0 BOX(1;203): 8 steps
lem-nat-0-BOX⟨1·203⟩ : WsL → ⟪ (Sw01 ∷ Bx1-203 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-213 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·203⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-203 ∷ []) (Bx0-213 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff102 ∷ Bx2-13 ∷ Toff102 ∷ CCZ012 ∷ Bx2-13 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw01 ∷ []) (sym (wl0096 c4)) ▸
       at 1 2 (Toff012 ∷ Sw01 ∷ []) (wl0097 c4) ▸
       at 2 2 (Bx2-03 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·13⟩ c4) ▸
       at 3 2 (Toff012 ∷ Sw01 ∷ []) (wl0097 c4) ▸
       at 4 2 (CCZ012 ∷ Sw01 ∷ []) (sym (wl0096 c4)) ▸
       at 5 2 (Bx2-03 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·13⟩ c4) ▸
       at 0 6 (Bx0-213 ∷ []) (refl) ▸ done


-- nat 0 BOX(2;1403): 8 steps
lem-nat-0-BOX⟨2·1403⟩ : WsL → ⟪ (Sw01 ∷ Bx2-1403 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·1403⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx2-1403 ∷ []) (Bx2-0413 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff214 ∷ Bx1-203 ∷ Toff214 ∷ CCZ124 ∷ Bx1-203 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 1 2 (Toff204 ∷ Sw01 ∷ []) (lem-nat-0-TOFF214 c4) ▸
       at 2 2 (Bx0-213 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·203⟩ c4) ▸
       at 3 2 (Toff204 ∷ Sw01 ∷ []) (lem-nat-0-TOFF214 c4) ▸
       at 4 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 5 2 (Bx0-213 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·203⟩ c4) ▸
       at 0 6 (Bx2-0413 ∷ []) (refl) ▸ done


-- resp CX40 at 2: 12 steps
lem-resp-CX40-at-2 : WsL → ⟪ (CX40 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CX41 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CX40-at-2 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CX40 ∷ []) (Sw12 ∷ Sw34 ∷ CX30 ∷ Sw34 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 0 1 (Sw34 ∷ CX30 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 1 2 (Sw12 ∷ CX30 ∷ []) (wl0124 c4) ▸
       at 0 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 1 3 (CX40 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 c4)) ▸
       at 1 1 (Sw34 ∷ CX30 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw12 ∷ Sw34 ∷ CX30 ∷ Sw34 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw01 ∷ CX41 ∷ Sw01 ∷ Sw12 ∷ [])
  b1 = at 3 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 2 2 (Sw01 ∷ CX31 ∷ []) (wl0122 c4) ▸
       at 1 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 2 3 (CX41 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp CX41 at 2: 4 steps
lem-resp-CX41-at-2 : WsL → ⟪ (CX41 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CX42 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CX41-at-2 c4 = run b0
  where
  b0 : Chain (CX41 ∷ []) (Sw12 ∷ Sw01 ∷ CX42 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 0 2 (Sw12 ∷ CX42 ∷ []) (wl0125 c4) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 c4)) ▸
       at 1 2 (Sw01 ∷ CX42 ∷ []) (sym (c₂ (Swap) (Swap ↑ • CX₁₀ • Swap ↑))) ▸ done


-- resp CS04 at 2: 12 steps
lem-resp-CS04-at-2 : WsL → ⟪ (CS04 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CS14 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CS04-at-2 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CS04 ∷ []) (Sw12 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 0 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 1 2 (Sw12 ∷ CS03 ∷ []) (wl0010 c4) ▸
       at 0 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 1 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 c4)) ▸
       at 1 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw12 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw01 ∷ CS14 ∷ Sw01 ∷ Sw12 ∷ [])
  b1 = at 3 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 2 2 (Sw01 ∷ CS13 ∷ []) (wl0019 c4) ▸
       at 1 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 2 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 2 BOX(1;032): 8 steps
lem-nat-2-BOX⟨1·032⟩ : WsL → ⟪ (Sw23 ∷ Bx1-032 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-023 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·032⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx1-032 ∷ []) (Bx1-023 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff103 ∷ Bx0-12 ∷ Toff103 ∷ CCZ013 ∷ Bx0-12 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 1 2 (Toff102 ∷ Sw23 ∷ []) (lem-nat-2-TOFF103 c4) ▸
       at 2 2 (Bx0-13 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·12⟩ c4) ▸
       at 3 2 (Toff102 ∷ Sw23 ∷ []) (lem-nat-2-TOFF103 c4) ▸
       at 4 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 5 2 (Bx0-13 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·12⟩ c4) ▸
       at 0 6 (Bx1-023 ∷ []) (refl) ▸ done


-- nat 2 BOX(0;1432): 8 steps
lem-nat-2-BOX⟨0·1432⟩ : WsL → ⟪ (Sw23 ∷ Bx0-1432 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·1432⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-1432 ∷ []) (Bx0-1423 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff014 ∷ Bx1-032 ∷ Toff014 ∷ CCZ014 ∷ Bx1-032 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 1 2 (Toff014 ∷ Sw23 ∷ []) (lem-nat-2-TOFF014 c4) ▸
       at 2 2 (Bx1-023 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·032⟩ c4) ▸
       at 3 2 (Toff014 ∷ Sw23 ∷ []) (lem-nat-2-TOFF014 c4) ▸
       at 4 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 5 2 (Bx1-023 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·032⟩ c4) ▸
       at 0 6 (Bx0-1423 ∷ []) (refl) ▸ done


-- resp TOFF014 at 3: 143 steps
lem-resp-TOFF014-at-3 : WsL → ⟪ (Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ Toff124 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-TOFF014-at-3 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (run b17)))))))))))))))))
  where
  b0 : Chain (Toff014 ∷ []) (Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw23 ∷ Sw23 ∷ [])
  b0 = at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 0 1 (Sw34 ∷ Toff013 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 2 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸ done

  b1 : Chain (Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw23 ∷ Sw23 ∷ []) (Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw23 ∷ Sw23 ∷ [])
  b1 = at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 4 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 6 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 8 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 9 2 [] (wl0006 c4) ▸ done

  b2 : Chain (Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw23 ∷ Sw23 ∷ []) (K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw34 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw23 ∷ Sw23 ∷ [])
  b2 = at 0 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 3 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 1 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 5 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 3 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸ done

  b3 : Chain (K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw34 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw23 ∷ Sw23 ∷ []) (K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Sw34 ∷ K0 ∷ ι ∷ Sw23 ∷ [])
  b3 = at 5 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 7 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 8 2 [] (wl0007 c4) ▸
       at 7 2 (Sw23 ∷ ι ∷ []) (c₁ (iI) (Swap ↑)) ▸
       at 6 2 (Sw23 ∷ K0 ∷ []) (c₁ (K) (Swap ↑)) ▸
       at 5 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 10 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (wl0013 c4) ▸ done

  b4 : Chain (K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Sw34 ∷ K0 ∷ ι ∷ Sw23 ∷ []) (K0 ∷ CS14 ∷ Sw23 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ Sw23 ∷ [])
  b4 = at 9 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 8 2 (Sw34 ∷ CS01 ∷ []) (c₂ (CS) (Swap ↑)) ▸
       at 7 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 5 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (sym (wl0013 c4)) ▸
       at 6 7 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw23 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Swap)) ▸
       at 3 2 (Sw23 ∷ CS14⁻ ∷ []) (wl0033 c4) ▸
       at 2 2 (Sw23 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Swap)) ▸ done

  b5 : Chain (K0 ∷ CS14 ∷ Sw23 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ Sw23 ∷ []) (Sw23 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw34 ∷ Sw34 ∷ CS13⁻ ∷ Sw34 ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ Sw23 ∷ [])
  b5 = at 1 2 (Sw23 ∷ CS14 ∷ []) (wl0021 c4) ▸
       at 0 2 (Sw23 ∷ K0 ∷ []) (c₁ (K) (Swap ↑)) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 2 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 4 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0007 c4) ▸
       at 4 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 6 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b6 : Chain (Sw23 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw34 ∷ Sw34 ∷ CS13⁻ ∷ Sw34 ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ Sw23 ∷ []) (Sw23 ∷ Sw34 ∷ Sw23 ∷ K0 ∷ Sw23 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw23 ∷ [])
  b6 = at 5 2 [] (wl0007 c4) ▸
       at 6 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0007 c4) ▸
       at 8 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 9 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 3 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸ done

  b7 : Chain (Sw23 ∷ Sw34 ∷ Sw23 ∷ K0 ∷ Sw23 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw23 ∷ []) (Sw23 ∷ Sw34 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw23 ∷ [])
  b7 = at 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0006 c4) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0006 c4) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0006 c4) ▸ done

  b8 : Chain (Sw23 ∷ Sw34 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Toff024 ∷ Sw12 ∷ Sw23 ∷ [])
  b8 = at 9 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 10 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 3 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff014 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 2 3 (Toff024 ∷ []) (by-assoc Eq.refl) ▸ done

  b9 : Chain (Sw23 ∷ Sw12 ∷ Toff024 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b9 = at 3 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 c4)) ▸
       at 2 1 (Sw12 ∷ Toff014 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw34 ∷ Toff013 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 5 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b10 : Chain (Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b10 = at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 7 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 9 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 11 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸ done

  b11 : Chain (Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b11 = at 12 2 [] (wl0006 c4) ▸
       at 3 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 6 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 4 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 6 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸ done

  b12 : Chain (Sw23 ∷ Sw12 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ K0 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b12 = at 10 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 8 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 10 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 11 2 [] (wl0007 c4) ▸
       at 2 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 3 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0008 c4)) ▸
       at 6 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸ done

  b13 : Chain (Sw23 ∷ Sw12 ∷ K0 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b13 = at 4 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS24⁻ ∷ Sw12 ∷ []) (sym (wl0009 c4)) ▸
       at 8 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 6 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 8 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 c4)) ▸
       at 9 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸ done

  b14 : Chain (Sw23 ∷ Sw12 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ CS03 ∷ Sw01 ∷ Sw34 ∷ K1 ∷ ι ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b14 = at 7 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 9 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 10 2 [] (wl0001 c4) ▸
       at 9 2 (Sw01 ∷ ι ∷ []) (sym (wl0030 c4)) ▸
       at 8 2 (Sw01 ∷ K1 ∷ []) (wl0031 c4) ▸
       at 7 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸ done

  b15 : Chain (Sw23 ∷ Sw12 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ CS03 ∷ Sw01 ∷ Sw34 ∷ K1 ∷ ι ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ K1 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K1 ∷ ι ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b15 = at 8 2 (Sw01 ∷ CS13 ∷ []) (wl0019 c4) ▸
       at 7 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 8 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw01 ∷ CX12 ∷ []) (wl0048 c4) ▸
       at 5 2 (Sw01 ∷ CS24⁻ ∷ []) (sym (c₂ (Swap) (Swap ↑ • (CS • CS • CS) • Swap ↑))) ▸
       at 4 2 (Sw01 ∷ CX12 ∷ []) (wl0048 c4) ▸
       at 3 2 (Sw01 ∷ CS24 ∷ []) (sym (c₂ (Swap) (Swap ↑ • CS • Swap ↑))) ▸
       at 2 2 (Sw01 ∷ K1 ∷ []) (wl0031 c4) ▸ done

  b16 : Chain (Sw23 ∷ Sw12 ∷ Sw01 ∷ K1 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K1 ∷ ι ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ Sw34 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw34 ∷ CS14 ∷ K1 ∷ ι ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b16 = at 3 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 4 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 6 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0007 c4) ▸
       at 6 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 8 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0007 c4) ▸
       at 8 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸ done

  b17 : Chain (Sw23 ∷ Sw12 ∷ Sw01 ∷ Sw34 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw34 ∷ CS14 ∷ K1 ∷ ι ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ Toff124 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b17 = at 10 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (wl0007 c4) ▸
       at 10 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 11 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 4 8 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (wl0032 c4) ▸
       at 4 8 (Toff123 ∷ []) (by-assoc Eq.refl) ▸
       at 3 3 (Toff124 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 1 BOX(3;02): 3 steps
lem-nat-1-BOX⟨3·02⟩ : WsL → ⟪ (Sw12 ∷ Bx3-02 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-01 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·02⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-02 ∷ []) (Bx3-01 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ02 ∷ []) (refl) ▸
       at 0 2 (CZ01 ∷ Sw12 ∷ []) (lem-nat-1-CZ02 c4) ▸
       at 0 1 (Bx3-01 ∷ []) (refl) ▸ done


-- nat 1 BOX(0;312): 8 steps
lem-nat-1-BOX⟨0·312⟩ : WsL → ⟪ (Sw12 ∷ Bx0-312 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-321 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·312⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-312 ∷ []) (Bx0-321 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff013 ∷ Bx3-02 ∷ Toff013 ∷ CCZ013 ∷ Bx3-02 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 1 2 (Toff023 ∷ Sw12 ∷ []) (lem-nat-1-TOFF013 c4) ▸
       at 2 2 (Bx3-01 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·02⟩ c4) ▸
       at 3 2 (Toff023 ∷ Sw12 ∷ []) (lem-nat-1-TOFF013 c4) ▸
       at 4 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 5 2 (Bx3-01 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·02⟩ c4) ▸
       at 0 6 (Bx0-321 ∷ []) (refl) ▸ done


-- nat 1 BOX(3;0412): 8 steps
lem-nat-1-BOX⟨3·0412⟩ : WsL → ⟪ (Sw12 ∷ Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0421 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·0412⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-0412 ∷ []) (Bx3-0421 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff304 ∷ Bx0-312 ∷ Toff304 ∷ CCZ034 ∷ Bx0-312 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 1 2 (Toff304 ∷ Sw12 ∷ []) (lem-nat-1-TOFF304 c4) ▸
       at 2 2 (Bx0-321 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·312⟩ c4) ▸
       at 3 2 (Toff304 ∷ Sw12 ∷ []) (lem-nat-1-TOFF304 c4) ▸
       at 4 2 (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4) ▸
       at 5 2 (Bx0-321 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·312⟩ c4) ▸
       at 0 6 (Bx3-0421 ∷ []) (refl) ▸ done


-- nat 1 SBOX(3;0;2;1): 3 steps
lem-nat-1-SBOX⟨3·0·2·1⟩ : WsL → ⟪ (Sw12 ∷ Sb3-0-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-1-2 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨3·0·2·1⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb3-0-2-1 ∷ []) (Sb3-0-1-2 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS02 ∷ []) (refl) ▸
       at 0 2 (CS01 ∷ Sw12 ∷ []) (lem-nat-1-CS02 c4) ▸
       at 0 1 (Sb3-0-1-2 ∷ []) (refl) ▸ done


-- nat 1 CSd02: 2 steps
lem-nat-1-CSd02 : WsL → ⟪ (Sw12 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-CSd02 c4 = run b0
  where
  b0 : Chain (Sw12 ∷ CS02⁻ ∷ []) (CS01⁻ ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0001 c4) ▸ done


-- nat 1 SBOXd(3;0;2;1): 3 steps
lem-nat-1-SBOXd⟨3·0·2·1⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻3-0-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻3-0-1-2 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨3·0·2·1⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻3-0-2-1 ∷ []) (Sb⁻3-0-1-2 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS02⁻ ∷ []) (refl) ▸
       at 0 2 (CS01⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd02 c4) ▸
       at 0 1 (Sb⁻3-0-1-2 ∷ []) (refl) ▸ done


-- nat 1 SBOX(3;0;41;2): 7 steps
lem-nat-1-SBOX⟨3·0·41·2⟩ : WsL → ⟪ (Sw12 ∷ Sb3-0-41-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-42-1 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨3·0·41·2⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb3-0-41-2 ∷ []) (Sb3-0-42-1 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (refl) ▸
       at 0 2 (Bx3-0421 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0412⟩ c4) ▸
       at 1 2 (Toff124 ∷ Sw12 ∷ []) (wl0126 c4) ▸
       at 2 2 (Sb3-0-1-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·2·1⟩ c4) ▸
       at 3 2 (Toff124 ∷ Sw12 ∷ []) (wl0126 c4) ▸
       at 4 2 (Sb⁻3-0-1-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨3·0·2·1⟩ c4) ▸
       at 0 5 (Sb3-0-42-1 ∷ []) (refl) ▸ done


-- nat 2 BOX(1;02): 3 steps
lem-nat-2-BOX⟨1·02⟩ : WsL → ⟪ (Sw23 ∷ Bx1-02 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-03 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·02⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx1-02 ∷ []) (Bx1-03 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ02 ∷ []) (refl) ▸
       at 0 2 (CZ03 ∷ Sw23 ∷ []) (lem-nat-2-CZ02 c4) ▸
       at 0 1 (Bx1-03 ∷ []) (refl) ▸ done


-- nat 2 BOX(0;132): 8 steps
lem-nat-2-BOX⟨0·132⟩ : WsL → ⟪ (Sw23 ∷ Bx0-132 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-123 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·132⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-132 ∷ []) (Bx0-123 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff013 ∷ Bx1-02 ∷ Toff013 ∷ CCZ013 ∷ Bx1-02 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 1 2 (Toff012 ∷ Sw23 ∷ []) (lem-nat-2-TOFF013 c4) ▸
       at 2 2 (Bx1-03 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·02⟩ c4) ▸
       at 3 2 (Toff012 ∷ Sw23 ∷ []) (lem-nat-2-TOFF013 c4) ▸
       at 4 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 5 2 (Bx1-03 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·02⟩ c4) ▸
       at 0 6 (Bx0-123 ∷ []) (refl) ▸ done


-- nat 2 BOX(1;0432): 8 steps
lem-nat-2-BOX⟨1·0432⟩ : WsL → ⟪ (Sw23 ∷ Bx1-0432 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0423 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·0432⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx1-0432 ∷ []) (Bx1-0423 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff104 ∷ Bx0-132 ∷ Toff104 ∷ CCZ014 ∷ Bx0-132 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 1 2 (Toff104 ∷ Sw23 ∷ []) (lem-nat-2-TOFF104 c4) ▸
       at 2 2 (Bx0-123 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·132⟩ c4) ▸
       at 3 2 (Toff104 ∷ Sw23 ∷ []) (lem-nat-2-TOFF104 c4) ▸
       at 4 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 5 2 (Bx0-123 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·132⟩ c4) ▸
       at 0 6 (Bx1-0423 ∷ []) (refl) ▸ done


-- nat 2 CS02: 2 steps
lem-nat-2-CS02 : WsL → ⟪ (Sw23 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-CS02 c4 = run b0
  where
  b0 : Chain (Sw23 ∷ CS02 ∷ []) (CS03 ∷ Sw23 ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 0 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 2 SBOX(1;0;2;3): 3 steps
lem-nat-2-SBOX⟨1·0·2·3⟩ : WsL → ⟪ (Sw23 ∷ Sb1-0-2-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-3-2 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨1·0·2·3⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb1-0-2-3 ∷ []) (Sb1-0-3-2 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS02 ∷ []) (refl) ▸
       at 0 2 (CS03 ∷ Sw23 ∷ []) (lem-nat-2-CS02 c4) ▸
       at 0 1 (Sb1-0-3-2 ∷ []) (refl) ▸ done


-- nat 2 CSd02: 2 steps
lem-nat-2-CSd02 : WsL → ⟪ (Sw23 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-CSd02 c4 = run b0
  where
  b0 : Chain (Sw23 ∷ CS02⁻ ∷ []) (CS03⁻ ∷ Sw23 ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 0 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 2 SBOXd(1;0;2;3): 3 steps
lem-nat-2-SBOXd⟨1·0·2·3⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻1-0-2-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-3-2 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨1·0·2·3⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻1-0-2-3 ∷ []) (Sb⁻1-0-3-2 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS02⁻ ∷ []) (refl) ▸
       at 0 2 (CS03⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd02 c4) ▸
       at 0 1 (Sb⁻1-0-3-2 ∷ []) (refl) ▸ done


-- nat 2 SBOX(1;0;43;2): 7 steps
lem-nat-2-SBOX⟨1·0·43·2⟩ : WsL → ⟪ (Sw23 ∷ Sb1-0-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-42-3 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨1·0·43·2⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb1-0-43-2 ∷ []) (Sb1-0-42-3 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) (refl) ▸
       at 0 2 (Bx1-0423 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·0432⟩ c4) ▸
       at 1 2 (Toff324 ∷ Sw23 ∷ []) (wl0127 c4) ▸
       at 2 2 (Sb1-0-3-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·2·3⟩ c4) ▸
       at 3 2 (Toff324 ∷ Sw23 ∷ []) (wl0127 c4) ▸
       at 4 2 (Sb⁻1-0-3-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·0·2·3⟩ c4) ▸
       at 0 5 (Sb1-0-42-3 ∷ []) (refl) ▸ done


-- nat 2 BOX(3;01): 2 steps
lem-nat-2-BOX⟨3·01⟩ : WsL → ⟪ (Sw23 ∷ Bx3-01 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-01 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·01⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx3-01 ∷ []) (Bx2-01 ∷ Sw23 ∷ [])
  b0 = at 0 2 (Bx3-01 ∷ Sw23 ∷ []) (sym (c₂ (CZ) (Swap))) ▸
       at 0 1 (Bx2-01 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 2 BOX(0;321): 8 steps
lem-nat-2-BOX⟨0·321⟩ : WsL → ⟪ (Sw23 ∷ Bx0-321 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-231 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·321⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-321 ∷ []) (Bx0-231 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff023 ∷ Bx3-01 ∷ Toff023 ∷ CCZ023 ∷ Bx3-01 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw23 ∷ []) (sym (wl0065 c4)) ▸
       at 1 2 (Toff023 ∷ Sw23 ∷ []) (wl0093 c4) ▸
       at 2 2 (Bx2-01 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·01⟩ c4) ▸
       at 3 2 (Toff023 ∷ Sw23 ∷ []) (wl0093 c4) ▸
       at 4 2 (CCZ023 ∷ Sw23 ∷ []) (sym (wl0065 c4)) ▸
       at 5 2 (Bx2-01 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·01⟩ c4) ▸
       at 0 6 (Bx0-231 ∷ []) (refl) ▸ done


-- nat 2 BOX(3;0421): 8 steps
lem-nat-2-BOX⟨3·0421⟩ : WsL → ⟪ (Sw23 ∷ Bx3-0421 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0431 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·0421⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx3-0421 ∷ []) (Bx2-0431 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff304 ∷ Bx0-321 ∷ Toff304 ∷ CCZ034 ∷ Bx0-321 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 1 2 (Toff204 ∷ Sw23 ∷ []) (lem-nat-2-TOFF304 c4) ▸
       at 2 2 (Bx0-231 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·321⟩ c4) ▸
       at 3 2 (Toff204 ∷ Sw23 ∷ []) (lem-nat-2-TOFF304 c4) ▸
       at 4 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 5 2 (Bx0-231 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·321⟩ c4) ▸
       at 0 6 (Bx2-0431 ∷ []) (refl) ▸ done


-- nat 2 TOFF124: 2 steps
lem-nat-2-TOFF124 : WsL → ⟪ (Sw23 ∷ Toff124 ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-TOFF124 c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Toff124 ∷ []) (Toff134 ∷ Sw23 ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 0 3 (Toff134 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 2 SBOX(3;0;1;2): 2 steps
lem-nat-2-SBOX⟨3·0·1·2⟩ : WsL → ⟪ (Sw23 ∷ Sb3-0-1-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-1-3 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨3·0·1·2⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb3-0-1-2 ∷ []) (Sb2-0-1-3 ∷ Sw23 ∷ [])
  b0 = at 0 2 (Sb3-0-1-2 ∷ Sw23 ∷ []) (sym (c₂ (CS) (Swap))) ▸
       at 0 1 (Sb2-0-1-3 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 2 SBOXd(3;0;1;2): 2 steps
lem-nat-2-SBOXd⟨3·0·1·2⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻3-0-1-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-0-1-3 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨3·0·1·2⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻3-0-1-2 ∷ []) (Sb⁻2-0-1-3 ∷ Sw23 ∷ [])
  b0 = at 0 2 (Sb⁻3-0-1-2 ∷ Sw23 ∷ []) (sym (c₂ (CS • CS • CS) (Swap))) ▸
       at 0 1 (Sb⁻2-0-1-3 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 2 SBOX(3;0;42;1): 7 steps
lem-nat-2-SBOX⟨3·0·42·1⟩ : WsL → ⟪ (Sw23 ∷ Sb3-0-42-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-43-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨3·0·42·1⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb3-0-42-1 ∷ []) (Sb2-0-43-1 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx3-0421 ∷ Toff124 ∷ Sb3-0-1-2 ∷ Toff124 ∷ Sb⁻3-0-1-2 ∷ []) (refl) ▸
       at 0 2 (Bx2-0431 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0421⟩ c4) ▸
       at 1 2 (Toff134 ∷ Sw23 ∷ []) (lem-nat-2-TOFF124 c4) ▸
       at 2 2 (Sb2-0-1-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·0·1·2⟩ c4) ▸
       at 3 2 (Toff134 ∷ Sw23 ∷ []) (lem-nat-2-TOFF124 c4) ▸
       at 4 2 (Sb⁻2-0-1-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨3·0·1·2⟩ c4) ▸
       at 0 5 (Sb2-0-43-1 ∷ []) (refl) ▸ done


-- nat 3 BOX(0;142): 8 steps
lem-nat-3-BOX⟨0·142⟩ : WsL → ⟪ (Sw34 ∷ Bx0-142 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-132 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·142⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx0-142 ∷ []) (Bx0-132 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff014 ∷ Bx1-02 ∷ Toff014 ∷ CCZ014 ∷ Bx1-02 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4) ▸
       at 1 2 (Toff013 ∷ Sw34 ∷ []) (lem-nat-3-TOFF014 c4) ▸
       at 2 2 (Bx1-02 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑ • CZ • Swap ↑) (Swap))) ▸
       at 3 2 (Toff013 ∷ Sw34 ∷ []) (lem-nat-3-TOFF014 c4) ▸
       at 4 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4) ▸
       at 5 2 (Bx1-02 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑ • CZ • Swap ↑) (Swap))) ▸
       at 0 6 (Bx0-132 ∷ []) (refl) ▸ done


-- nat 3 BOX(1;0342): 8 steps
lem-nat-3-BOX⟨1·0342⟩ : WsL → ⟪ (Sw34 ∷ Bx1-0342 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0432 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨1·0342⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx1-0342 ∷ []) (Bx1-0432 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff103 ∷ Bx0-142 ∷ Toff103 ∷ CCZ013 ∷ Bx0-142 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4) ▸
       at 1 2 (Toff104 ∷ Sw34 ∷ []) (lem-nat-3-TOFF103 c4) ▸
       at 2 2 (Bx0-132 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·142⟩ c4) ▸
       at 3 2 (Toff104 ∷ Sw34 ∷ []) (lem-nat-3-TOFF103 c4) ▸
       at 4 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4) ▸
       at 5 2 (Bx0-132 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·142⟩ c4) ▸
       at 0 6 (Bx1-0432 ∷ []) (refl) ▸ done


-- nat 3 SBOX(1;0;2;4): 2 steps
lem-nat-3-SBOX⟨1·0·2·4⟩ : WsL → ⟪ (Sw34 ∷ Sb1-0-2-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-2-3 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨1·0·2·4⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb1-0-2-4 ∷ []) (Sb1-0-2-3 ∷ Sw34 ∷ [])
  b0 = at 0 2 (Sb1-0-2-4 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑ • CS • Swap ↑) (Swap))) ▸
       at 0 1 (Sb1-0-2-3 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 3 SBOXd(1;0;2;4): 2 steps
lem-nat-3-SBOXd⟨1·0·2·4⟩ : WsL → ⟪ (Sw34 ∷ Sb⁻1-0-2-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-2-3 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨1·0·2·4⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb⁻1-0-2-4 ∷ []) (Sb⁻1-0-2-3 ∷ Sw34 ∷ [])
  b0 = at 0 2 (Sb⁻1-0-2-4 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑ • (CS • CS • CS) • Swap ↑) (Swap))) ▸
       at 0 1 (Sb⁻1-0-2-3 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 3 SBOX(1;0;34;2): 7 steps
lem-nat-3-SBOX⟨1·0·34·2⟩ : WsL → ⟪ (Sw34 ∷ Sb1-0-34-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-43-2 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨1·0·34·2⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb1-0-34-2 ∷ []) (Sb1-0-43-2 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx1-0342 ∷ Toff234 ∷ Sb1-0-2-4 ∷ Toff234 ∷ Sb⁻1-0-2-4 ∷ []) (refl) ▸
       at 0 2 (Bx1-0432 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·0342⟩ c4) ▸
       at 1 2 (Toff234 ∷ Sw34 ∷ []) (wl0128 c4) ▸
       at 2 2 (Sb1-0-2-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨1·0·2·4⟩ c4) ▸
       at 3 2 (Toff234 ∷ Sw34 ∷ []) (wl0128 c4) ▸
       at 4 2 (Sb⁻1-0-2-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨1·0·2·4⟩ c4) ▸
       at 0 5 (Sb1-0-43-2 ∷ []) (refl) ▸ done


-- nat 3 BOX(0;231): 8 steps
lem-nat-3-BOX⟨0·231⟩ : WsL → ⟪ (Sw34 ∷ Bx0-231 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-241 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·231⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx0-231 ∷ []) (Bx0-241 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff023 ∷ Bx2-01 ∷ Toff023 ∷ CCZ023 ∷ Bx2-01 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw34 ∷ []) (lem-nat-3-CCZ023 c4) ▸
       at 1 2 (Toff024 ∷ Sw34 ∷ []) (lem-nat-3-TOFF023 c4) ▸
       at 2 2 (Bx2-01 ∷ Sw34 ∷ []) (sym (c₂ (CZ) (Swap ↑))) ▸
       at 3 2 (Toff024 ∷ Sw34 ∷ []) (lem-nat-3-TOFF023 c4) ▸
       at 4 2 (CCZ024 ∷ Sw34 ∷ []) (lem-nat-3-CCZ023 c4) ▸
       at 5 2 (Bx2-01 ∷ Sw34 ∷ []) (sym (c₂ (CZ) (Swap ↑))) ▸
       at 0 6 (Bx0-241 ∷ []) (refl) ▸ done


-- nat 3 BOX(2;0431): 8 steps
lem-nat-3-BOX⟨2·0431⟩ : WsL → ⟪ (Sw34 ∷ Bx2-0431 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0341 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨2·0431⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx2-0431 ∷ []) (Bx2-0341 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff204 ∷ Bx0-231 ∷ Toff204 ∷ CCZ024 ∷ Bx0-231 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 c4) ▸
       at 1 2 (Toff203 ∷ Sw34 ∷ []) (lem-nat-3-TOFF204 c4) ▸
       at 2 2 (Bx0-241 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·231⟩ c4) ▸
       at 3 2 (Toff203 ∷ Sw34 ∷ []) (lem-nat-3-TOFF204 c4) ▸
       at 4 2 (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 c4) ▸
       at 5 2 (Bx0-241 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·231⟩ c4) ▸
       at 0 6 (Bx2-0341 ∷ []) (refl) ▸ done


-- nat 3 SBOX(2;0;1;3): 2 steps
lem-nat-3-SBOX⟨2·0·1·3⟩ : WsL → ⟪ (Sw34 ∷ Sb2-0-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-1-4 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨2·0·1·3⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb2-0-1-3 ∷ []) (Sb2-0-1-4 ∷ Sw34 ∷ [])
  b0 = at 0 2 (Sb2-0-1-3 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸
       at 0 1 (Sb2-0-1-4 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 3 SBOXd(2;0;1;3): 2 steps
lem-nat-3-SBOXd⟨2·0·1·3⟩ : WsL → ⟪ (Sw34 ∷ Sb⁻2-0-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-0-1-4 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨2·0·1·3⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb⁻2-0-1-3 ∷ []) (Sb⁻2-0-1-4 ∷ Sw34 ∷ [])
  b0 = at 0 2 (Sb⁻2-0-1-3 ∷ Sw34 ∷ []) (sym (c₂ (CS • CS • CS) (Swap ↑))) ▸
       at 0 1 (Sb⁻2-0-1-4 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 3 SBOX(2;0;43;1): 7 steps
lem-nat-3-SBOX⟨2·0·43·1⟩ : WsL → ⟪ (Sw34 ∷ Sb2-0-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-34-1 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨2·0·43·1⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb2-0-43-1 ∷ []) (Sb2-0-34-1 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx2-0431 ∷ Toff134 ∷ Sb2-0-1-3 ∷ Toff134 ∷ Sb⁻2-0-1-3 ∷ []) (refl) ▸
       at 0 2 (Bx2-0341 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·0431⟩ c4) ▸
       at 1 2 (Toff134 ∷ Sw34 ∷ []) (wl0129 c4) ▸
       at 2 2 (Sb2-0-1-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨2·0·1·3⟩ c4) ▸
       at 3 2 (Toff134 ∷ Sw34 ∷ []) (wl0129 c4) ▸
       at 4 2 (Sb⁻2-0-1-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨2·0·1·3⟩ c4) ▸
       at 0 5 (Sb2-0-34-1 ∷ []) (refl) ▸ done


-- nat 0 BOX(0;12): 3 steps
lem-nat-0-BOX⟨0·12⟩ : WsL → ⟪ (Sw01 ∷ Bx0-12 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-02 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·12⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-12 ∷ []) (Bx1-02 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CZ12 ∷ []) (refl) ▸
       at 0 2 (CZ02 ∷ Sw01 ∷ []) (sym (wl0105 c4)) ▸
       at 0 1 (Bx1-02 ∷ []) (refl) ▸ done


-- nat 0 BOX(1;042): 8 steps
lem-nat-0-BOX⟨1·042⟩ : WsL → ⟪ (Sw01 ∷ Bx1-042 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-142 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·042⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-042 ∷ []) (Bx0-142 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff104 ∷ Bx0-12 ∷ Toff104 ∷ CCZ014 ∷ Bx0-12 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 1 2 (Toff014 ∷ Sw01 ∷ []) (lem-nat-0-TOFF104 c4) ▸
       at 2 2 (Bx1-02 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·12⟩ c4) ▸
       at 3 2 (Toff014 ∷ Sw01 ∷ []) (lem-nat-0-TOFF104 c4) ▸
       at 4 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 5 2 (Bx1-02 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·12⟩ c4) ▸
       at 0 6 (Bx0-142 ∷ []) (refl) ▸ done


-- nat 0 BOX(0;1342): 8 steps
lem-nat-0-BOX⟨0·1342⟩ : WsL → ⟪ (Sw01 ∷ Bx0-1342 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0342 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·1342⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-1342 ∷ []) (Bx1-0342 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff013 ∷ Bx1-042 ∷ Toff013 ∷ CCZ013 ∷ Bx1-042 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw01 ∷ []) (sym (wl0100 c4)) ▸
       at 1 2 (Toff103 ∷ Sw01 ∷ []) (wl0101 c4) ▸
       at 2 2 (Bx0-142 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·042⟩ c4) ▸
       at 3 2 (Toff103 ∷ Sw01 ∷ []) (wl0101 c4) ▸
       at 4 2 (CCZ013 ∷ Sw01 ∷ []) (sym (wl0100 c4)) ▸
       at 5 2 (Bx0-142 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·042⟩ c4) ▸
       at 0 6 (Bx1-0342 ∷ []) (refl) ▸ done


-- nat 0 SBOX(0;1;2;4): 3 steps
lem-nat-0-SBOX⟨0·1·2·4⟩ : WsL → ⟪ (Sw01 ∷ Sb0-1-2-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-2-4 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨0·1·2·4⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb0-1-2-4 ∷ []) (Sb1-0-2-4 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS12 ∷ []) (refl) ▸
       at 0 2 (CS02 ∷ Sw01 ∷ []) (sym (wl0035 c4)) ▸
       at 0 1 (Sb1-0-2-4 ∷ []) (refl) ▸ done


-- nat 0 SBOXd(0;1;2;4): 3 steps
lem-nat-0-SBOXd⟨0·1·2·4⟩ : WsL → ⟪ (Sw01 ∷ Sb⁻0-1-2-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-2-4 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨0·1·2·4⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻0-1-2-4 ∷ []) (Sb⁻1-0-2-4 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS12⁻ ∷ []) (refl) ▸
       at 0 2 (CS02⁻ ∷ Sw01 ∷ []) (sym (wl0036 c4)) ▸
       at 0 1 (Sb⁻1-0-2-4 ∷ []) (refl) ▸ done


-- nat 0 SBOX(0;1;34;2): 7 steps
lem-nat-0-SBOX⟨0·1·34·2⟩ : WsL → ⟪ (Sw01 ∷ Sb0-1-34-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-34-2 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨0·1·34·2⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb0-1-34-2 ∷ []) (Sb1-0-34-2 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx0-1342 ∷ Toff234 ∷ Sb0-1-2-4 ∷ Toff234 ∷ Sb⁻0-1-2-4 ∷ []) (refl) ▸
       at 0 2 (Bx1-0342 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1342⟩ c4) ▸
       at 1 2 (Toff234 ∷ Sw01 ∷ []) (c₂ (Swap) (Toff)) ▸
       at 2 2 (Sb1-0-2-4 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·2·4⟩ c4) ▸
       at 3 2 (Toff234 ∷ Sw01 ∷ []) (c₂ (Swap) (Toff)) ▸
       at 4 2 (Sb⁻1-0-2-4 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨0·1·2·4⟩ c4) ▸
       at 0 5 (Sb1-0-34-2 ∷ []) (refl) ▸ done


-- nat 0 BOX(2;01): 3 steps
lem-nat-0-BOX⟨2·01⟩ : WsL → ⟪ (Sw01 ∷ Bx2-01 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-10 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·01⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx2-01 ∷ []) (Bx2-10 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CZ01 ∷ []) (refl) ▸
       at 0 2 (CZ01 ∷ Sw01 ∷ []) (sym (wl0130 c4)) ▸
       at 0 1 (Bx2-10 ∷ []) (refl) ▸ done


-- nat 0 BOX(0;241): 8 steps
lem-nat-0-BOX⟨0·241⟩ : WsL → ⟪ (Sw01 ∷ Bx0-241 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-240 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·241⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-241 ∷ []) (Bx1-240 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff024 ∷ Bx2-01 ∷ Toff024 ∷ CCZ024 ∷ Bx2-01 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 1 2 (Toff124 ∷ Sw01 ∷ []) (lem-nat-0-TOFF024 c4) ▸
       at 2 2 (Bx2-10 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·01⟩ c4) ▸
       at 3 2 (Toff124 ∷ Sw01 ∷ []) (lem-nat-0-TOFF024 c4) ▸
       at 4 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 5 2 (Bx2-10 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·01⟩ c4) ▸
       at 0 6 (Bx1-240 ∷ []) (refl) ▸ done


-- nat 0 BOX(2;0341): 8 steps
lem-nat-0-BOX⟨2·0341⟩ : WsL → ⟪ (Sw01 ∷ Bx2-0341 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1340 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·0341⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx2-0341 ∷ []) (Bx2-1340 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff203 ∷ Bx0-241 ∷ Toff203 ∷ CCZ023 ∷ Bx0-241 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw01 ∷ []) (sym (wl0103 c4)) ▸
       at 1 2 (Toff213 ∷ Sw01 ∷ []) (wl0104 c4) ▸
       at 2 2 (Bx1-240 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·241⟩ c4) ▸
       at 3 2 (Toff213 ∷ Sw01 ∷ []) (wl0104 c4) ▸
       at 4 2 (CCZ123 ∷ Sw01 ∷ []) (sym (wl0103 c4)) ▸
       at 5 2 (Bx1-240 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·241⟩ c4) ▸
       at 0 6 (Bx2-1340 ∷ []) (refl) ▸ done


-- nat 0 TOFF134: 100 steps
lem-nat-0-TOFF134 : WsL → ⟪ (Sw01 ∷ Toff134 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-TOFF134 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (run b12))))))))))))
  where
  b0 : Chain (Sw01 ∷ Toff134 ∷ []) (Sw01 ∷ Sw23 ∷ K1 ∷ CS24 ∷ CX12 ∷ Sw34 ∷ CS23⁻ ∷ Sw34 ∷ Sw34 ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw34 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Toff124 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ Toff123 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 5 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 3 3 (CS24 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸ done

  b1 : Chain (Sw01 ∷ Sw23 ∷ K1 ∷ CS24 ∷ CX12 ∷ Sw34 ∷ CS23⁻ ∷ Sw34 ∷ Sw34 ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw34 ∷ Sw23 ∷ []) (Sw01 ∷ K1 ∷ Sw23 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K1 ∷ ι1 ∷ Sw23 ∷ [])
  b1 = at 5 3 (CS24⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 9 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 7 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 9 2 (ι1 ∷ Sw34 ∷ []) (sym (c₂ (iI ↑) (Swap ↑))) ▸
       at 10 2 [] (wl0007 c4) ▸
       at 1 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸ done

  b2 : Chain (Sw01 ∷ K1 ∷ Sw23 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K1 ∷ ι1 ∷ Sw23 ∷ []) (Sw01 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1 ∷ Sw23 ∷ ι1 ∷ Sw23 ∷ [])
  b2 = at 2 2 (CS34 ∷ Sw23 ∷ []) (sym (wl0011 c4)) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 3 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS34⁻ ∷ Sw23 ∷ []) (sym (wl0012 c4)) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 5 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CS14 ∷ Sw23 ∷ []) (sym (wl0021 c4)) ▸
       at 7 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸ done

  b3 : Chain (Sw01 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1 ∷ Sw23 ∷ ι1 ∷ Sw23 ∷ []) (K0 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw01 ∷ Sw34 ∷ CS13 ∷ Sw34 ∷ K1 ∷ ι1 ∷ [])
  b3 = at 8 2 (ι1 ∷ Sw23 ∷ []) (sym (c₂ (iI ↑) (Swap))) ▸
       at 9 2 [] (wl0006 c4) ▸
       at 0 2 (K0 ∷ Sw01 ∷ []) (sym (wl0031 c4)) ▸
       at 1 2 (CS34 ∷ Sw01 ∷ []) (c₂ (Swap) (CS ↑)) ▸
       at 2 2 (CX03 ∷ Sw01 ∷ []) (sym (wl0020 c4)) ▸
       at 3 2 (CS34⁻ ∷ Sw01 ∷ []) (c₂ (Swap) ((CS • CS • CS) ↑)) ▸
       at 4 2 (CX03 ∷ Sw01 ∷ []) (sym (wl0020 c4)) ▸
       at 6 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b4 : Chain (K0 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw01 ∷ Sw34 ∷ CS13 ∷ Sw34 ∷ K1 ∷ ι1 ∷ []) (Sw23 ∷ K0 ∷ Sw23 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K0 ∷ ι1 ∷ Sw01 ∷ [])
  b4 = at 5 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 6 2 (CS03 ∷ Sw01 ∷ []) (sym (wl0019 c4)) ▸
       at 7 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 5 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K0 ∷ Sw01 ∷ []) (sym (wl0031 c4)) ▸
       at 7 2 (ι1 ∷ Sw01 ∷ []) (wl0073 c4) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 1 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸ done

  b5 : Chain (Sw23 ∷ K0 ∷ Sw23 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K0 ∷ ι1 ∷ Sw01 ∷ []) (Sw23 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ K0 ∷ ι1 ∷ Sw01 ∷ [])
  b5 = at 2 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0015 c4)) ▸
       at 4 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0006 c4) ▸
       at 4 2 (CS24⁻ ∷ Sw23 ∷ []) (sym (wl0016 c4)) ▸
       at 6 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0006 c4) ▸
       at 7 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (wl0013 c4) ▸ done

  b6 : Chain (Sw23 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ K0 ∷ ι1 ∷ Sw01 ∷ []) (Sw23 ∷ Sw12 ∷ Sw12 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0 ∷ ι1 ∷ Sw23 ∷ Sw01 ∷ [])
  b6 = at 8 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 9 2 (CS01 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸
       at 10 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 11 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (sym (wl0013 c4)) ▸
       at 6 7 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 8 2 (ι1 ∷ Sw23 ∷ []) (sym (c₂ (iI ↑) (Swap))) ▸
       at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸ done

  b7 : Chain (Sw23 ∷ Sw12 ∷ Sw12 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0 ∷ ι1 ∷ Sw23 ∷ Sw01 ∷ []) (Sw23 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw12 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ K0 ∷ ι1 ∷ Sw23 ∷ Sw01 ∷ [])
  b7 = at 2 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 3 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0017 c4)) ▸
       at 5 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0001 c4) ▸
       at 5 2 (CS14⁻ ∷ Sw12 ∷ []) (sym (wl0018 c4)) ▸
       at 7 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0001 c4) ▸
       at 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b8 : Chain (Sw23 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw12 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ K0 ∷ ι1 ∷ Sw23 ∷ Sw01 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ Sw34 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ ι1 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ [])
  b8 = at 7 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 8 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 c4)) ▸
       at 9 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 7 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 9 2 (ι1 ∷ Sw12 ∷ []) (wl0074 c4) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 3 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸ done

  b9 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ Sw34 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ ι1 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw34 ∷ K0 ∷ ι1 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ [])
  b9 = at 5 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0007 c4) ▸
       at 5 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 7 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0007 c4) ▸
       at 7 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 9 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0007 c4) ▸ done

  b10 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw34 ∷ K0 ∷ ι1 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ Sw23 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ K0 ∷ ι1 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ [])
  b10 = at 9 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 10 2 (ι1 ∷ Sw34 ∷ []) (sym (c₂ (iI ↑) (Swap ↑))) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 4 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0006 c4) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b11 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ Sw23 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ K0 ∷ ι1 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ [])
  b11 = at 7 2 [] (wl0006 c4) ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (wl0006 c4) ▸
       at 10 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 11 2 (ι1 ∷ Sw23 ∷ []) (sym (c₂ (iI ↑) (Swap))) ▸
       at 4 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (sym (wl0131 c4)) ▸
       at 4 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸ done

  b12 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ []) (Toff034 ∷ Sw01 ∷ [])
  b12 = at 3 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (Toff014 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff024 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Toff034 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 SBOX(2;0;1;4): 3 steps
lem-nat-0-SBOX⟨2·0·1·4⟩ : WsL → ⟪ (Sw01 ∷ Sb2-0-1-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-1-0-4 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨2·0·1·4⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb2-0-1-4 ∷ []) (Sb2-1-0-4 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS01 ∷ []) (refl) ▸
       at 0 2 (CS01 ∷ Sw01 ∷ []) (sym (wl0132 c4)) ▸
       at 0 1 (Sb2-1-0-4 ∷ []) (refl) ▸ done


-- nat 0 SBOXd(2;0;1;4): 3 steps
lem-nat-0-SBOXd⟨2·0·1·4⟩ : WsL → ⟪ (Sw01 ∷ Sb⁻2-0-1-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-1-0-4 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨2·0·1·4⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻2-0-1-4 ∷ []) (Sb⁻2-1-0-4 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS01⁻ ∷ []) (refl) ▸
       at 0 2 (CS01⁻ ∷ Sw01 ∷ []) (sym (wl0133 c4)) ▸
       at 0 1 (Sb⁻2-1-0-4 ∷ []) (refl) ▸ done


-- nat 0 SBOX(2;0;34;1): 7 steps
lem-nat-0-SBOX⟨2·0·34·1⟩ : WsL → ⟪ (Sw01 ∷ Sb2-0-34-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-1-34-0 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨2·0·34·1⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb2-0-34-1 ∷ []) (Sb2-1-34-0 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx2-0341 ∷ Toff134 ∷ Sb2-0-1-4 ∷ Toff134 ∷ Sb⁻2-0-1-4 ∷ []) (refl) ▸
       at 0 2 (Bx2-1340 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·0341⟩ c4) ▸
       at 1 2 (Toff034 ∷ Sw01 ∷ []) (lem-nat-0-TOFF134 c4) ▸
       at 2 2 (Sb2-1-0-4 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·0·1·4⟩ c4) ▸
       at 3 2 (Toff034 ∷ Sw01 ∷ []) (lem-nat-0-TOFF134 c4) ▸
       at 4 2 (Sb⁻2-1-0-4 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨2·0·1·4⟩ c4) ▸
       at 0 5 (Sb2-1-34-0 ∷ []) (refl) ▸ done


-- nat 1 SBOX(0;2;1;4): 3 steps
lem-nat-1-SBOX⟨0·2·1·4⟩ : WsL → ⟪ (Sw12 ∷ Sb0-2-1-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-2-4 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨0·2·1·4⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb0-2-1-4 ∷ []) (Sb0-1-2-4 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS12 ∷ []) (refl) ▸
       at 0 2 (CS12 ∷ Sw12 ∷ []) (sym (wl0134 c4)) ▸
       at 0 1 (Sb0-1-2-4 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(0;2;1;4): 3 steps
lem-nat-1-SBOXd⟨0·2·1·4⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻0-2-1-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-2-4 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨0·2·1·4⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻0-2-1-4 ∷ []) (Sb⁻0-1-2-4 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS12⁻ ∷ []) (refl) ▸
       at 0 2 (CS12⁻ ∷ Sw12 ∷ []) (sym (wl0135 c4)) ▸
       at 0 1 (Sb⁻0-1-2-4 ∷ []) (refl) ▸ done


-- nat 1 SBOX(0;2;34;1): 7 steps
lem-nat-1-SBOX⟨0·2·34·1⟩ : WsL → ⟪ (Sw12 ∷ Sb0-2-34-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-34-2 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨0·2·34·1⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb0-2-34-1 ∷ []) (Sb0-1-34-2 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx0-2341 ∷ Toff134 ∷ Sb0-2-1-4 ∷ Toff134 ∷ Sb⁻0-2-1-4 ∷ []) (refl) ▸
       at 0 2 (Bx0-1342 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2341⟩ c4) ▸
       at 1 2 (Toff234 ∷ Sw12 ∷ []) (wl0136 c4) ▸
       at 2 2 (Sb0-1-2-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·1·4⟩ c4) ▸
       at 3 2 (Toff234 ∷ Sw12 ∷ []) (wl0136 c4) ▸
       at 4 2 (Sb⁻0-1-2-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨0·2·1·4⟩ c4) ▸
       at 0 5 (Sb0-1-34-2 ∷ []) (refl) ▸ done


-- nat 1 BOX(2;10): 3 steps
lem-nat-1-BOX⟨2·10⟩ : WsL → ⟪ (Sw12 ∷ Bx2-10 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-20 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·10⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx2-10 ∷ []) (Bx1-20 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ01 ∷ []) (refl) ▸
       at 0 2 (CZ02 ∷ Sw12 ∷ []) (lem-nat-1-CZ01 c4) ▸
       at 0 1 (Bx1-20 ∷ []) (refl) ▸ done


-- nat 1 BOX(1;240): 8 steps
lem-nat-1-BOX⟨1·240⟩ : WsL → ⟪ (Sw12 ∷ Bx1-240 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-140 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·240⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx1-240 ∷ []) (Bx2-140 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff124 ∷ Bx2-10 ∷ Toff124 ∷ CCZ124 ∷ Bx2-10 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw12 ∷ []) (sym (wl0078 c4)) ▸
       at 1 2 (Toff214 ∷ Sw12 ∷ []) (wl0095 c4) ▸
       at 2 2 (Bx1-20 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·10⟩ c4) ▸
       at 3 2 (Toff214 ∷ Sw12 ∷ []) (wl0095 c4) ▸
       at 4 2 (CCZ124 ∷ Sw12 ∷ []) (sym (wl0078 c4)) ▸
       at 5 2 (Bx1-20 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·10⟩ c4) ▸
       at 0 6 (Bx2-140 ∷ []) (refl) ▸ done


-- nat 1 BOX(2;1340): 8 steps
lem-nat-1-BOX⟨2·1340⟩ : WsL → ⟪ (Sw12 ∷ Bx2-1340 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2340 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·1340⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx2-1340 ∷ []) (Bx1-2340 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff213 ∷ Bx1-240 ∷ Toff213 ∷ CCZ123 ∷ Bx1-240 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw12 ∷ []) (sym (wl0111 c4)) ▸
       at 1 2 (Toff123 ∷ Sw12 ∷ []) (wl0112 c4) ▸
       at 2 2 (Bx2-140 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·240⟩ c4) ▸
       at 3 2 (Toff123 ∷ Sw12 ∷ []) (wl0112 c4) ▸
       at 4 2 (CCZ123 ∷ Sw12 ∷ []) (sym (wl0111 c4)) ▸
       at 5 2 (Bx2-140 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·240⟩ c4) ▸
       at 0 6 (Bx1-2340 ∷ []) (refl) ▸ done

