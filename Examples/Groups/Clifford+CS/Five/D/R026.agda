{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.R026 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Lits using (lw0 ; lw1 ; lw2 ; lw3 ; lw4)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-1-CCZ024 ; lem-nat-2-CCZ013 ; lem-nat-2-TOFF012 ; lem-nat-2-TOFF013 ; lem-nat-2-TOFF103 ; lem-nat-3-TOFF013 ; lem-nat-3-TOFF014)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-3-CCZ013)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-1-TOFF301 ; lem-nat-2-CCZ124 ; lem-nat-2-CCZ134)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-1-BOX⟨2·43⟩ ; lem-nat-2-TOFF413)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-nat-2-TOFF412)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-nat-2-CZ04 ; lem-nat-3-CCZ123 ; lem-nat-3-CCZ124)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-nat-2-CCZ014 ; lem-nat-3-CZ03 ; lem-nat-3-CZ04)
open import Examples.Groups.Clifford+CS.Five.D.R013 using (lem-nat-2-TOFF014)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-nat-0-BOX⟨2·4013⟩ ; lem-nat-1-CS04 ; lem-nat-2-BOX⟨1·02⟩)
open import Examples.Groups.Clifford+CS.Five.D.R015 using (lem-nat-2-TOFF124)
open import Examples.Groups.Clifford+CS.Five.D.R016 using (lem-nat-1-CSd04 ; lem-nat-3-CS04 ; lem-nat-3-CSd04 ; lem-nat-3-TOFF412)
open import Examples.Groups.Clifford+CS.Five.D.R017 using (lem-nat-1-TOFF402 ; lem-nat-2-CS04 ; lem-nat-2-CSd04 ; lem-nat-2-TOFF401 ; lem-nat-3-CS03 ; lem-nat-3-CSd03)
open import Examples.Groups.Clifford+CS.Five.D.R025 using (lem-nat-1-BOX⟨3·40⟩ ; lem-nat-3-BOX⟨1·04⟩)
-- nat 3 BOX(0;134): 8 steps
lem-nat-3-BOX⟨0·134⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx0-134 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-143 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·134⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx0-134 ∷ []) (Bx0-143 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff013 ∷ Bx1-04 ∷ Toff013 ∷ CCZ013 ∷ Bx1-04 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4) ▸
       at 1 2 (Toff014 ∷ Sw34 ∷ []) (lem-nat-3-TOFF013 c4) ▸
       at 2 2 (Bx1-03 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·04⟩ c4) ▸
       at 3 2 (Toff014 ∷ Sw34 ∷ []) (lem-nat-3-TOFF013 c4) ▸
       at 4 2 (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4) ▸
       at 5 2 (Bx1-03 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·04⟩ c4) ▸
       at 0 6 (Bx0-143 ∷ []) (refl) ▸ done


-- nat 3 BOX(1;0234): 8 steps
lem-nat-3-BOX⟨1·0234⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx1-0234 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0243 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨1·0234⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx1-0234 ∷ []) (Bx1-0243 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff102 ∷ Bx0-134 ∷ Toff102 ∷ CCZ012 ∷ Bx0-134 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 1 2 (Toff102 ∷ Sw34 ∷ []) (sym (c₃ (K ↑ • CCZ • K ↑ • iI) (Swap))) ▸
       at 2 2 (Bx0-143 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·134⟩ c4) ▸
       at 3 2 (Toff102 ∷ Sw34 ∷ []) (sym (c₃ (K ↑ • CCZ • K ↑ • iI) (Swap))) ▸
       at 4 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 5 2 (Bx0-143 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·134⟩ c4) ▸
       at 0 6 (Bx1-0243 ∷ []) (refl) ▸ done


-- nat 2 BOX(0;142): 8 steps
lem-nat-2-BOX⟨0·142⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx0-142 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-143 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·142⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-142 ∷ []) (Bx0-143 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff014 ∷ Bx1-02 ∷ Toff014 ∷ CCZ014 ∷ Bx1-02 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 1 2 (Toff014 ∷ Sw23 ∷ []) (lem-nat-2-TOFF014 c4) ▸
       at 2 2 (Bx1-03 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·02⟩ c4) ▸
       at 3 2 (Toff014 ∷ Sw23 ∷ []) (lem-nat-2-TOFF014 c4) ▸
       at 4 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 5 2 (Bx1-03 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·02⟩ c4) ▸
       at 0 6 (Bx0-143 ∷ []) (refl) ▸ done


-- nat 2 BOX(1;0342): 8 steps
lem-nat-2-BOX⟨1·0342⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx1-0342 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0243 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·0342⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx1-0342 ∷ []) (Bx1-0243 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff103 ∷ Bx0-142 ∷ Toff103 ∷ CCZ013 ∷ Bx0-142 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 1 2 (Toff102 ∷ Sw23 ∷ []) (lem-nat-2-TOFF103 c4) ▸
       at 2 2 (Bx0-143 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·142⟩ c4) ▸
       at 3 2 (Toff102 ∷ Sw23 ∷ []) (lem-nat-2-TOFF103 c4) ▸
       at 4 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 5 2 (Bx0-143 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·142⟩ c4) ▸
       at 0 6 (Bx1-0243 ∷ []) (refl) ▸ done


-- resp TOFF034 at 2: 236 steps
lem-resp-TOFF034-at-2 : Complete 4 → ⟪ (Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ Toff134 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-TOFF034-at-2 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (run b29)))))))))))))))))))))))))))))
  where
  b0 : Chain (Toff034 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sw23 ∷ Toff024 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (Sw12 ∷ Toff014 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ Toff013 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ Sw23 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ [])
  b1 = at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 6 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸ done

  b2 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ Sw23 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ []) (Sw23 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ Sw34 ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ [])
  b2 = at 10 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 11 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 2 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 5 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b3 : Chain (Sw23 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ Sw34 ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ []) (Sw23 ∷ K0 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ [])
  b3 = at 6 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 9 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 7 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 9 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 10 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 1 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 2 2 (CS24 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS14 ∷ []) (CS24 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸ done

  b4 : Chain (Sw23 ∷ K0 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ []) (Sw23 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ CS03 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ [])
  b4 = at 5 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS24⁻ ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS14⁻ ∷ []) (CS24⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 7 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 7 2 (CS03 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS03 ∷ []) (CS03 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸ done

  b5 : Chain (Sw23 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ CS03 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ []) (K0 ∷ CS34 ∷ Sw23 ∷ CX02 ∷ Sw23 ∷ Sw23 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ [])
  b5 = at 8 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 6 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 8 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 9 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸
       at 0 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 1 2 (CS34 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS24 ∷ []) (CS34 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸ done

  b6 : Chain (K0 ∷ CS34 ∷ Sw23 ∷ CX02 ∷ Sw23 ∷ Sw23 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ []) (K0 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ [])
  b6 = at 2 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS34⁻ ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS24⁻ ∷ []) (CS34⁻ ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (lw0 c4 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 8 2 (CS01 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸ done

  b7 : Chain (K0 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ []) (K0 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ Sw12 ∷ K0 ∷ ι ∷ Sw12 ∷ [])
  b7 = at 9 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 10 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (lw0 c4 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 7 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 7 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 8 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 (Sw12 ∷ ι ∷ []) (c₁ (iI) (Swap)) ▸
       at 6 2 (Sw12 ∷ K0 ∷ []) (c₁ (K) (Swap)) ▸ done

  b8 : Chain (K0 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ Sw12 ∷ K0 ∷ ι ∷ Sw12 ∷ []) (K0 ∷ CS34 ∷ Sw12 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ [])
  b8 = at 5 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 6 2 (Sw12 ∷ CS03 ∷ []) (lw4 c4 (CS03 ∷ Sw12 ∷ []) (Sw12 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 6 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw12 ∷ CX03 ∷ []) (lw4 c4 (CX03 ∷ Sw12 ∷ []) (Sw12 ∷ CX03 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Sw12 ∷ CS34⁻ ∷ []) (sym (c₃ (Swap ↑) (CS • CS • CS))) ▸
       at 2 2 (Sw12 ∷ CX03 ∷ []) (lw4 c4 (CX03 ∷ Sw12 ∷ []) (Sw12 ∷ CX03 ∷ []) tt tt Eq.refl) ▸ done

  b9 : Chain (K0 ∷ CS34 ∷ Sw12 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ Sw23 ∷ CX03 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ [])
  b9 = at 1 2 (Sw12 ∷ CS34 ∷ []) (sym (c₃ (Swap ↑) (CS))) ▸
       at 0 2 (Sw12 ∷ K0 ∷ []) (c₁ (K) (Swap)) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 3 2 (CS24 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS34 ∷ []) (CS24 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 5 2 (CS24⁻ ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS34⁻ ∷ []) (CS24⁻ ∷ Sw23 ∷ []) tt tt Eq.refl) ▸ done

  b10 : Chain (Sw12 ∷ Sw23 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ Sw23 ∷ CX03 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw12 ∷ [])
  b10 = at 7 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 8 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (lw0 c4 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 10 2 (CS01 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸
       at 11 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 12 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (lw0 c4 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸ done

  b11 : Chain (Sw12 ∷ Sw23 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ Sw12 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw12 ∷ [])
  b11 = at 7 7 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 4 2 (CS14 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS24 ∷ []) (CS14 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done

  b12 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ Sw12 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw12 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw12 ∷ [])
  b12 = at 6 2 (CS14⁻ ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS24⁻ ∷ []) (CS14⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 8 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸
       at 9 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 9 2 (CS03 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS03 ∷ []) (CS03 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 8 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸ done

  b13 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw12 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw34 ∷ Sw34 ∷ CS13⁻ ∷ Sw34 ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ [])
  b13 = at 9 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 10 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 3 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 6 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 8 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b14 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw34 ∷ Sw34 ∷ CS13⁻ ∷ Sw34 ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K0 ∷ Sw23 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ [])
  b14 = at 7 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 8 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 10 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 10 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 11 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸ done

  b15 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K0 ∷ Sw23 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ [])
  b15 = at 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 9 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 9 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done

  b16 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (Sw12 ∷ Toff034 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ [])
  b16 = at 11 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 12 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 5 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 4 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸
       at 3 3 (Toff014 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (Toff024 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff034 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸ done

  b17 : Chain (Sw12 ∷ Toff034 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ [])
  b17 = at 1 1 (Sw23 ∷ Toff024 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw12 ∷ Toff014 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw34 ∷ Toff013 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b18 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ [])
  b18 = at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 7 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 9 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 11 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸ done

  b19 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ [])
  b19 = at 12 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 3 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 6 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 6 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸ done

  b20 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ K0 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ [])
  b20 = at 10 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 8 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 10 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 11 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 2 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 3 2 (CS24 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS14 ∷ []) (CS24 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 6 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸ done

  b21 : Chain (Sw12 ∷ Sw23 ∷ K0 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ [])
  b21 = at 4 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS24⁻ ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS14⁻ ∷ []) (CS24⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 8 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 6 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 8 2 (CS03 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS03 ∷ []) (CS03 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸ done

  b22 : Chain (Sw12 ∷ Sw23 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ K0 ∷ CS34 ∷ CX03 ∷ Sw23 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ [])
  b22 = at 7 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 9 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 10 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸
       at 1 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 2 2 (CS34 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS24 ∷ []) (CS34 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸ done

  b23 : Chain (Sw12 ∷ K0 ∷ CS34 ∷ CX03 ∷ Sw23 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ K0 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Sw34 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ [])
  b23 = at 4 2 (CS34⁻ ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS24⁻ ∷ []) (CS34⁻ ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (lw0 c4 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 9 2 (CS01 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸
       at 10 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸ done

  b24 : Chain (Sw12 ∷ K0 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Sw34 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ K0 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw01 ∷ K1 ∷ ι ∷ Sw01 ∷ Sw12 ∷ [])
  b24 = at 11 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (lw0 c4 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 6 7 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 8 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 9 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 8 2 (Sw01 ∷ ι ∷ []) (lw4 c4 (ι ∷ Sw01 ∷ []) (Sw01 ∷ ι ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Sw01 ∷ K1 ∷ []) (lw4 c4 (K0 ∷ Sw01 ∷ []) (Sw01 ∷ K1 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b25 : Chain (Sw12 ∷ K0 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw01 ∷ K1 ∷ ι ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ K0 ∷ Sw01 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1 ∷ ι ∷ Sw01 ∷ Sw12 ∷ [])
  b25 = at 8 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 7 2 (Sw01 ∷ CS13 ∷ []) (lw4 c4 (CS03 ∷ Sw01 ∷ []) (Sw01 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 7 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw01 ∷ CX13 ∷ []) (lw4 c4 (CX03 ∷ Sw01 ∷ []) (Sw01 ∷ CX13 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Sw01 ∷ CS34⁻ ∷ []) (sym (c₂ (Swap) ((CS • CS • CS) ↑))) ▸
       at 3 2 (Sw01 ∷ CX13 ∷ []) (lw4 c4 (CX03 ∷ Sw01 ∷ []) (Sw01 ∷ CX13 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sw01 ∷ CS34 ∷ []) (sym (c₂ (Swap) (CS ↑))) ▸ done

  b26 : Chain (Sw12 ∷ K0 ∷ Sw01 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1 ∷ ι ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw01 ∷ Sw23 ∷ K1 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ Sw23 ∷ Sw23 ∷ CX12 ∷ Sw23 ∷ CS14 ∷ K1 ∷ ι ∷ Sw01 ∷ Sw12 ∷ [])
  b26 = at 1 2 (Sw01 ∷ K1 ∷ []) (lw4 c4 (K0 ∷ Sw01 ∷ []) (Sw01 ∷ K1 ∷ []) tt tt Eq.refl) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 4 2 (CS24 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS34 ∷ []) (CS24 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 6 2 (CS24⁻ ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS34⁻ ∷ []) (CS24⁻ ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 8 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b27 : Chain (Sw12 ∷ Sw01 ∷ Sw23 ∷ K1 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ Sw23 ∷ Sw23 ∷ CX12 ∷ Sw23 ∷ CS14 ∷ K1 ∷ ι ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw34 ∷ K1 ∷ CS23 ∷ Sw34 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ [])
  b27 = at 7 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 8 2 (CS14 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS14 ∷ []) (CS14 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 10 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 3 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 6 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done

  b28 : Chain (Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw34 ∷ K1 ∷ CS23 ∷ Sw34 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw34 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ [])
  b28 = at 6 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 8 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 8 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 10 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 10 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 11 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸ done

  b29 : Chain (Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw34 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw01 ∷ Toff134 ∷ Sw01 ∷ Sw12 ∷ [])
  b29 = at 4 8 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (lw4 c4 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι ∷ []) (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) tt tt Eq.refl) ▸
       at 4 8 (Toff123 ∷ []) (by-assoc Eq.refl) ▸
       at 3 3 (Toff124 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (Toff134 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp TOFF412 at 3: 7 steps
lem-resp-TOFF412-at-3 : Complete 4 → ⟪ (Toff412 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ Toff423 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-TOFF412-at-3 c4 = run b0
  where
  b0 : Chain (Toff412 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ Toff423 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Toff413 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sw12 ∷ Toff423 ∷ []) (lw0 c4 (Toff413 ∷ Sw12 ∷ []) (Sw12 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sw01 ∷ Toff423 ∷ []) (sym (c₂ (Swap) (Toffᵗ))) ▸ done


-- nat 2 BOX(1;43): 3 steps
lem-nat-2-BOX⟨1·43⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx1-43 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-42 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·43⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx1-43 ∷ []) (Bx1-42 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ34 ∷ []) (refl) ▸
       at 0 2 (CZ24 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CZ34 ∷ []) (CZ24 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Bx1-42 ∷ []) (refl) ▸ done


-- nat 2 BOX(4;103): 8 steps
lem-nat-2-BOX⟨4·103⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx4-103 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-102 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·103⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx4-103 ∷ []) (Bx4-102 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff401 ∷ Bx1-43 ∷ Toff401 ∷ CCZ014 ∷ Bx1-43 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 1 2 (Toff401 ∷ Sw23 ∷ []) (lem-nat-2-TOFF401 c4) ▸
       at 2 2 (Bx1-42 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·43⟩ c4) ▸
       at 3 2 (Toff401 ∷ Sw23 ∷ []) (lem-nat-2-TOFF401 c4) ▸
       at 4 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 5 2 (Bx1-42 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·43⟩ c4) ▸
       at 0 6 (Bx4-102 ∷ []) (refl) ▸ done


-- nat 2 BOX(1;4203): 8 steps
lem-nat-2-BOX⟨1·4203⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx1-4203 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-4302 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·4203⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx1-4203 ∷ []) (Bx1-4302 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff124 ∷ Bx4-103 ∷ Toff124 ∷ CCZ124 ∷ Bx4-103 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 1 2 (Toff134 ∷ Sw23 ∷ []) (lem-nat-2-TOFF124 c4) ▸
       at 2 2 (Bx4-102 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·103⟩ c4) ▸
       at 3 2 (Toff134 ∷ Sw23 ∷ []) (lem-nat-2-TOFF124 c4) ▸
       at 4 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 5 2 (Bx4-102 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·103⟩ c4) ▸
       at 0 6 (Bx1-4302 ∷ []) (refl) ▸ done


-- nat 2 SBOX(1;4;3;0): 3 steps
lem-nat-2-SBOX⟨1·4·3·0⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb1-4-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-4-2-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨1·4·3·0⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb1-4-3-0 ∷ []) (Sb1-4-2-0 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS34 ∷ []) (refl) ▸
       at 0 2 (CS24 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS34 ∷ []) (CS24 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb1-4-2-0 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(1;4;3;0): 3 steps
lem-nat-2-SBOXd⟨1·4·3·0⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb⁻1-4-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-4-2-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨1·4·3·0⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻1-4-3-0 ∷ []) (Sb⁻1-4-2-0 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS34⁻ ∷ []) (refl) ▸
       at 0 2 (CS24⁻ ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS34⁻ ∷ []) (CS24⁻ ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 0 1 (Sb⁻1-4-2-0 ∷ []) (refl) ▸ done


-- nat 2 SBOX(1;4;20;3): 7 steps
lem-nat-2-SBOX⟨1·4·20·3⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb1-4-20-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-4-30-2 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨1·4·20·3⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb1-4-20-3 ∷ []) (Sb1-4-30-2 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx1-4203 ∷ Toff302 ∷ Sb1-4-3-0 ∷ Toff302 ∷ Sb⁻1-4-3-0 ∷ []) (refl) ▸
       at 0 2 (Bx1-4302 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·4203⟩ c4) ▸
       at 1 2 (Toff203 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff302 ∷ []) (Toff203 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb1-4-2-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·4·3·0⟩ c4) ▸
       at 3 2 (Toff203 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ Toff302 ∷ []) (Toff203 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Sb⁻1-4-2-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·4·3·0⟩ c4) ▸
       at 0 5 (Sb1-4-30-2 ∷ []) (refl) ▸ done


-- nat 1 BOX(4;203): 8 steps
lem-nat-1-BOX⟨4·203⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx4-203 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-103 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·203⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx4-203 ∷ []) (Bx4-103 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff402 ∷ Bx2-43 ∷ Toff402 ∷ CCZ024 ∷ Bx2-43 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 1 2 (Toff401 ∷ Sw12 ∷ []) (lem-nat-1-TOFF402 c4) ▸
       at 2 2 (Bx1-43 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·43⟩ c4) ▸
       at 3 2 (Toff401 ∷ Sw12 ∷ []) (lem-nat-1-TOFF402 c4) ▸
       at 4 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 5 2 (Bx1-43 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·43⟩ c4) ▸
       at 0 6 (Bx4-103 ∷ []) (refl) ▸ done


-- nat 1 BOX(2;4103): 8 steps
lem-nat-1-BOX⟨2·4103⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx2-4103 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-4203 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·4103⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx2-4103 ∷ []) (Bx1-4203 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff214 ∷ Bx4-203 ∷ Toff214 ∷ CCZ124 ∷ Bx4-203 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff124 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff214 ∷ []) (Toff124 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx4-103 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·203⟩ c4) ▸
       at 3 2 (Toff124 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff214 ∷ []) (Toff124 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ124 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx4-103 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·203⟩ c4) ▸
       at 0 6 (Bx1-4203 ∷ []) (refl) ▸ done


-- nat 1 SBOX(2;4;3;0): 2 steps
lem-nat-1-SBOX⟨2·4·3·0⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb2-4-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-4-3-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨2·4·3·0⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb2-4-3-0 ∷ []) (Sb1-4-3-0 ∷ Sw12 ∷ [])
  b0 = at 0 2 (Sb2-4-3-0 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS)) ▸
       at 0 1 (Sb1-4-3-0 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 1 SBOXd(2;4;3;0): 2 steps
lem-nat-1-SBOXd⟨2·4·3·0⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb⁻2-4-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-4-3-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨2·4·3·0⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻2-4-3-0 ∷ []) (Sb⁻1-4-3-0 ∷ Sw12 ∷ [])
  b0 = at 0 2 (Sb⁻2-4-3-0 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS • CS • CS)) ▸
       at 0 1 (Sb⁻1-4-3-0 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 1 SBOX(2;4;10;3): 7 steps
lem-nat-1-SBOX⟨2·4·10·3⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb2-4-10-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-4-20-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨2·4·10·3⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb2-4-10-3 ∷ []) (Sb1-4-20-3 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx2-4103 ∷ Toff301 ∷ Sb2-4-3-0 ∷ Toff301 ∷ Sb⁻2-4-3-0 ∷ []) (refl) ▸
       at 0 2 (Bx1-4203 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·4103⟩ c4) ▸
       at 1 2 (Toff302 ∷ Sw12 ∷ []) (lem-nat-1-TOFF301 c4) ▸
       at 2 2 (Sb1-4-3-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·4·3·0⟩ c4) ▸
       at 3 2 (Toff302 ∷ Sw12 ∷ []) (lem-nat-1-TOFF301 c4) ▸
       at 4 2 (Sb⁻1-4-3-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·4·3·0⟩ c4) ▸
       at 0 5 (Sb1-4-20-3 ∷ []) (refl) ▸ done


-- nat 0 SBOX(2;4;3;1): 2 steps
lem-nat-0-SBOX⟨2·4·3·1⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb2-4-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-3-0 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨2·4·3·1⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb2-4-3-1 ∷ []) (Sb2-4-3-0 ∷ Sw01 ∷ [])
  b0 = at 0 2 (Sb2-4-3-1 ∷ Sw01 ∷ []) (c₂ (Swap) (CS ↑)) ▸
       at 0 1 (Sb2-4-3-0 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 SBOXd(2;4;3;1): 2 steps
lem-nat-0-SBOXd⟨2·4·3·1⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb⁻2-4-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-4-3-0 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨2·4·3·1⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb⁻2-4-3-1 ∷ []) (Sb⁻2-4-3-0 ∷ Sw01 ∷ [])
  b0 = at 0 2 (Sb⁻2-4-3-1 ∷ Sw01 ∷ []) (c₂ (Swap) ((CS • CS • CS) ↑)) ▸
       at 0 1 (Sb⁻2-4-3-0 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 SBOX(2;4;01;3): 7 steps
lem-nat-0-SBOX⟨2·4·01·3⟩ : Complete 4 → ⟪ (Sw01 ∷ Sb2-4-01-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-10-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨2·4·01·3⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Sb2-4-01-3 ∷ []) (Sb2-4-10-3 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 0 2 (Bx2-4103 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·4013⟩ c4) ▸
       at 1 2 (Toff301 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff301 ∷ []) (Toff301 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb2-4-3-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·4·3·1⟩ c4) ▸
       at 3 2 (Toff301 ∷ Sw01 ∷ []) (lw4 c4 (Sw01 ∷ Toff301 ∷ []) (Toff301 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Sb⁻2-4-3-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨2·4·3·1⟩ c4) ▸
       at 0 5 (Sb2-4-10-3 ∷ []) (refl) ▸ done


-- nat 1 BOX(4;310): 8 steps
lem-nat-1-BOX⟨4·310⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx4-310 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-320 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·310⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx4-310 ∷ []) (Bx4-320 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff413 ∷ Bx3-40 ∷ Toff413 ∷ CCZ134 ∷ Bx3-40 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ134 ∷ []) (CCZ234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff423 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff413 ∷ []) (Toff423 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx3-40 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·40⟩ c4) ▸
       at 3 2 (Toff423 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff413 ∷ []) (Toff423 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ234 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ134 ∷ []) (CCZ234 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx3-40 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·40⟩ c4) ▸
       at 0 6 (Bx4-320 ∷ []) (refl) ▸ done


-- nat 1 BOX(3;4210): 8 steps
lem-nat-1-BOX⟨3·4210⟩ : Complete 4 → ⟪ (Sw12 ∷ Bx3-4210 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4120 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·4210⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx3-4210 ∷ []) (Bx3-4120 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff324 ∷ Bx4-310 ∷ Toff324 ∷ CCZ234 ∷ Bx4-310 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ234 ∷ []) (CCZ134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff314 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff324 ∷ []) (Toff314 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx4-320 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·310⟩ c4) ▸
       at 3 2 (Toff314 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ Toff324 ∷ []) (Toff314 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ134 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CCZ234 ∷ []) (CCZ134 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx4-320 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·310⟩ c4) ▸
       at 0 6 (Bx3-4120 ∷ []) (refl) ▸ done


-- nat 1 SBOX(3;4;0;1): 3 steps
lem-nat-1-SBOX⟨3·4·0·1⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb3-4-0-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-4-0-2 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨3·4·0·1⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb3-4-0-1 ∷ []) (Sb3-4-0-2 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS04 ∷ []) (refl) ▸
       at 0 2 (CS04 ∷ Sw12 ∷ []) (lem-nat-1-CS04 c4) ▸
       at 0 1 (Sb3-4-0-2 ∷ []) (refl) ▸ done


-- nat 1 SBOXd(3;4;0;1): 3 steps
lem-nat-1-SBOXd⟨3·4·0·1⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb⁻3-4-0-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻3-4-0-2 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨3·4·0·1⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb⁻3-4-0-1 ∷ []) (Sb⁻3-4-0-2 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS04⁻ ∷ []) (refl) ▸
       at 0 2 (CS04⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd04 c4) ▸
       at 0 1 (Sb⁻3-4-0-2 ∷ []) (refl) ▸ done


-- nat 1 SBOX(3;4;21;0): 7 steps
lem-nat-1-SBOX⟨3·4·21·0⟩ : Complete 4 → ⟪ (Sw12 ∷ Sb3-4-21-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-4-12-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨3·4·21·0⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Sb3-4-21-0 ∷ []) (Sb3-4-12-0 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx3-4210 ∷ Toff012 ∷ Sb3-4-0-1 ∷ Toff012 ∷ Sb⁻3-4-0-1 ∷ []) (refl) ▸
       at 0 2 (Bx3-4120 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·4210⟩ c4) ▸
       at 1 2 (Toff012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff012 ∷ []) (Toff012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb3-4-0-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·4·0·1⟩ c4) ▸
       at 3 2 (Toff012 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff012 ∷ []) (Toff012 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Sb⁻3-4-0-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨3·4·0·1⟩ c4) ▸
       at 0 5 (Sb3-4-12-0 ∷ []) (refl) ▸ done


-- nat 2 BOX(2;40): 3 steps
lem-nat-2-BOX⟨2·40⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx2-40 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-40 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·40⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx2-40 ∷ []) (Bx3-40 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ04 ∷ []) (refl) ▸
       at 0 2 (CZ04 ∷ Sw23 ∷ []) (lem-nat-2-CZ04 c4) ▸
       at 0 1 (Bx3-40 ∷ []) (refl) ▸ done


-- nat 2 BOX(4;210): 8 steps
lem-nat-2-BOX⟨4·210⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx4-210 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-310 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·210⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx4-210 ∷ []) (Bx4-310 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff412 ∷ Bx2-40 ∷ Toff412 ∷ CCZ124 ∷ Bx2-40 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 1 2 (Toff413 ∷ Sw23 ∷ []) (lem-nat-2-TOFF412 c4) ▸
       at 2 2 (Bx3-40 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·40⟩ c4) ▸
       at 3 2 (Toff413 ∷ Sw23 ∷ []) (lem-nat-2-TOFF412 c4) ▸
       at 4 2 (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4) ▸
       at 5 2 (Bx3-40 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·40⟩ c4) ▸
       at 0 6 (Bx4-310 ∷ []) (refl) ▸ done


-- nat 2 BOX(2;4310): 8 steps
lem-nat-2-BOX⟨2·4310⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx2-4310 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4210 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·4310⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx2-4310 ∷ []) (Bx3-4210 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff234 ∷ Bx4-210 ∷ Toff234 ∷ CCZ234 ∷ Bx4-210 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff324 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ Toff234 ∷ []) (Toff324 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx4-310 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·210⟩ c4) ▸
       at 3 2 (Toff324 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ Toff234 ∷ []) (Toff324 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ234 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx4-310 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·210⟩ c4) ▸
       at 0 6 (Bx3-4210 ∷ []) (refl) ▸ done


-- nat 2 SBOX(2;4;0;1): 3 steps
lem-nat-2-SBOX⟨2·4·0·1⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb2-4-0-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-4-0-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨2·4·0·1⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb2-4-0-1 ∷ []) (Sb3-4-0-1 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS04 ∷ []) (refl) ▸
       at 0 2 (CS04 ∷ Sw23 ∷ []) (lem-nat-2-CS04 c4) ▸
       at 0 1 (Sb3-4-0-1 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(2;4;0;1): 3 steps
lem-nat-2-SBOXd⟨2·4·0·1⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb⁻2-4-0-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻3-4-0-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨2·4·0·1⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻2-4-0-1 ∷ []) (Sb⁻3-4-0-1 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS04⁻ ∷ []) (refl) ▸
       at 0 2 (CS04⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd04 c4) ▸
       at 0 1 (Sb⁻3-4-0-1 ∷ []) (refl) ▸ done


-- nat 2 SBOX(2;4;31;0): 7 steps
lem-nat-2-SBOX⟨2·4·31·0⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb2-4-31-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-4-21-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨2·4·31·0⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb2-4-31-0 ∷ []) (Sb3-4-21-0 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx2-4310 ∷ Toff013 ∷ Sb2-4-0-1 ∷ Toff013 ∷ Sb⁻2-4-0-1 ∷ []) (refl) ▸
       at 0 2 (Bx3-4210 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·4310⟩ c4) ▸
       at 1 2 (Toff012 ∷ Sw23 ∷ []) (lem-nat-2-TOFF013 c4) ▸
       at 2 2 (Sb3-4-0-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨2·4·0·1⟩ c4) ▸
       at 3 2 (Toff012 ∷ Sw23 ∷ []) (lem-nat-2-TOFF013 c4) ▸
       at 4 2 (Sb⁻3-4-0-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨2·4·0·1⟩ c4) ▸
       at 0 5 (Sb3-4-21-0 ∷ []) (refl) ▸ done


-- nat 2 BOX(3;40): 3 steps
lem-nat-2-BOX⟨3·40⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx3-40 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-40 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·40⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx3-40 ∷ []) (Bx2-40 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ04 ∷ []) (refl) ▸
       at 0 2 (CZ04 ∷ Sw23 ∷ []) (lem-nat-2-CZ04 c4) ▸
       at 0 1 (Bx2-40 ∷ []) (refl) ▸ done


-- nat 2 BOX(4;310): 8 steps
lem-nat-2-BOX⟨4·310⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx4-310 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-210 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·310⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx4-310 ∷ []) (Bx4-210 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff413 ∷ Bx3-40 ∷ Toff413 ∷ CCZ134 ∷ Bx3-40 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 1 2 (Toff412 ∷ Sw23 ∷ []) (lem-nat-2-TOFF413 c4) ▸
       at 2 2 (Bx2-40 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·40⟩ c4) ▸
       at 3 2 (Toff412 ∷ Sw23 ∷ []) (lem-nat-2-TOFF413 c4) ▸
       at 4 2 (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4) ▸
       at 5 2 (Bx2-40 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·40⟩ c4) ▸
       at 0 6 (Bx4-210 ∷ []) (refl) ▸ done


-- nat 2 BOX(3;4210): 8 steps
lem-nat-2-BOX⟨3·4210⟩ : Complete 4 → ⟪ (Sw23 ∷ Bx3-4210 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4310 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·4210⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx3-4210 ∷ []) (Bx2-4310 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff324 ∷ Bx4-310 ∷ Toff324 ∷ CCZ234 ∷ Bx4-310 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff234 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ Toff324 ∷ []) (Toff234 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx4-210 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·310⟩ c4) ▸
       at 3 2 (Toff234 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ Toff324 ∷ []) (Toff234 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ234 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx4-210 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·310⟩ c4) ▸
       at 0 6 (Bx2-4310 ∷ []) (refl) ▸ done


-- nat 2 SBOX(3;4;0;1): 3 steps
lem-nat-2-SBOX⟨3·4·0·1⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb3-4-0-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-0-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨3·4·0·1⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb3-4-0-1 ∷ []) (Sb2-4-0-1 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS04 ∷ []) (refl) ▸
       at 0 2 (CS04 ∷ Sw23 ∷ []) (lem-nat-2-CS04 c4) ▸
       at 0 1 (Sb2-4-0-1 ∷ []) (refl) ▸ done


-- nat 2 SBOXd(3;4;0;1): 3 steps
lem-nat-2-SBOXd⟨3·4·0·1⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb⁻3-4-0-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-4-0-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨3·4·0·1⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb⁻3-4-0-1 ∷ []) (Sb⁻2-4-0-1 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS04⁻ ∷ []) (refl) ▸
       at 0 2 (CS04⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd04 c4) ▸
       at 0 1 (Sb⁻2-4-0-1 ∷ []) (refl) ▸ done


-- nat 2 SBOX(3;4;21;0): 7 steps
lem-nat-2-SBOX⟨3·4·21·0⟩ : Complete 4 → ⟪ (Sw23 ∷ Sb3-4-21-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-31-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨3·4·21·0⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb3-4-21-0 ∷ []) (Sb2-4-31-0 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx3-4210 ∷ Toff012 ∷ Sb3-4-0-1 ∷ Toff012 ∷ Sb⁻3-4-0-1 ∷ []) (refl) ▸
       at 0 2 (Bx2-4310 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·4210⟩ c4) ▸
       at 1 2 (Toff013 ∷ Sw23 ∷ []) (lem-nat-2-TOFF012 c4) ▸
       at 2 2 (Sb2-4-0-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·4·0·1⟩ c4) ▸
       at 3 2 (Toff013 ∷ Sw23 ∷ []) (lem-nat-2-TOFF012 c4) ▸
       at 4 2 (Sb⁻2-4-0-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨3·4·0·1⟩ c4) ▸
       at 0 5 (Sb2-4-31-0 ∷ []) (refl) ▸ done


-- nat 3 TOFF312: 2 steps
lem-nat-3-TOFF312 : Complete 4 → ⟪ (Sw34 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-TOFF312 c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Toff312 ∷ []) (Toff412 ∷ Sw34 ∷ [])
  b0 = at 2 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Toff412 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 3 BOX(2;30): 3 steps
lem-nat-3-BOX⟨2·30⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx2-30 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-40 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨2·30⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx2-30 ∷ []) (Bx2-40 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CZ03 ∷ []) (refl) ▸
       at 0 2 (CZ04 ∷ Sw34 ∷ []) (lem-nat-3-CZ03 c4) ▸
       at 0 1 (Bx2-40 ∷ []) (refl) ▸ done


-- nat 3 BOX(3;210): 8 steps
lem-nat-3-BOX⟨3·210⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx3-210 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-210 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨3·210⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx3-210 ∷ []) (Bx4-210 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff312 ∷ Bx2-30 ∷ Toff312 ∷ CCZ123 ∷ Bx2-30 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw34 ∷ []) (lem-nat-3-CCZ123 c4) ▸
       at 1 2 (Toff412 ∷ Sw34 ∷ []) (lem-nat-3-TOFF312 c4) ▸
       at 2 2 (Bx2-40 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·30⟩ c4) ▸
       at 3 2 (Toff412 ∷ Sw34 ∷ []) (lem-nat-3-TOFF312 c4) ▸
       at 4 2 (CCZ124 ∷ Sw34 ∷ []) (lem-nat-3-CCZ123 c4) ▸
       at 5 2 (Bx2-40 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·30⟩ c4) ▸
       at 0 6 (Bx4-210 ∷ []) (refl) ▸ done


-- nat 3 BOX(2;3410): 8 steps
lem-nat-3-BOX⟨2·3410⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx2-3410 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4310 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨2·3410⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx2-3410 ∷ []) (Bx2-4310 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff234 ∷ Bx3-210 ∷ Toff234 ∷ CCZ234 ∷ Bx3-210 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff234 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ Toff234 ∷ []) (Toff234 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx4-210 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·210⟩ c4) ▸
       at 3 2 (Toff234 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ Toff234 ∷ []) (Toff234 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ234 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx4-210 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·210⟩ c4) ▸
       at 0 6 (Bx2-4310 ∷ []) (refl) ▸ done


-- nat 3 SBOX(2;3;0;1): 3 steps
lem-nat-3-SBOX⟨2·3·0·1⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb2-3-0-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-0-1 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨2·3·0·1⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb2-3-0-1 ∷ []) (Sb2-4-0-1 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS03 ∷ []) (refl) ▸
       at 0 2 (CS04 ∷ Sw34 ∷ []) (lem-nat-3-CS03 c4) ▸
       at 0 1 (Sb2-4-0-1 ∷ []) (refl) ▸ done


-- nat 3 SBOXd(2;3;0;1): 3 steps
lem-nat-3-SBOXd⟨2·3·0·1⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb⁻2-3-0-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-4-0-1 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨2·3·0·1⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb⁻2-3-0-1 ∷ []) (Sb⁻2-4-0-1 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS03⁻ ∷ []) (refl) ▸
       at 0 2 (CS04⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd03 c4) ▸
       at 0 1 (Sb⁻2-4-0-1 ∷ []) (refl) ▸ done


-- nat 3 SBOX(2;3;41;0): 7 steps
lem-nat-3-SBOX⟨2·3·41·0⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb2-3-41-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-31-0 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨2·3·41·0⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb2-3-41-0 ∷ []) (Sb2-4-31-0 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx2-3410 ∷ Toff014 ∷ Sb2-3-0-1 ∷ Toff014 ∷ Sb⁻2-3-0-1 ∷ []) (refl) ▸
       at 0 2 (Bx2-4310 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·3410⟩ c4) ▸
       at 1 2 (Toff013 ∷ Sw34 ∷ []) (lem-nat-3-TOFF014 c4) ▸
       at 2 2 (Sb2-4-0-1 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨2·3·0·1⟩ c4) ▸
       at 3 2 (Toff013 ∷ Sw34 ∷ []) (lem-nat-3-TOFF014 c4) ▸
       at 4 2 (Sb⁻2-4-0-1 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨2·3·0·1⟩ c4) ▸
       at 0 5 (Sb2-4-31-0 ∷ []) (refl) ▸ done


-- nat 3 BOX(2;40): 3 steps
lem-nat-3-BOX⟨2·40⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx2-40 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-30 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨2·40⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx2-40 ∷ []) (Bx2-30 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CZ04 ∷ []) (refl) ▸
       at 0 2 (CZ03 ∷ Sw34 ∷ []) (lem-nat-3-CZ04 c4) ▸
       at 0 1 (Bx2-30 ∷ []) (refl) ▸ done


-- nat 3 BOX(4;210): 8 steps
lem-nat-3-BOX⟨4·210⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx4-210 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-210 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨4·210⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx4-210 ∷ []) (Bx3-210 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff412 ∷ Bx2-40 ∷ Toff412 ∷ CCZ124 ∷ Bx2-40 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw34 ∷ []) (lem-nat-3-CCZ124 c4) ▸
       at 1 2 (Toff312 ∷ Sw34 ∷ []) (lem-nat-3-TOFF412 c4) ▸
       at 2 2 (Bx2-30 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·40⟩ c4) ▸
       at 3 2 (Toff312 ∷ Sw34 ∷ []) (lem-nat-3-TOFF412 c4) ▸
       at 4 2 (CCZ123 ∷ Sw34 ∷ []) (lem-nat-3-CCZ124 c4) ▸
       at 5 2 (Bx2-30 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·40⟩ c4) ▸
       at 0 6 (Bx3-210 ∷ []) (refl) ▸ done


-- nat 3 BOX(2;4310): 8 steps
lem-nat-3-BOX⟨2·4310⟩ : Complete 4 → ⟪ (Sw34 ∷ Bx2-4310 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3410 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨2·4310⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx2-4310 ∷ []) (Bx2-3410 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff234 ∷ Bx4-210 ∷ Toff234 ∷ CCZ234 ∷ Bx4-210 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff234 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ Toff234 ∷ []) (Toff234 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Bx3-210 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·210⟩ c4) ▸
       at 3 2 (Toff234 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ Toff234 ∷ []) (Toff234 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ234 ∷ Sw34 ∷ []) (lw0 c4 (Sw34 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Bx3-210 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·210⟩ c4) ▸
       at 0 6 (Bx2-3410 ∷ []) (refl) ▸ done


-- nat 3 SBOX(2;4;0;1): 3 steps
lem-nat-3-SBOX⟨2·4·0·1⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb2-4-0-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-3-0-1 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨2·4·0·1⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb2-4-0-1 ∷ []) (Sb2-3-0-1 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS04 ∷ []) (refl) ▸
       at 0 2 (CS03 ∷ Sw34 ∷ []) (lem-nat-3-CS04 c4) ▸
       at 0 1 (Sb2-3-0-1 ∷ []) (refl) ▸ done


-- nat 3 SBOXd(2;4;0;1): 3 steps
lem-nat-3-SBOXd⟨2·4·0·1⟩ : Complete 4 → ⟪ (Sw34 ∷ Sb⁻2-4-0-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-3-0-1 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨2·4·0·1⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb⁻2-4-0-1 ∷ []) (Sb⁻2-3-0-1 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CS04⁻ ∷ []) (refl) ▸
       at 0 2 (CS03⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd04 c4) ▸
       at 0 1 (Sb⁻2-3-0-1 ∷ []) (refl) ▸ done

