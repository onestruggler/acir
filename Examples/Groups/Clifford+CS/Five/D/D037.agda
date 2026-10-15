{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D037 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Lits using (lw0 ; lw1 ; lw2 ; lw3 ; lw4)
open import Examples.Groups.Clifford+CS.Five.Resps using (pw0 ; pw1 ; pw2 ; pw3 ; pw4)
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-box-cP-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D026 using (lem-CSdu-box-2-at0210243143 ; lem-Su-box-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D031 using (lem-box-cP-at0210233441 ; lem-box-perm-1423-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D036 using (lem-P-box-at14233241 ; lem-box-cP-at14233241 ; lem-sym-ab-at122441 ; lem-sym-bc-at1441)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CSd12-TOFF034 ; lem-comm-CZ12-CCZ034)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-comm-CX21-CCZ034)
open import Examples.Groups.Clifford+CS.Five.D.R016 using (lem-comm-CCZ023-CK41 ; lem-comm-TOFF213-CK40 ; lem-comm-TOFF213-CSd04)
-- cQ @12213443: 7 steps
lem-cQ-at12213443 : Complete 4 → ⟪ (CCZ012 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ CCZ012 ∷ []) ⟫ʷ
lem-cQ-at12213443 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ012 ∷ [])
  b0 = at 0 1 (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ034 ∷ CS02 ∷ []) (pw1 c4 (CS02 ∷ CCZ034 ∷ []) (CCZ034 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ034 ∷ CX21 ∷ []) (lem-comm-CX21-CCZ034 c4) ▸
       at 2 2 (CCZ034 ∷ CS01⁻ ∷ []) (pw2 c4 (CS01⁻ ∷ CCZ034 ∷ []) (CCZ034 ∷ CS01⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ034 ∷ CX21 ∷ []) (lem-comm-CX21-CCZ034 c4) ▸
       at 0 2 (CCZ034 ∷ CS01 ∷ []) (pw2 c4 (CS01 ∷ CCZ034 ∷ []) (CCZ034 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 1 5 (CCZ012 ∷ []) (lw4 c4 (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸ done


-- box-tQ @12213443: 13 steps
lem-box-tQ-at12213443 : Complete 4 → ⟪ (Bx0-2143 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) ⟫ʷ
lem-box-tQ-at12213443 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-2143 ∷ []) (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ024 ∷ Toff204 ∷ CZ23 ∷ Toff204 ∷ CCZ024 ∷ CZ23 ∷ [])
  b0 = at 0 1 (CCZ012 ∷ Toff012 ∷ Bx2-043 ∷ Toff012 ∷ CCZ012 ∷ Bx2-043 ∷ []) (refl) ▸
       at 2 1 (CCZ024 ∷ Toff204 ∷ Bx0-23 ∷ Toff204 ∷ CCZ024 ∷ Bx0-23 ∷ []) (refl) ▸
       at 4 1 (CZ23 ∷ []) (refl) ▸
       at 7 1 (CZ23 ∷ []) (refl) ▸
       at 2 6 (CCZ034 ∷ []) (pw1 c4 (CCZ024 ∷ Toff204 ∷ CZ23 ∷ Toff204 ∷ CCZ024 ∷ CZ23 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ024 ∷ Toff204 ∷ Bx0-23 ∷ Toff204 ∷ CCZ024 ∷ Bx0-23 ∷ []) (refl) ▸
       at 7 1 (CZ23 ∷ []) (refl) ▸
       at 10 1 (CZ23 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ024 ∷ Toff204 ∷ CZ23 ∷ Toff204 ∷ CCZ024 ∷ CZ23 ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ [])
  b1 = at 5 6 (CCZ034 ∷ []) (pw1 c4 (CCZ024 ∷ Toff204 ∷ CZ23 ∷ Toff204 ∷ CCZ024 ∷ CZ23 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Toff012 ∷ CCZ012 ∷ CZ12 ∷ []) (lw4 c4 (CCZ012 ∷ Toff012 ∷ []) (Toff012 ∷ CCZ012 ∷ CZ12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ034 ∷ CZ12 ∷ []) (lem-comm-CZ12-CCZ034 c4) ▸
       at 1 2 (CCZ034 ∷ CCZ012 ∷ []) (lem-cQ-at12213443 c4) ▸
       at 2 4 (Toff012 ∷ []) (lw4 c4 (CCZ012 ∷ CZ12 ∷ Toff012 ∷ CCZ012 ∷ []) (Toff012 ∷ []) tt tt Eq.refl) ▸ done


-- pairs @14233241: 4 steps
lem-pairs-at14233241 : Complete 4 → ⟪ (Bx0-4321 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2143 ∷ []) ⟫ʷ
lem-pairs-at14233241 c4 = run b0
  where
  b0 : Chain (Bx0-4321 ∷ []) (Bx0-2143 ∷ [])
  b0 = at 0 1 (Toff012 ∷ Bx0-4321 ∷ Toff012 ∷ []) (sym (lem-P-box-at14233241 c4)) ▸
       at 1 1 (CCZ034 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ []) (lem-box-cP-at14233241 c4) ▸
       at 4 2 [] (lw4 c4 (Toff012 ∷ Toff012 ∷ []) [] tt tt Eq.refl) ▸
       at 0 4 (Bx0-2143 ∷ []) (sym (lem-box-tQ-at12213443 c4)) ▸ done


-- box-perm-1423 @122441: 3 steps
lem-box-perm-1423-at122441 : Complete 4 → ⟪ (Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2143 ∷ []) ⟫ʷ
lem-box-perm-1423-at122441 c4 = run b0
  where
  b0 : Chain (Bx0-2431 ∷ []) (Bx0-2143 ∷ [])
  b0 = at 0 1 (Bx0-4231 ∷ []) (lem-sym-ab-at122441 c4) ▸
       at 0 1 (Bx0-4321 ∷ []) (lem-sym-bc-at1441 c4) ▸
       at 0 1 (Bx0-2143 ∷ []) (lem-pairs-at14233241 c4) ▸ done


-- tP @12213443: 7 steps
lem-tP-at12213443 : Complete 4 → ⟪ (Toff012 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ Toff012 ∷ []) ⟫ʷ
lem-tP-at12213443 c4 = run b0
  where
  b0 : Chain (Toff012 ∷ Toff034 ∷ []) (Toff034 ∷ Toff012 ∷ [])
  b0 = at 0 1 (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (lw4 c4 (Toff012 ∷ []) (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 1 (K0 ∷ CCZ034 ∷ K0⁻ ∷ []) (pw1 c4 (Toff034 ∷ []) (K0 ∷ CCZ034 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (K0⁻ ∷ K0 ∷ []) [] tt tt Eq.refl) ▸
       at 1 2 (CCZ034 ∷ CCZ012 ∷ []) (lem-cQ-at12213443 c4) ▸
       at 2 0 (K0⁻ ∷ K0 ∷ []) (lw4 c4 [] (K0⁻ ∷ K0 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Toff034 ∷ []) (pw1 c4 (K0 ∷ CCZ034 ∷ K0⁻ ∷ []) (Toff034 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Toff012 ∷ []) (lw4 c4 (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (Toff012 ∷ []) tt tt Eq.refl) ▸ done


-- VPQ @12213443: 14 steps
lem-VPQ-at12213443 : Complete 4 → ⟪ (Toff012 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ []) ⟫ʷ
lem-VPQ-at12213443 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff012 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ []) (CS34⁻ ∷ CS12⁻ ∷ S0 ∷ Toff034 ∷ Toff012 ∷ S0⁻ ∷ [])
  b0 = at 0 2 (CS12⁻ ∷ S0 ∷ Toff012 ∷ S0⁻ ∷ []) (lw4 c4 (Toff012 ∷ CCZ012 ∷ []) (CS12⁻ ∷ S0 ∷ Toff012 ∷ S0⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CS34⁻ ∷ S0 ∷ Toff034 ∷ S0⁻ ∷ []) (pw1 c4 (Toff034 ∷ CCZ034 ∷ []) (CS34⁻ ∷ S0 ∷ Toff034 ∷ S0⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CS34⁻ ∷ S0⁻ ∷ []) (c₁ (S • S • S) ((CS • CS • CS) ↑ ↑)) ▸
       at 2 2 (CS34⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (CS • CS • CS)) ▸
       at 1 2 (CS34⁻ ∷ S0 ∷ []) (c₁ (S) ((CS • CS • CS) ↑ ↑)) ▸
       at 0 2 (CS34⁻ ∷ CS12⁻ ∷ []) (c₃ ((CS • CS • CS) ↑) (CS • CS • CS)) ▸
       at 4 2 [] (lw4 c4 (S0⁻ ∷ S0 ∷ []) [] tt tt Eq.refl) ▸
       at 3 2 (Toff034 ∷ Toff012 ∷ []) (lem-tP-at12213443 c4) ▸ done

  b1 : Chain (CS34⁻ ∷ CS12⁻ ∷ S0 ∷ Toff034 ∷ Toff012 ∷ S0⁻ ∷ []) (Toff034 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ [])
  b1 = at 4 0 (S0⁻ ∷ S0 ∷ []) (lw4 c4 [] (S0⁻ ∷ S0 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (S0 ∷ CS12⁻ ∷ []) (sym (c₁ (S) (CS • CS • CS))) ▸
       at 2 2 (Toff034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-TOFF034 c4) ▸
       at 3 2 (S0⁻ ∷ CS12⁻ ∷ []) (sym (c₁ (S • S • S) (CS • CS • CS))) ▸
       at 0 4 (Toff034 ∷ CCZ034 ∷ []) (pw1 c4 (CS34⁻ ∷ S0 ∷ Toff034 ∷ S0⁻ ∷ []) (Toff034 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Toff012 ∷ CCZ012 ∷ []) (lw4 c4 (CS12⁻ ∷ S0 ∷ Toff012 ∷ S0⁻ ∷ []) (Toff012 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸ done


-- QVQ @12213443: 3 steps
lem-QVQ-at12213443 : Complete 4 → ⟪ (CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ Toff012 ∷ CCZ012 ∷ Toff034 ∷ []) ⟫ʷ
lem-QVQ-at12213443 c4 = run b0
  where
  b0 : Chain (CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) (Toff034 ∷ Toff012 ∷ CCZ012 ∷ Toff034 ∷ [])
  b0 = at 0 0 (Toff034 ∷ Toff034 ∷ []) (pw1 c4 [] (Toff034 ∷ Toff034 ∷ []) tt tt Eq.refl) ▸
       at 1 4 (Toff012 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ []) (sym (lem-VPQ-at12213443 c4)) ▸
       at 4 2 [] (pw1 c4 (CCZ034 ∷ CCZ034 ∷ []) [] tt tt Eq.refl) ▸ done


-- box-cP @12213443: 12 steps
lem-box-cP-at12213443 : Complete 4 → ⟪ (Bx0-2143 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ []) ⟫ʷ
lem-box-cP-at12213443 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-2143 ∷ []) (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ024 ∷ Toff204 ∷ CZ23 ∷ Toff204 ∷ CCZ024 ∷ CZ23 ∷ [])
  b0 = at 0 1 (CCZ012 ∷ Toff012 ∷ Bx2-043 ∷ Toff012 ∷ CCZ012 ∷ Bx2-043 ∷ []) (refl) ▸
       at 2 1 (CCZ024 ∷ Toff204 ∷ Bx0-23 ∷ Toff204 ∷ CCZ024 ∷ Bx0-23 ∷ []) (refl) ▸
       at 4 1 (CZ23 ∷ []) (refl) ▸
       at 7 1 (CZ23 ∷ []) (refl) ▸
       at 2 6 (CCZ034 ∷ []) (pw1 c4 (CCZ024 ∷ Toff204 ∷ CZ23 ∷ Toff204 ∷ CCZ024 ∷ CZ23 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ024 ∷ Toff204 ∷ Bx0-23 ∷ Toff204 ∷ CCZ024 ∷ Bx0-23 ∷ []) (refl) ▸
       at 7 1 (CZ23 ∷ []) (refl) ▸
       at 10 1 (CZ23 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ024 ∷ Toff204 ∷ CZ23 ∷ Toff204 ∷ CCZ024 ∷ CZ23 ∷ []) (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ [])
  b1 = at 5 6 (CCZ034 ∷ []) (pw1 c4 (CCZ024 ∷ Toff204 ∷ CZ23 ∷ Toff204 ∷ CCZ024 ∷ CZ23 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Toff034 ∷ Toff012 ∷ CCZ012 ∷ Toff034 ∷ []) (lem-QVQ-at12213443 c4) ▸
       at 1 2 (Toff034 ∷ Toff012 ∷ []) (lem-tP-at12213443 c4) ▸
       at 2 2 [] (lw4 c4 (Toff012 ∷ Toff012 ∷ []) [] tt tt Eq.refl) ▸ done


-- F4-K3-CS2: 19 steps
lem-F4-K3-CS2 : Complete 4 → ⟪ (X4 ∷ CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K3-CS2 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ CK43 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (CCZ012 ∷ X4 ∷ CK43 ∷ X4 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b0 = at 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 5 1 (CS12 ∷ []) (refl) ▸
       at 7 1 (CS12⁻ ∷ []) (refl) ▸
       at 3 1 (Bx0-2143 ∷ []) (lem-box-perm-1423-at122441 c4) ▸
       at 3 1 (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ []) (lem-box-cP-at12213443 c4) ▸
       at 2 2 (CCZ012 ∷ X4 ∷ []) (sym (c₃ (CCZ) (X ↑))) ▸
       at 1 2 (CCZ012 ∷ CK43 ∷ []) (sym (c₃ (CCZ) (CK₁₀))) ▸
       at 0 2 (CCZ012 ∷ X4 ∷ []) (sym (c₃ (CCZ) (X ↑))) ▸ done

  b1 : Chain (CCZ012 ∷ X4 ∷ CK43 ∷ X4 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  b1 = at 1 4 (Toff034 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CK43 ∷ X4 ∷ Toff034 ∷ []) (Toff034 ∷ X4 ∷ CK43 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ012 ∷ X4 ∷ []) (sym (c₃ (CCZ) (X ↑))) ▸
       at 3 2 (CCZ012 ∷ CK43 ∷ []) (sym (c₃ (CCZ) (CK₁₀))) ▸
       at 2 2 (CCZ012 ∷ X4 ∷ []) (sym (c₃ (CCZ) (X ↑))) ▸
       at 3 4 (Toff034 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CK43 ∷ X4 ∷ Toff034 ∷ []) (Toff034 ∷ X4 ∷ CK43 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx0-2143 ∷ []) (sym (lem-box-cP-at12213443 c4)) ▸
       at 0 1 (Bx0-2431 ∷ []) (sym (lem-box-perm-1423-at122441 c4)) ▸
       at 1 7 (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CK43 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK43 ∷ X4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CK43 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CK43 ∷ X4 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CK43 ∷ X4 ∷ [])
  b2 = at 2 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 0 5 (Sb0-2-43-1 ∷ []) (refl) ▸ done


-- F4-CS0-I: 19 steps
lem-F4-CS0-I : Complete 4 → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS0-I c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ []) (X4 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ ι1 ∷ S4⁻ ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ [])
  b0 = at 2 2 (ι ∷ S4⁻ ∷ X4 ∷ []) (lw1 c4 (X4 ∷ S4 ∷ []) (ι ∷ S4⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 1 (CS03 ∷ []) (refl) ▸
       at 5 1 (CS03⁻ ∷ []) (refl) ▸
       at 2 6 (ι ∷ S4⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (pw2 c4 (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ ι ∷ S4⁻ ∷ []) (ι ∷ S4⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 5 1 (ι1 ∷ []) (uₛ (iI) (iI ↑) Eq.refl) ▸
       at 4 3 (ι1 ∷ S4⁻ ∷ Toff213 ∷ []) (pw0 c4 (Toff213 ∷ ι1 ∷ S4⁻ ∷ []) (ι1 ∷ S4⁻ ∷ Toff213 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (X4 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ ι1 ∷ S4⁻ ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ []) (X4 ∷ ι ∷ S4⁻ ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ [])
  b1 = at 4 1 (ι ∷ []) (uₛ (iI ↑) (iI) Eq.refl) ▸
       at 3 3 (ι ∷ S4⁻ ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ ι ∷ S4⁻ ∷ []) (ι ∷ S4⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (ι1 ∷ []) (uₛ (iI) (iI ↑) Eq.refl) ▸
       at 2 3 (ι1 ∷ S4⁻ ∷ Toff213 ∷ []) (pw0 c4 (Toff213 ∷ ι1 ∷ S4⁻ ∷ []) (ι1 ∷ S4⁻ ∷ Toff213 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (ι ∷ []) (uₛ (iI ↑) (iI) Eq.refl) ▸
       at 1 3 (ι ∷ S4⁻ ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ ι ∷ S4⁻ ∷ []) (ι ∷ S4⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 3 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 5 1 (Sb2-0-3-1 ∷ []) (refl) ▸ done

  b2 : Chain (X4 ∷ ι ∷ S4⁻ ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ []) (S4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  b2 = at 7 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 0 3 (S4 ∷ X4 ∷ []) (lw1 c4 (X4 ∷ ι ∷ S4⁻ ∷ []) (S4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-CS0-S0: 17 steps
lem-F4-CS0-S0 : Complete 4 → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS0-S0 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ []) (X4 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ S0 ∷ CS04⁻ ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ [])
  b0 = at 2 2 (S0 ∷ CS04⁻ ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS04 ∷ []) (S0 ∷ CS04⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 1 (CS03 ∷ []) (refl) ▸
       at 5 1 (CS03⁻ ∷ []) (refl) ▸
       at 2 6 (S0 ∷ CS04⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (pw2 c4 (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ S0 ∷ CS04⁻ ∷ []) (S0 ∷ CS04⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 4 2 (S0 ∷ Toff213 ∷ []) (sym (c₁ (S) (K ↑ • CCZ • K ↑ • iI))) ▸
       at 5 2 (CS04⁻ ∷ Toff213 ∷ []) (lem-comm-TOFF213-CSd04 c4) ▸ done

  b1 : Chain (X4 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ S0 ∷ CS04⁻ ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ []) (X4 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  b1 = at 3 3 (S0 ∷ CS04⁻ ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ S0 ∷ CS04⁻ ∷ []) (S0 ∷ CS04⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (S0 ∷ Toff213 ∷ []) (sym (c₁ (S) (K ↑ • CCZ • K ↑ • iI))) ▸
       at 3 2 (CS04⁻ ∷ Toff213 ∷ []) (lem-comm-TOFF213-CSd04 c4) ▸
       at 1 3 (S0 ∷ CS04⁻ ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ S0 ∷ CS04⁻ ∷ []) (S0 ∷ CS04⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 3 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 5 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 7 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 5 (Sb2-0-41-3 ∷ []) (refl) ▸ done

  b2 : Chain (X4 ∷ S0 ∷ CS04⁻ ∷ Sb2-0-41-3 ∷ X4 ∷ []) (CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  b2 = at 0 3 (CS04 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ S0 ∷ CS04⁻ ∷ []) (CS04 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-CS0-S1: 15 steps
lem-F4-CS0-S1 : Complete 4 → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS0-S1 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ []) (X4 ∷ CCZ024 ∷ Toff213 ∷ S1 ∷ CS14⁻ ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ [])
  b0 = at 2 2 (S1 ∷ CS14⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS14 ∷ []) (S1 ∷ CS14⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 1 (CS03 ∷ []) (refl) ▸
       at 5 1 (CS03⁻ ∷ []) (refl) ▸
       at 2 6 (S1 ∷ CS14⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (pw2 c4 (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ S1 ∷ CS14⁻ ∷ []) (S1 ∷ CS14⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 4 3 (S1 ∷ CS14⁻ ∷ Toff213 ∷ []) (lw0 c4 (Toff213 ∷ S1 ∷ CS14⁻ ∷ []) (S1 ∷ CS14⁻ ∷ Toff213 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (S1 ∷ CS14⁻ ∷ CCZ024 ∷ []) (pw3 c4 (CCZ024 ∷ S1 ∷ CS14⁻ ∷ []) (S1 ∷ CS14⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (X4 ∷ CCZ024 ∷ Toff213 ∷ S1 ∷ CS14⁻ ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ []) (CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  b1 = at 2 3 (S1 ∷ CS14⁻ ∷ Toff213 ∷ []) (lw0 c4 (Toff213 ∷ S1 ∷ CS14⁻ ∷ []) (S1 ∷ CS14⁻ ∷ Toff213 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (S1 ∷ CS14⁻ ∷ CCZ024 ∷ []) (pw3 c4 (CCZ024 ∷ S1 ∷ CS14⁻ ∷ []) (S1 ∷ CS14⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 3 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 5 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 7 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 0 3 (CS14 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ S1 ∷ CS14⁻ ∷ []) (CS14 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-CS0-S2: 14 steps
lem-F4-CS0-S2 : Complete 4 → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS0-S2 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS24 ∷ []) (X4 ∷ Bx2-0413 ∷ S2 ∷ CS24⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ [])
  b0 = at 2 2 (S2 ∷ CS24⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS24 ∷ []) (S2 ∷ CS24⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 1 (CS03 ∷ []) (refl) ▸
       at 5 1 (CS03⁻ ∷ []) (refl) ▸
       at 5 3 (S2 ∷ CS24⁻ ∷ CS03⁻ ∷ []) (pw1 c4 (CS03⁻ ∷ S2 ∷ CS24⁻ ∷ []) (S2 ∷ CS24⁻ ∷ CS03⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 3 (S2 ∷ CS24⁻ ∷ Toff314 ∷ []) (lw0 c4 (Toff314 ∷ S2 ∷ CS24⁻ ∷ []) (S2 ∷ CS24⁻ ∷ Toff314 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (S2 ∷ CS24⁻ ∷ CS03 ∷ []) (pw1 c4 (CS03 ∷ S2 ∷ CS24⁻ ∷ []) (S2 ∷ CS24⁻ ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 2 3 (S2 ∷ CS24⁻ ∷ Toff314 ∷ []) (lw0 c4 (Toff314 ∷ S2 ∷ CS24⁻ ∷ []) (S2 ∷ CS24⁻ ∷ Toff314 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (X4 ∷ Bx2-0413 ∷ S2 ∷ CS24⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ []) (CS24 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  b1 = at 1 2 (S2 ∷ Bx2-0413 ∷ []) (sym (lem-Su-box-at0210243143 c4)) ▸
       at 2 2 (CS24⁻ ∷ Bx2-0413 ∷ []) (sym (lem-CSdu-box-2-at0210243143 c4)) ▸
       at 5 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 7 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 0 3 (CS24 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ S2 ∷ CS24⁻ ∷ []) (CS24 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-CS0-S3: 15 steps
lem-F4-CS0-S3 : Complete 4 → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS0-S3 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS34 ∷ []) (X4 ∷ CCZ024 ∷ Toff213 ∷ S3 ∷ CS34⁻ ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ [])
  b0 = at 2 2 (S3 ∷ CS34⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS34 ∷ []) (S3 ∷ CS34⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 1 (CS03 ∷ []) (refl) ▸
       at 5 1 (CS03⁻ ∷ []) (refl) ▸
       at 2 6 (S3 ∷ CS34⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (pw2 c4 (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ S3 ∷ CS34⁻ ∷ []) (S3 ∷ CS34⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 4 3 (S3 ∷ CS34⁻ ∷ Toff213 ∷ []) (lw0 c4 (Toff213 ∷ S3 ∷ CS34⁻ ∷ []) (S3 ∷ CS34⁻ ∷ Toff213 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (S3 ∷ CS34⁻ ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ S3 ∷ CS34⁻ ∷ []) (S3 ∷ CS34⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (X4 ∷ CCZ024 ∷ Toff213 ∷ S3 ∷ CS34⁻ ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ []) (CS34 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  b1 = at 2 3 (S3 ∷ CS34⁻ ∷ Toff213 ∷ []) (lw0 c4 (Toff213 ∷ S3 ∷ CS34⁻ ∷ []) (S3 ∷ CS34⁻ ∷ Toff213 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (S3 ∷ CS34⁻ ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ S3 ∷ CS34⁻ ∷ []) (S3 ∷ CS34⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 3 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 5 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 7 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 0 3 (CS34 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ S3 ∷ CS34⁻ ∷ []) (CS34 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-CS0-K0: 19 steps
lem-F4-CS0-K0 : Complete 4 → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS0-K0 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ []) (X4 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ K0 ∷ CK40 ∷ Toff213 ∷ S4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ [])
  b0 = at 2 2 (K0 ∷ CK40 ∷ S4 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CK40 ∷ []) (K0 ∷ CK40 ∷ S4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 1 (CS03 ∷ []) (refl) ▸
       at 5 1 (CS03⁻ ∷ []) (refl) ▸
       at 2 7 (K0 ∷ CK40 ∷ S4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (pw2 c4 (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ K0 ∷ CK40 ∷ S4 ∷ []) (K0 ∷ CK40 ∷ S4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 4 2 (K0 ∷ Toff213 ∷ []) (sym (c₁ (K) (K ↑ • CCZ • K ↑ • iI))) ▸
       at 5 2 (CK40 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CK40 c4) ▸ done

  b1 : Chain (X4 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ K0 ∷ CK40 ∷ Toff213 ∷ S4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ []) (X4 ∷ K0 ∷ CK40 ∷ S4 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ [])
  b1 = at 6 2 (S4 ∷ Toff213 ∷ []) (c₄ ((K ↑ • CCZ • K ↑ • iI) ↑) (S)) ▸
       at 3 4 (K0 ∷ CK40 ∷ S4 ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ K0 ∷ CK40 ∷ S4 ∷ []) (K0 ∷ CK40 ∷ S4 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (K0 ∷ Toff213 ∷ []) (sym (c₁ (K) (K ↑ • CCZ • K ↑ • iI))) ▸
       at 3 2 (CK40 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CK40 c4) ▸
       at 4 2 (S4 ∷ Toff213 ∷ []) (c₄ ((K ↑ • CCZ • K ↑ • iI) ↑) (S)) ▸
       at 1 4 (K0 ∷ CK40 ∷ S4 ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ K0 ∷ CK40 ∷ S4 ∷ []) (K0 ∷ CK40 ∷ S4 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 4 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 6 1 (Sb2-0-3-1 ∷ []) (refl) ▸ done

  b2 : Chain (X4 ∷ K0 ∷ CK40 ∷ S4 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ []) (CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  b2 = at 8 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 4 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 0 4 (CK40 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ K0 ∷ CK40 ∷ S4 ∷ []) (CK40 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-CS0-K1: 21 steps
lem-F4-CS0-K1 : Complete 4 → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS0-K1 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ []) (X4 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ K1 ∷ CK41 ∷ S4 ∷ Toff214 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ [])
  b0 = at 2 2 (K1 ∷ CK41 ∷ S4 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK41 ∷ []) (K1 ∷ CK41 ∷ S4 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 1 (CS03 ∷ []) (refl) ▸
       at 5 1 (CS03⁻ ∷ []) (refl) ▸
       at 2 7 (K1 ∷ CK41 ∷ S4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (pw2 c4 (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ K1 ∷ CK41 ∷ S4 ∷ []) (K1 ∷ CK41 ∷ S4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Bx2-0341 ∷ []) (lem-box-perm-1423-at0210243143 c4) ▸
       at 1 1 (CCZ023 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ []) (lem-box-cP-at0210233441 c4) ▸
       at 4 4 (K1 ∷ CK41 ∷ S4 ∷ Toff214 ∷ []) (lw0 c4 (Toff214 ∷ K1 ∷ CK41 ∷ S4 ∷ []) (K1 ∷ CK41 ∷ S4 ∷ Toff214 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (X4 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ K1 ∷ CK41 ∷ S4 ∷ Toff214 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ []) (X4 ∷ K1 ∷ CK41 ∷ S4 ∷ Bx2-0341 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ [])
  b1 = at 3 2 (K1 ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1 ∷ []) (K1 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CK41 ∷ CCZ023 ∷ []) (lem-comm-CCZ023-CK41 c4) ▸
       at 5 2 (S4 ∷ CCZ023 ∷ []) (c₄ (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) (S)) ▸
       at 2 4 (K1 ∷ CK41 ∷ S4 ∷ Toff214 ∷ []) (lw0 c4 (Toff214 ∷ K1 ∷ CK41 ∷ S4 ∷ []) (K1 ∷ CK41 ∷ S4 ∷ Toff214 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (K1 ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ K1 ∷ []) (K1 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CK41 ∷ CCZ023 ∷ []) (lem-comm-CCZ023-CK41 c4) ▸
       at 3 2 (S4 ∷ CCZ023 ∷ []) (c₄ (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) (S)) ▸
       at 4 4 (Bx2-0341 ∷ []) (sym (lem-box-cP-at0210233441 c4)) ▸ done

  b2 : Chain (X4 ∷ K1 ∷ CK41 ∷ S4 ∷ Bx2-0341 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ []) (CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  b2 = at 4 1 (Bx2-0413 ∷ []) (sym (lem-box-perm-1423-at0210243143 c4)) ▸
       at 6 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 8 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 4 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 0 4 (CK41 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ K1 ∷ CK41 ∷ S4 ∷ []) (CK41 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

