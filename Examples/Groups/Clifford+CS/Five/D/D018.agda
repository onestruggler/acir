{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D018 where

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
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-box-tQ)
open import Examples.Groups.Clifford+CS.Five.D.D009 using (lem-box-perm-1243 ; lem-box-tQ-at3443)
open import Examples.Groups.Clifford+CS.Five.D.D017 using (lem-box-cP-at03102132 ; lem-pairs-at13243142 ; lem-pairs-at3443 ; lem-sym-ab-at14233142)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CX12-CCZ034 ; lem-comm-CZ12-CCZ034)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-comm-CS23-CCZ014 ; lem-comm-CSd23-CCZ014)
open import Examples.Groups.Clifford+CS.Five.D.R012 using (lem-comm-CS03-CCZ124 ; lem-comm-CS03-TOFF412 ; lem-comm-CS24-CCZ013 ; lem-comm-CSd03-CCZ124 ; lem-comm-CSd12-TOFF403 ; lem-comm-CSd24-CCZ013 ; lem-comm-TOFF401-CSd23 ; lem-comm-TOFF412-CSd03)
-- box-perm-1243 @3443: 3 steps
lem-box-perm-1243-at3443 : Complete 4 → ⟪ (Bx0-1243 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-box-perm-1243-at3443 c4 = run b0
  where
  b0 : Chain (Bx0-1243 ∷ []) (Bx0-1234 ∷ [])
  b0 = at 0 1 (Bx0-4312 ∷ []) (lem-pairs-at3443 c4) ▸
       at 0 1 (Bx0-3412 ∷ []) (lem-sym-ab-at14233142 c4) ▸
       at 0 1 (Bx0-1234 ∷ []) (lem-pairs-at13243142 c4) ▸ done


-- box-box-3: 105 steps
lem-box-box-3 : Complete 4 → ⟪ (Bx0-1234 ∷ Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-box-box-3 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (run b13)))))))))))))
  where
  b0 : Chain (Bx0-1234 ∷ Bx3-0124 ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ013 ∷ Toff324 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CCZ013 ∷ CS04 ∷ CCZ034 ∷ Toff324 ∷ [])
  b0 = at 0 1 (Bx0-1243 ∷ []) (lem-box-perm-1243 c4) ▸
       at 0 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-box-tQ-at3443 c4) ▸
       at 4 1 (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ []) (lem-box-cP-at03102132 c4) ▸
       at 3 2 (CCZ013 ∷ CCZ034 ∷ []) (pw2 c4 (CCZ034 ∷ CCZ013 ∷ []) (CCZ013 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff324 ∷ CCZ024 ∷ CCZ034 ∷ []) (pw1 c4 (CCZ034 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ024 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ013 ∷ CCZ034 ∷ []) (pw2 c4 (CCZ034 ∷ CCZ013 ∷ []) (CCZ013 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ []) (pw1 c4 (CCZ024 ∷ []) (CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ013 ∷ CS04 ∷ []) (pw2 c4 (CS04 ∷ CCZ013 ∷ []) (CCZ013 ∷ CS04 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ013 ∷ Toff324 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CCZ013 ∷ CS04 ∷ CCZ034 ∷ Toff324 ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ034 ∷ [])
  b1 = at 8 2 (CCZ013 ∷ CX02 ∷ []) (lw4 c4 (CX02 ∷ CCZ013 ∷ []) (CCZ013 ∷ CX02 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ013 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-CCZ013 c4) ▸
       at 6 2 (CCZ013 ∷ CX02 ∷ []) (lw4 c4 (CX02 ∷ CCZ013 ∷ []) (CCZ013 ∷ CX02 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ013 ∷ CS24 ∷ []) (lem-comm-CS24-CCZ013 c4) ▸
       at 6 5 (CCZ024 ∷ []) (pw1 c4 (CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ []) (CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 6 3 (Toff324 ∷ CCZ034 ∷ []) (pw1 c4 (CCZ024 ∷ CCZ034 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 3 4 (Bx3-0124 ∷ []) (sym (lem-box-cP-at03102132 c4)) ▸
       at 3 1 (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ []) (lem-box-cP-at03102132 c4) ▸ done

  b2 : Chain (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ034 ∷ []) (Toff012 ∷ CCZ034 ∷ CCZ013 ∷ K0 ∷ CS12 ∷ Toff324 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0⁻ ∷ CCZ123 ∷ CCZ124 ∷ CCZ013 ∷ Toff324 ∷ CCZ034 ∷ [])
  b2 = at 2 2 (CCZ013 ∷ Toff012 ∷ CCZ123 ∷ []) (lw4 c4 (Toff012 ∷ CCZ013 ∷ []) (CCZ013 ∷ Toff012 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff324 ∷ CCZ123 ∷ CCZ124 ∷ []) (lw0 c4 (CCZ123 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ123 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0⁻ ∷ []) (lw4 c4 (Toff012 ∷ []) (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 9 2 (Toff324 ∷ K0⁻ ∷ []) (c₁ (K • iI) ((K ↑ • CCZ • K ↑ • iI) ↑)) ▸
       at 8 2 (Toff324 ∷ CS02 ∷ []) (pw1 c4 (CS02 ∷ Toff324 ∷ []) (Toff324 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff324 ∷ CX01 ∷ []) (c₂ (CX₀₁) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 6 2 (Toff324 ∷ CS12⁻ ∷ []) (lw0 c4 (CS12⁻ ∷ Toff324 ∷ []) (Toff324 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff324 ∷ CX01 ∷ []) (c₂ (CX₀₁) (K ↑ • CCZ • K ↑ • iI)) ▸ done

  b3 : Chain (Toff012 ∷ CCZ034 ∷ CCZ013 ∷ K0 ∷ CS12 ∷ Toff324 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0⁻ ∷ CCZ123 ∷ CCZ124 ∷ CCZ013 ∷ Toff324 ∷ CCZ034 ∷ []) (Toff012 ∷ CCZ034 ∷ CCZ013 ∷ Toff324 ∷ Toff012 ∷ CCZ123 ∷ CS24 ∷ CCZ013 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ Toff324 ∷ CCZ034 ∷ [])
  b3 = at 4 2 (Toff324 ∷ CS12 ∷ []) (lw0 c4 (CS12 ∷ Toff324 ∷ []) (Toff324 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff324 ∷ K0 ∷ []) (c₁ (K) ((K ↑ • CCZ • K ↑ • iI) ↑)) ▸
       at 4 7 (Toff012 ∷ []) (lw4 c4 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0⁻ ∷ []) (Toff012 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (lw0 c4 (CCZ124 ∷ []) (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (CCZ013 ∷ CS14 ∷ []) (pw2 c4 (CS14 ∷ CCZ013 ∷ []) (CCZ013 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ013 ∷ CX12 ∷ []) (lw4 c4 (CX12 ∷ CCZ013 ∷ []) (CCZ013 ∷ CX12 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ013 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-CCZ013 c4) ▸
       at 7 2 (CCZ013 ∷ CX12 ∷ []) (lw4 c4 (CX12 ∷ CCZ013 ∷ []) (CCZ013 ∷ CX12 ∷ []) tt tt Eq.refl) ▸ done

  b4 : Chain (Toff012 ∷ CCZ034 ∷ CCZ013 ∷ Toff324 ∷ Toff012 ∷ CCZ123 ∷ CS24 ∷ CCZ013 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ Toff324 ∷ CCZ034 ∷ []) (Toff012 ∷ CCZ034 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Toff324 ∷ K0⁻ ∷ CCZ124 ∷ CCZ034 ∷ [])
  b4 = at 6 2 (CCZ013 ∷ CS24 ∷ []) (lem-comm-CS24-CCZ013 c4) ▸
       at 7 5 (CCZ124 ∷ []) (lw0 c4 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ013 ∷ CCZ123 ∷ []) (lw4 c4 (CCZ123 ∷ CCZ013 ∷ []) (CCZ013 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ013 ∷ Toff012 ∷ CCZ123 ∷ []) (lw4 c4 (Toff012 ∷ CCZ013 ∷ []) (CCZ013 ∷ Toff012 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (Toff012 ∷ []) (lw4 c4 (Toff012 ∷ CCZ123 ∷ CCZ123 ∷ []) (Toff012 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Toff324 ∷ CCZ124 ∷ []) (lw0 c4 (CCZ124 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0⁻ ∷ []) (lw4 c4 (Toff012 ∷ []) (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 11 2 (Toff324 ∷ K0⁻ ∷ []) (c₁ (K • iI) ((K ↑ • CCZ • K ↑ • iI) ↑)) ▸ done

  b5 : Chain (Toff012 ∷ CCZ034 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Toff324 ∷ K0⁻ ∷ CCZ124 ∷ CCZ034 ∷ []) (Toff012 ∷ CCZ034 ∷ Bx3-0124 ∷ Toff012 ∷ CCZ124 ∷ CCZ034 ∷ [])
  b5 = at 10 2 (Toff324 ∷ CS02 ∷ []) (pw1 c4 (CS02 ∷ Toff324 ∷ []) (Toff324 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (Toff324 ∷ CX01 ∷ []) (c₂ (CX₀₁) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 8 2 (Toff324 ∷ CS12⁻ ∷ []) (lw0 c4 (CS12⁻ ∷ Toff324 ∷ []) (Toff324 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff324 ∷ CX01 ∷ []) (c₂ (CX₀₁) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 6 2 (Toff324 ∷ CS12 ∷ []) (lw0 c4 (CS12 ∷ Toff324 ∷ []) (Toff324 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff324 ∷ K0 ∷ []) (c₁ (K) ((K ↑ • CCZ • K ↑ • iI) ↑)) ▸
       at 6 7 (Toff012 ∷ []) (lw4 c4 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0⁻ ∷ []) (Toff012 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Bx3-0124 ∷ []) (sym (lem-box-cP-at03102132 c4)) ▸ done

  b6 : Chain (Toff012 ∷ CCZ034 ∷ Bx3-0124 ∷ Toff012 ∷ CCZ124 ∷ CCZ034 ∷ []) (Toff012 ∷ CCZ013 ∷ Toff324 ∷ CS24 ∷ CX02 ∷ CCZ013 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ CCZ034 ∷ Toff324 ∷ Toff012 ∷ CCZ124 ∷ CCZ034 ∷ [])
  b6 = at 2 1 (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ []) (lem-box-cP-at03102132 c4) ▸
       at 1 2 (CCZ013 ∷ CCZ034 ∷ []) (pw2 c4 (CCZ034 ∷ CCZ013 ∷ []) (CCZ013 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff324 ∷ CCZ024 ∷ CCZ034 ∷ []) (pw1 c4 (CCZ034 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ024 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ013 ∷ CCZ034 ∷ []) (pw2 c4 (CCZ034 ∷ CCZ013 ∷ []) (CCZ013 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ []) (pw1 c4 (CCZ024 ∷ []) (CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ013 ∷ CS04 ∷ []) (pw2 c4 (CS04 ∷ CCZ013 ∷ []) (CCZ013 ∷ CS04 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ013 ∷ CX02 ∷ []) (lw4 c4 (CX02 ∷ CCZ013 ∷ []) (CCZ013 ∷ CX02 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ013 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-CCZ013 c4) ▸ done

  b7 : Chain (Toff012 ∷ CCZ013 ∷ Toff324 ∷ CS24 ∷ CX02 ∷ CCZ013 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ CCZ034 ∷ Toff324 ∷ Toff012 ∷ CCZ124 ∷ CCZ034 ∷ []) (CCZ013 ∷ Toff012 ∷ Toff324 ∷ CCZ123 ∷ CCZ124 ∷ CCZ013 ∷ Toff324 ∷ CCZ034 ∷ Toff012 ∷ CCZ124 ∷ CCZ034 ∷ [])
  b7 = at 4 2 (CCZ013 ∷ CX02 ∷ []) (lw4 c4 (CX02 ∷ CCZ013 ∷ []) (CCZ013 ∷ CX02 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ013 ∷ CS24 ∷ []) (lem-comm-CS24-CCZ013 c4) ▸
       at 4 5 (CCZ024 ∷ []) (pw1 c4 (CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ []) (CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (Toff324 ∷ CCZ034 ∷ []) (pw1 c4 (CCZ024 ∷ CCZ034 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 1 4 (Bx3-0124 ∷ []) (sym (lem-box-cP-at03102132 c4)) ▸
       at 1 1 (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ []) (lem-box-cP-at03102132 c4) ▸
       at 0 2 (CCZ013 ∷ Toff012 ∷ CCZ123 ∷ []) (lw4 c4 (Toff012 ∷ CCZ013 ∷ []) (CCZ013 ∷ Toff012 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff324 ∷ CCZ123 ∷ CCZ124 ∷ []) (lw0 c4 (CCZ123 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ123 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸ done

  b8 : Chain (CCZ013 ∷ Toff012 ∷ Toff324 ∷ CCZ123 ∷ CCZ124 ∷ CCZ013 ∷ Toff324 ∷ CCZ034 ∷ Toff012 ∷ CCZ124 ∷ CCZ034 ∷ []) (CCZ013 ∷ Toff324 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0⁻ ∷ CCZ123 ∷ CCZ124 ∷ CCZ013 ∷ Toff324 ∷ CCZ034 ∷ Toff012 ∷ CCZ124 ∷ CCZ034 ∷ [])
  b8 = at 1 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0⁻ ∷ []) (lw4 c4 (Toff012 ∷ []) (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff324 ∷ K0⁻ ∷ []) (c₁ (K • iI) ((K ↑ • CCZ • K ↑ • iI) ↑)) ▸
       at 6 2 (Toff324 ∷ CS02 ∷ []) (pw1 c4 (CS02 ∷ Toff324 ∷ []) (Toff324 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff324 ∷ CX01 ∷ []) (c₂ (CX₀₁) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 4 2 (Toff324 ∷ CS12⁻ ∷ []) (lw0 c4 (CS12⁻ ∷ Toff324 ∷ []) (Toff324 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff324 ∷ CX01 ∷ []) (c₂ (CX₀₁) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 2 2 (Toff324 ∷ CS12 ∷ []) (lw0 c4 (CS12 ∷ Toff324 ∷ []) (Toff324 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff324 ∷ K0 ∷ []) (c₁ (K) ((K ↑ • CCZ • K ↑ • iI) ↑)) ▸ done

  b9 : Chain (CCZ013 ∷ Toff324 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0⁻ ∷ CCZ123 ∷ CCZ124 ∷ CCZ013 ∷ Toff324 ∷ CCZ034 ∷ Toff012 ∷ CCZ124 ∷ CCZ034 ∷ []) (CCZ013 ∷ Toff324 ∷ Toff012 ∷ CCZ123 ∷ CCZ013 ∷ CCZ124 ∷ Toff324 ∷ CCZ034 ∷ Toff012 ∷ CCZ124 ∷ CCZ034 ∷ [])
  b9 = at 2 7 (Toff012 ∷ []) (lw4 c4 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0⁻ ∷ []) (Toff012 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (lw0 c4 (CCZ124 ∷ []) (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ013 ∷ CS14 ∷ []) (pw2 c4 (CS14 ∷ CCZ013 ∷ []) (CCZ013 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ013 ∷ CX12 ∷ []) (lw4 c4 (CX12 ∷ CCZ013 ∷ []) (CCZ013 ∷ CX12 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ013 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-CCZ013 c4) ▸
       at 5 2 (CCZ013 ∷ CX12 ∷ []) (lw4 c4 (CX12 ∷ CCZ013 ∷ []) (CCZ013 ∷ CX12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ013 ∷ CS24 ∷ []) (lem-comm-CS24-CCZ013 c4) ▸
       at 5 5 (CCZ124 ∷ []) (lw0 c4 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl) ▸ done

  b10 : Chain (CCZ013 ∷ Toff324 ∷ Toff012 ∷ CCZ123 ∷ CCZ013 ∷ CCZ124 ∷ Toff324 ∷ CCZ034 ∷ Toff012 ∷ CCZ124 ∷ CCZ034 ∷ []) (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Toff324 ∷ CX01 ∷ CS02 ∷ K0⁻ ∷ CCZ124 ∷ CCZ034 ∷ Toff012 ∷ CCZ124 ∷ CCZ034 ∷ [])
  b10 = at 3 2 (CCZ013 ∷ CCZ123 ∷ []) (lw4 c4 (CCZ123 ∷ CCZ013 ∷ []) (CCZ013 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ013 ∷ Toff012 ∷ CCZ123 ∷ []) (lw4 c4 (Toff012 ∷ CCZ013 ∷ []) (CCZ013 ∷ Toff012 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (Toff012 ∷ []) (lw4 c4 (Toff012 ∷ CCZ123 ∷ CCZ123 ∷ []) (Toff012 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff324 ∷ CCZ124 ∷ []) (lw0 c4 (CCZ124 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0⁻ ∷ []) (lw4 c4 (Toff012 ∷ []) (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 9 2 (Toff324 ∷ K0⁻ ∷ []) (c₁ (K • iI) ((K ↑ • CCZ • K ↑ • iI) ↑)) ▸
       at 8 2 (Toff324 ∷ CS02 ∷ []) (pw1 c4 (CS02 ∷ Toff324 ∷ []) (Toff324 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff324 ∷ CX01 ∷ []) (c₂ (CX₀₁) (K ↑ • CCZ • K ↑ • iI)) ▸ done

  b11 : Chain (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Toff324 ∷ CX01 ∷ CS02 ∷ K0⁻ ∷ CCZ124 ∷ CCZ034 ∷ Toff012 ∷ CCZ124 ∷ CCZ034 ∷ []) (Bx3-0124 ∷ Toff012 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CCZ034 ∷ CS14 ∷ Toff012 ∷ CCZ124 ∷ CCZ034 ∷ [])
  b11 = at 6 2 (Toff324 ∷ CS12⁻ ∷ []) (lw0 c4 (CS12⁻ ∷ Toff324 ∷ []) (Toff324 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff324 ∷ CX01 ∷ []) (c₂ (CX₀₁) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 4 2 (Toff324 ∷ CS12 ∷ []) (lw0 c4 (CS12 ∷ Toff324 ∷ []) (Toff324 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff324 ∷ K0 ∷ []) (c₁ (K) ((K ↑ • CCZ • K ↑ • iI) ↑)) ▸
       at 4 7 (Toff012 ∷ []) (lw4 c4 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0⁻ ∷ []) (Toff012 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx3-0124 ∷ []) (sym (lem-box-cP-at03102132 c4)) ▸
       at 2 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (lw0 c4 (CCZ124 ∷ []) (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ034 ∷ CS14 ∷ []) (pw2 c4 (CS14 ∷ CCZ034 ∷ []) (CCZ034 ∷ CS14 ∷ []) tt tt Eq.refl) ▸ done

  b12 : Chain (Bx3-0124 ∷ Toff012 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CCZ034 ∷ CS14 ∷ Toff012 ∷ CCZ124 ∷ CCZ034 ∷ []) (Bx3-0124 ∷ Bx0-1243 ∷ [])
  b12 = at 5 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 c4) ▸
       at 4 2 (CCZ034 ∷ CS24⁻ ∷ []) (pw1 c4 (CS24⁻ ∷ CCZ034 ∷ []) (CCZ034 ∷ CS24⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 c4) ▸
       at 2 2 (CCZ034 ∷ CS24 ∷ []) (pw1 c4 (CS24 ∷ CCZ034 ∷ []) (CCZ034 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 3 5 (CCZ124 ∷ []) (lw0 c4 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff012 ∷ CCZ124 ∷ []) (pw3 c4 (CCZ124 ∷ Toff012 ∷ []) (Toff012 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw0 c4 (CCZ124 ∷ CCZ124 ∷ []) [] tt tt Eq.refl) ▸
       at 1 4 (Bx0-1243 ∷ []) (sym (lem-box-tQ-at3443 c4)) ▸ done

  b13 : Chain (Bx3-0124 ∷ Bx0-1243 ∷ []) (Bx3-0124 ∷ Bx0-1234 ∷ [])
  b13 = at 1 1 (Bx0-1234 ∷ []) (lem-box-perm-1243-at3443 c4) ▸ done


-- cQ @0410213243: 7 steps
lem-cQ-at0410213243 : Complete 4 → ⟪ (CCZ014 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ CCZ014 ∷ []) ⟫ʷ
lem-cQ-at0410213243 c4 = run b0
  where
  b0 : Chain (CCZ014 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ014 ∷ [])
  b0 = at 0 1 (CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ []) (pw2 c4 (CCZ014 ∷ []) (CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ234 ∷ CS04 ∷ []) (pw1 c4 (CS04 ∷ CCZ234 ∷ []) (CCZ234 ∷ CS04 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (CCZ)) ▸
       at 2 2 (CCZ234 ∷ CS14⁻ ∷ []) (lw0 c4 (CS14⁻ ∷ CCZ234 ∷ []) (CCZ234 ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (CCZ)) ▸
       at 0 2 (CCZ234 ∷ CS14 ∷ []) (lw0 c4 (CS14 ∷ CCZ234 ∷ []) (CCZ234 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 1 5 (CCZ014 ∷ []) (pw2 c4 (CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ []) (CCZ014 ∷ []) tt tt Eq.refl) ▸ done


-- tP @0410213243: 7 steps
lem-tP-at0410213243 : Complete 4 → ⟪ (Toff401 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ Toff401 ∷ []) ⟫ʷ
lem-tP-at0410213243 c4 = run b0
  where
  b0 : Chain (Toff401 ∷ Toff423 ∷ []) (Toff423 ∷ Toff401 ∷ [])
  b0 = at 0 1 (K4 ∷ CCZ014 ∷ K4⁻ ∷ []) (pw2 c4 (Toff401 ∷ []) (K4 ∷ CCZ014 ∷ K4⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 1 (K4 ∷ CCZ234 ∷ K4⁻ ∷ []) (lw0 c4 (Toff423 ∷ []) (K4 ∷ CCZ234 ∷ K4⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw0 c4 (K4⁻ ∷ K4 ∷ []) [] tt tt Eq.refl) ▸
       at 1 2 (CCZ234 ∷ CCZ014 ∷ []) (lem-cQ-at0410213243 c4) ▸
       at 2 0 (K4⁻ ∷ K4 ∷ []) (lw0 c4 [] (K4⁻ ∷ K4 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Toff423 ∷ []) (lw0 c4 (K4 ∷ CCZ234 ∷ K4⁻ ∷ []) (Toff423 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Toff401 ∷ []) (pw2 c4 (K4 ∷ CCZ014 ∷ K4⁻ ∷ []) (Toff401 ∷ []) tt tt Eq.refl) ▸ done


-- VPQ @0410213243: 14 steps
lem-VPQ-at0410213243 : Complete 4 → ⟪ (Toff401 ∷ CCZ014 ∷ Toff423 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CCZ234 ∷ Toff401 ∷ CCZ014 ∷ []) ⟫ʷ
lem-VPQ-at0410213243 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff401 ∷ CCZ014 ∷ Toff423 ∷ CCZ234 ∷ []) (CS23⁻ ∷ CS01⁻ ∷ S4 ∷ Toff423 ∷ Toff401 ∷ S4⁻ ∷ [])
  b0 = at 0 2 (CS01⁻ ∷ S4 ∷ Toff401 ∷ S4⁻ ∷ []) (pw2 c4 (Toff401 ∷ CCZ014 ∷ []) (CS01⁻ ∷ S4 ∷ Toff401 ∷ S4⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CS23⁻ ∷ S4 ∷ Toff423 ∷ S4⁻ ∷ []) (lw0 c4 (Toff423 ∷ CCZ234 ∷ []) (CS23⁻ ∷ S4 ∷ Toff423 ∷ S4⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CS23⁻ ∷ S4⁻ ∷ []) (sym (c₄ ((CS • CS • CS) ↑ ↑) (S • S • S))) ▸
       at 2 2 (CS23⁻ ∷ Toff401 ∷ []) (lem-comm-TOFF401-CSd23 c4) ▸
       at 1 2 (CS23⁻ ∷ S4 ∷ []) (sym (c₄ ((CS • CS • CS) ↑ ↑) (S))) ▸
       at 0 2 (CS23⁻ ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (CS • CS • CS)) ▸
       at 4 2 [] (lw0 c4 (S4⁻ ∷ S4 ∷ []) [] tt tt Eq.refl) ▸
       at 3 2 (Toff423 ∷ Toff401 ∷ []) (lem-tP-at0410213243 c4) ▸ done

  b1 : Chain (CS23⁻ ∷ CS01⁻ ∷ S4 ∷ Toff423 ∷ Toff401 ∷ S4⁻ ∷ []) (Toff423 ∷ CCZ234 ∷ Toff401 ∷ CCZ014 ∷ [])
  b1 = at 4 0 (S4⁻ ∷ S4 ∷ []) (lw0 c4 [] (S4⁻ ∷ S4 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (S4 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (S ↑ ↑)) ▸
       at 2 2 (Toff423 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (Toffᵗ)) ▸
       at 3 2 (S4⁻ ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) ((S • S • S) ↑ ↑)) ▸
       at 0 4 (Toff423 ∷ CCZ234 ∷ []) (lw0 c4 (CS23⁻ ∷ S4 ∷ Toff423 ∷ S4⁻ ∷ []) (Toff423 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Toff401 ∷ CCZ014 ∷ []) (pw2 c4 (CS01⁻ ∷ S4 ∷ Toff401 ∷ S4⁻ ∷ []) (Toff401 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸ done


-- QVQ @0410213243: 3 steps
lem-QVQ-at0410213243 : Complete 4 → ⟪ (CCZ234 ∷ Toff401 ∷ CCZ014 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ Toff401 ∷ CCZ014 ∷ Toff423 ∷ []) ⟫ʷ
lem-QVQ-at0410213243 c4 = run b0
  where
  b0 : Chain (CCZ234 ∷ Toff401 ∷ CCZ014 ∷ CCZ234 ∷ []) (Toff423 ∷ Toff401 ∷ CCZ014 ∷ Toff423 ∷ [])
  b0 = at 0 0 (Toff423 ∷ Toff423 ∷ []) (lw0 c4 [] (Toff423 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 1 4 (Toff401 ∷ CCZ014 ∷ Toff423 ∷ CCZ234 ∷ []) (sym (lem-VPQ-at0410213243 c4)) ▸
       at 4 2 [] (lw0 c4 (CCZ234 ∷ CCZ234 ∷ []) [] tt tt Eq.refl) ▸ done


-- box-cP @0410213243: 12 steps
lem-box-cP-at0410213243 : Complete 4 → ⟪ (Bx4-0123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) ⟫ʷ
lem-box-cP-at0410213243 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx4-0123 ∷ []) (CCZ014 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ014 ∷ CCZ024 ∷ Toff024 ∷ CZ03 ∷ Toff024 ∷ CCZ024 ∷ CZ03 ∷ [])
  b0 = at 0 1 (CCZ014 ∷ Toff401 ∷ Bx0-423 ∷ Toff401 ∷ CCZ014 ∷ Bx0-423 ∷ []) (refl) ▸
       at 2 1 (CCZ024 ∷ Toff024 ∷ Bx4-03 ∷ Toff024 ∷ CCZ024 ∷ Bx4-03 ∷ []) (refl) ▸
       at 4 1 (CZ03 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 2 6 (CCZ234 ∷ []) (pw1 c4 (CCZ024 ∷ Toff024 ∷ CZ03 ∷ Toff024 ∷ CCZ024 ∷ CZ03 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ024 ∷ Toff024 ∷ Bx4-03 ∷ Toff024 ∷ CCZ024 ∷ Bx4-03 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 10 1 (CZ03 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ014 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ014 ∷ CCZ024 ∷ Toff024 ∷ CZ03 ∷ Toff024 ∷ CCZ024 ∷ CZ03 ∷ []) (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ [])
  b1 = at 5 6 (CCZ234 ∷ []) (pw1 c4 (CCZ024 ∷ Toff024 ∷ CZ03 ∷ Toff024 ∷ CCZ024 ∷ CZ03 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Toff423 ∷ Toff401 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-QVQ-at0410213243 c4) ▸
       at 1 2 (Toff423 ∷ Toff401 ∷ []) (lem-tP-at0410213243 c4) ▸
       at 2 2 [] (pw2 c4 (Toff401 ∷ Toff401 ∷ []) [] tt tt Eq.refl) ▸ done


-- box-box-4: 103 steps
lem-box-box-4 : Complete 4 → ⟪ (Bx0-1234 ∷ Bx4-0123 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0123 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-box-box-4 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (run b12))))))))))))
  where
  b0 : Chain (Bx0-1234 ∷ Bx4-0123 ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ014 ∷ Toff423 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CCZ014 ∷ CX02 ∷ CS03 ∷ CCZ034 ∷ Toff423 ∷ [])
  b0 = at 0 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-box-tQ c4) ▸
       at 4 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at0410213243 c4) ▸
       at 3 2 (CCZ014 ∷ CCZ034 ∷ []) (pw2 c4 (CCZ034 ∷ CCZ014 ∷ []) (CCZ014 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff423 ∷ CCZ023 ∷ CCZ034 ∷ []) (pw1 c4 (CCZ034 ∷ Toff423 ∷ []) (Toff423 ∷ CCZ023 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ014 ∷ CCZ034 ∷ []) (pw2 c4 (CCZ034 ∷ CCZ014 ∷ []) (CCZ014 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ []) (lw4 c4 (CCZ023 ∷ []) (CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ014 ∷ CS03 ∷ []) (pw2 c4 (CS03 ∷ CCZ014 ∷ []) (CCZ014 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ014 ∷ CX02 ∷ []) (pw3 c4 (CX02 ∷ CCZ014 ∷ []) (CCZ014 ∷ CX02 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ014 ∷ Toff423 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CCZ014 ∷ CX02 ∷ CS03 ∷ CCZ034 ∷ Toff423 ∷ []) (Toff012 ∷ CCZ034 ∷ CCZ014 ∷ Toff012 ∷ CCZ124 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ CCZ034 ∷ [])
  b1 = at 7 2 (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 c4) ▸
       at 6 2 (CCZ014 ∷ CX02 ∷ []) (pw3 c4 (CX02 ∷ CCZ014 ∷ []) (CCZ014 ∷ CX02 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 c4) ▸
       at 6 5 (CCZ023 ∷ []) (lw4 c4 (CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ []) (CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 6 3 (Toff423 ∷ CCZ034 ∷ []) (pw1 c4 (CCZ023 ∷ CCZ034 ∷ Toff423 ∷ []) (Toff423 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 3 4 (Bx4-0123 ∷ []) (sym (lem-box-cP-at0410213243 c4)) ▸
       at 3 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at0410213243 c4) ▸
       at 2 2 (CCZ014 ∷ Toff012 ∷ CCZ124 ∷ []) (pw3 c4 (Toff012 ∷ CCZ014 ∷ []) (CCZ014 ∷ Toff012 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Toff012 ∷ CCZ034 ∷ CCZ014 ∷ Toff012 ∷ CCZ124 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ CCZ034 ∷ []) (Toff012 ∷ CCZ034 ∷ CCZ014 ∷ K0 ∷ Toff423 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0⁻ ∷ CCZ123 ∷ CCZ124 ∷ CCZ014 ∷ Toff423 ∷ CCZ034 ∷ [])
  b2 = at 4 2 (Toff423 ∷ CCZ123 ∷ CCZ124 ∷ []) (lw0 c4 (CCZ124 ∷ Toff423 ∷ []) (Toff423 ∷ CCZ123 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0⁻ ∷ []) (lw4 c4 (Toff012 ∷ []) (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 9 2 (Toff423 ∷ K0⁻ ∷ []) (c₁ (K • iI) (Toffᵗ ↑)) ▸
       at 8 2 (Toff423 ∷ CS02 ∷ []) (pw1 c4 (CS02 ∷ Toff423 ∷ []) (Toff423 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff423 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Toffᵗ)) ▸
       at 6 2 (Toff423 ∷ CS12⁻ ∷ []) (lw0 c4 (CS12⁻ ∷ Toff423 ∷ []) (Toff423 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff423 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Toffᵗ)) ▸
       at 4 2 (Toff423 ∷ CS12 ∷ []) (lw0 c4 (CS12 ∷ Toff423 ∷ []) (Toff423 ∷ CS12 ∷ []) tt tt Eq.refl) ▸ done

  b3 : Chain (Toff012 ∷ CCZ034 ∷ CCZ014 ∷ K0 ∷ Toff423 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0⁻ ∷ CCZ123 ∷ CCZ124 ∷ CCZ014 ∷ Toff423 ∷ CCZ034 ∷ []) (Toff012 ∷ CCZ034 ∷ CCZ014 ∷ Toff423 ∷ Toff012 ∷ CS23 ∷ CCZ014 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CCZ124 ∷ Toff423 ∷ CCZ034 ∷ [])
  b3 = at 3 2 (Toff423 ∷ K0 ∷ []) (c₁ (K) (Toffᵗ ↑)) ▸
       at 4 7 (Toff012 ∷ []) (lw4 c4 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0⁻ ∷ []) (Toff012 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ014 ∷ CCZ124 ∷ []) (pw3 c4 (CCZ124 ∷ CCZ014 ∷ []) (CCZ014 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (lw4 c4 (CCZ123 ∷ []) (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ014 ∷ CS13 ∷ []) (pw2 c4 (CS13 ∷ CCZ014 ∷ []) (CCZ014 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ014 ∷ CX12 ∷ []) (pw3 c4 (CX12 ∷ CCZ014 ∷ []) (CCZ014 ∷ CX12 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 c4) ▸
       at 6 2 (CCZ014 ∷ CX12 ∷ []) (pw3 c4 (CX12 ∷ CCZ014 ∷ []) (CCZ014 ∷ CX12 ∷ []) tt tt Eq.refl) ▸ done

  b4 : Chain (Toff012 ∷ CCZ034 ∷ CCZ014 ∷ Toff423 ∷ Toff012 ∷ CS23 ∷ CCZ014 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CCZ124 ∷ Toff423 ∷ CCZ034 ∷ []) (Toff012 ∷ CCZ034 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Toff423 ∷ CS02 ∷ K0⁻ ∷ CCZ123 ∷ CCZ034 ∷ [])
  b4 = at 5 2 (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 c4) ▸
       at 6 5 (CCZ123 ∷ []) (lw4 c4 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ014 ∷ Toff012 ∷ CCZ124 ∷ []) (pw3 c4 (Toff012 ∷ CCZ014 ∷ []) (CCZ014 ∷ Toff012 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 6 3 (CCZ123 ∷ []) (lw0 c4 (CCZ124 ∷ CCZ123 ∷ CCZ124 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Toff423 ∷ CCZ123 ∷ []) (lw0 c4 (CCZ123 ∷ Toff423 ∷ []) (Toff423 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0⁻ ∷ []) (lw4 c4 (Toff012 ∷ []) (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 11 2 (Toff423 ∷ K0⁻ ∷ []) (c₁ (K • iI) (Toffᵗ ↑)) ▸
       at 10 2 (Toff423 ∷ CS02 ∷ []) (pw1 c4 (CS02 ∷ Toff423 ∷ []) (Toff423 ∷ CS02 ∷ []) tt tt Eq.refl) ▸ done

  b5 : Chain (Toff012 ∷ CCZ034 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Toff423 ∷ CS02 ∷ K0⁻ ∷ CCZ123 ∷ CCZ034 ∷ []) (Toff012 ∷ CCZ034 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ Toff012 ∷ CCZ123 ∷ CCZ034 ∷ [])
  b5 = at 9 2 (Toff423 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Toffᵗ)) ▸
       at 8 2 (Toff423 ∷ CS12⁻ ∷ []) (lw0 c4 (CS12⁻ ∷ Toff423 ∷ []) (Toff423 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff423 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Toffᵗ)) ▸
       at 6 2 (Toff423 ∷ CS12 ∷ []) (lw0 c4 (CS12 ∷ Toff423 ∷ []) (Toff423 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff423 ∷ K0 ∷ []) (c₁ (K) (Toffᵗ ↑)) ▸
       at 6 7 (Toff012 ∷ []) (lw4 c4 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0⁻ ∷ []) (Toff012 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Bx4-0123 ∷ []) (sym (lem-box-cP-at0410213243 c4)) ▸
       at 2 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at0410213243 c4) ▸ done

  b6 : Chain (Toff012 ∷ CCZ034 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ Toff012 ∷ CCZ123 ∷ CCZ034 ∷ []) (Toff012 ∷ CCZ014 ∷ Toff423 ∷ CS23 ∷ CCZ014 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ CCZ034 ∷ Toff423 ∷ Toff012 ∷ CCZ123 ∷ CCZ034 ∷ [])
  b6 = at 1 2 (CCZ014 ∷ CCZ034 ∷ []) (pw2 c4 (CCZ034 ∷ CCZ014 ∷ []) (CCZ014 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff423 ∷ CCZ023 ∷ CCZ034 ∷ []) (pw1 c4 (CCZ034 ∷ Toff423 ∷ []) (Toff423 ∷ CCZ023 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ014 ∷ CCZ034 ∷ []) (pw2 c4 (CCZ034 ∷ CCZ014 ∷ []) (CCZ014 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ []) (lw4 c4 (CCZ023 ∷ []) (CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ014 ∷ CS03 ∷ []) (pw2 c4 (CS03 ∷ CCZ014 ∷ []) (CCZ014 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ014 ∷ CX02 ∷ []) (pw3 c4 (CX02 ∷ CCZ014 ∷ []) (CCZ014 ∷ CX02 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 c4) ▸
       at 4 2 (CCZ014 ∷ CX02 ∷ []) (pw3 c4 (CX02 ∷ CCZ014 ∷ []) (CCZ014 ∷ CX02 ∷ []) tt tt Eq.refl) ▸ done

  b7 : Chain (Toff012 ∷ CCZ014 ∷ Toff423 ∷ CS23 ∷ CCZ014 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ CCZ034 ∷ Toff423 ∷ Toff012 ∷ CCZ123 ∷ CCZ034 ∷ []) (CCZ014 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0⁻ ∷ Toff423 ∷ CCZ123 ∷ CCZ124 ∷ CCZ014 ∷ Toff423 ∷ CCZ034 ∷ Toff012 ∷ CCZ123 ∷ CCZ034 ∷ [])
  b7 = at 3 2 (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 c4) ▸
       at 4 5 (CCZ023 ∷ []) (lw4 c4 (CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ []) (CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (Toff423 ∷ CCZ034 ∷ []) (pw1 c4 (CCZ023 ∷ CCZ034 ∷ Toff423 ∷ []) (Toff423 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 1 4 (Bx4-0123 ∷ []) (sym (lem-box-cP-at0410213243 c4)) ▸
       at 1 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at0410213243 c4) ▸
       at 0 2 (CCZ014 ∷ Toff012 ∷ CCZ124 ∷ []) (pw3 c4 (Toff012 ∷ CCZ014 ∷ []) (CCZ014 ∷ Toff012 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff423 ∷ CCZ123 ∷ CCZ124 ∷ []) (lw0 c4 (CCZ124 ∷ Toff423 ∷ []) (Toff423 ∷ CCZ123 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0⁻ ∷ []) (lw4 c4 (Toff012 ∷ []) (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸ done

  b8 : Chain (CCZ014 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0⁻ ∷ Toff423 ∷ CCZ123 ∷ CCZ124 ∷ CCZ014 ∷ Toff423 ∷ CCZ034 ∷ Toff012 ∷ CCZ123 ∷ CCZ034 ∷ []) (CCZ014 ∷ Toff423 ∷ Toff012 ∷ CCZ123 ∷ CCZ124 ∷ CCZ014 ∷ Toff423 ∷ CCZ034 ∷ Toff012 ∷ CCZ123 ∷ CCZ034 ∷ [])
  b8 = at 7 2 (Toff423 ∷ K0⁻ ∷ []) (c₁ (K • iI) (Toffᵗ ↑)) ▸
       at 6 2 (Toff423 ∷ CS02 ∷ []) (pw1 c4 (CS02 ∷ Toff423 ∷ []) (Toff423 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff423 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Toffᵗ)) ▸
       at 4 2 (Toff423 ∷ CS12⁻ ∷ []) (lw0 c4 (CS12⁻ ∷ Toff423 ∷ []) (Toff423 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff423 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Toffᵗ)) ▸
       at 2 2 (Toff423 ∷ CS12 ∷ []) (lw0 c4 (CS12 ∷ Toff423 ∷ []) (Toff423 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff423 ∷ K0 ∷ []) (c₁ (K) (Toffᵗ ↑)) ▸
       at 2 7 (Toff012 ∷ []) (lw4 c4 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0⁻ ∷ []) (Toff012 ∷ []) tt tt Eq.refl) ▸ done

  b9 : Chain (CCZ014 ∷ Toff423 ∷ Toff012 ∷ CCZ123 ∷ CCZ124 ∷ CCZ014 ∷ Toff423 ∷ CCZ034 ∷ Toff012 ∷ CCZ123 ∷ CCZ034 ∷ []) (CCZ014 ∷ Toff423 ∷ Toff012 ∷ CCZ014 ∷ CCZ123 ∷ CCZ124 ∷ Toff423 ∷ CCZ034 ∷ Toff012 ∷ CCZ123 ∷ CCZ034 ∷ [])
  b9 = at 4 2 (CCZ014 ∷ CCZ124 ∷ []) (pw3 c4 (CCZ124 ∷ CCZ014 ∷ []) (CCZ014 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (lw4 c4 (CCZ123 ∷ []) (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ014 ∷ CS13 ∷ []) (pw2 c4 (CS13 ∷ CCZ014 ∷ []) (CCZ014 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ014 ∷ CX12 ∷ []) (pw3 c4 (CX12 ∷ CCZ014 ∷ []) (CCZ014 ∷ CX12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 c4) ▸
       at 4 2 (CCZ014 ∷ CX12 ∷ []) (pw3 c4 (CX12 ∷ CCZ014 ∷ []) (CCZ014 ∷ CX12 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 c4) ▸
       at 4 5 (CCZ123 ∷ []) (lw4 c4 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸ done

  b10 : Chain (CCZ014 ∷ Toff423 ∷ Toff012 ∷ CCZ014 ∷ CCZ123 ∷ CCZ124 ∷ Toff423 ∷ CCZ034 ∷ Toff012 ∷ CCZ123 ∷ CCZ034 ∷ []) (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ K0 ∷ CS12 ∷ CX01 ∷ Toff423 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0⁻ ∷ CCZ123 ∷ CCZ034 ∷ Toff012 ∷ CCZ123 ∷ CCZ034 ∷ [])
  b10 = at 2 2 (CCZ014 ∷ Toff012 ∷ CCZ124 ∷ []) (pw3 c4 (Toff012 ∷ CCZ014 ∷ []) (CCZ014 ∷ Toff012 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CCZ123 ∷ []) (lw0 c4 (CCZ124 ∷ CCZ123 ∷ CCZ124 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff423 ∷ CCZ123 ∷ []) (lw0 c4 (CCZ123 ∷ Toff423 ∷ []) (Toff423 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0⁻ ∷ []) (lw4 c4 (Toff012 ∷ []) (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 9 2 (Toff423 ∷ K0⁻ ∷ []) (c₁ (K • iI) (Toffᵗ ↑)) ▸
       at 8 2 (Toff423 ∷ CS02 ∷ []) (pw1 c4 (CS02 ∷ Toff423 ∷ []) (Toff423 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff423 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Toffᵗ)) ▸
       at 6 2 (Toff423 ∷ CS12⁻ ∷ []) (lw0 c4 (CS12⁻ ∷ Toff423 ∷ []) (Toff423 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸ done

  b11 : Chain (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ K0 ∷ CS12 ∷ CX01 ∷ Toff423 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0⁻ ∷ CCZ123 ∷ CCZ034 ∷ Toff012 ∷ CCZ123 ∷ CCZ034 ∷ []) (Bx4-0123 ∷ Toff012 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CCZ034 ∷ CX12 ∷ CS13 ∷ Toff012 ∷ CCZ123 ∷ CCZ034 ∷ [])
  b11 = at 5 2 (Toff423 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Toffᵗ)) ▸
       at 4 2 (Toff423 ∷ CS12 ∷ []) (lw0 c4 (CS12 ∷ Toff423 ∷ []) (Toff423 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff423 ∷ K0 ∷ []) (c₁ (K) (Toffᵗ ↑)) ▸
       at 4 7 (Toff012 ∷ []) (lw4 c4 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0⁻ ∷ []) (Toff012 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx4-0123 ∷ []) (sym (lem-box-cP-at0410213243 c4)) ▸
       at 2 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (lw4 c4 (CCZ123 ∷ []) (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ034 ∷ CS13 ∷ []) (pw2 c4 (CS13 ∷ CCZ034 ∷ []) (CCZ034 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 c4) ▸ done

  b12 : Chain (Bx4-0123 ∷ Toff012 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CCZ034 ∷ CX12 ∷ CS13 ∷ Toff012 ∷ CCZ123 ∷ CCZ034 ∷ []) (Bx4-0123 ∷ Bx0-1234 ∷ [])
  b12 = at 4 2 (CCZ034 ∷ CS23⁻ ∷ []) (pw1 c4 (CS23⁻ ∷ CCZ034 ∷ []) (CCZ034 ∷ CS23⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 c4) ▸
       at 2 2 (CCZ034 ∷ CS23 ∷ []) (pw1 c4 (CS23 ∷ CCZ034 ∷ []) (CCZ034 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 3 5 (CCZ123 ∷ []) (lw4 c4 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff012 ∷ CCZ123 ∷ []) (lw4 c4 (CCZ123 ∷ Toff012 ∷ []) (Toff012 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw4 c4 (CCZ123 ∷ CCZ123 ∷ []) [] tt tt Eq.refl) ▸
       at 1 4 (Bx0-1234 ∷ []) (sym (lem-box-tQ c4)) ▸ done


-- cQ @043043: 7 steps
lem-cQ-at043043 : Complete 4 → ⟪ (CCZ124 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ CCZ124 ∷ []) ⟫ʷ
lem-cQ-at043043 c4 = run b0
  where
  b0 : Chain (CCZ124 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ124 ∷ [])
  b0 = at 0 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (lw0 c4 (CCZ124 ∷ []) (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ034 ∷ CS14 ∷ []) (pw2 c4 (CS14 ∷ CCZ034 ∷ []) (CCZ034 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 c4) ▸
       at 2 2 (CCZ034 ∷ CS24⁻ ∷ []) (pw1 c4 (CS24⁻ ∷ CCZ034 ∷ []) (CCZ034 ∷ CS24⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 c4) ▸
       at 0 2 (CCZ034 ∷ CS24 ∷ []) (pw1 c4 (CS24 ∷ CCZ034 ∷ []) (CCZ034 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 1 5 (CCZ124 ∷ []) (lw0 c4 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl) ▸ done


-- box-tQ @043043: 13 steps
lem-box-tQ-at043043 : Complete 4 → ⟪ (Bx4-1203 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ034 ∷ []) ⟫ʷ
lem-box-tQ-at043043 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx4-1203 ∷ []) (CCZ124 ∷ Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ124 ∷ CCZ014 ∷ Toff104 ∷ CZ13 ∷ Toff104 ∷ CCZ014 ∷ CZ13 ∷ [])
  b0 = at 0 1 (CCZ124 ∷ Toff412 ∷ Bx1-403 ∷ Toff412 ∷ CCZ124 ∷ Bx1-403 ∷ []) (refl) ▸
       at 2 1 (CCZ014 ∷ Toff104 ∷ Bx4-13 ∷ Toff104 ∷ CCZ014 ∷ Bx4-13 ∷ []) (refl) ▸
       at 4 1 (CZ13 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 2 6 (CCZ034 ∷ []) (pw2 c4 (CCZ014 ∷ Toff104 ∷ CZ13 ∷ Toff104 ∷ CCZ014 ∷ CZ13 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ014 ∷ Toff104 ∷ Bx4-13 ∷ Toff104 ∷ CCZ014 ∷ Bx4-13 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 10 1 (CZ13 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ124 ∷ Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ124 ∷ CCZ014 ∷ Toff104 ∷ CZ13 ∷ Toff104 ∷ CCZ014 ∷ CZ13 ∷ []) (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ034 ∷ [])
  b1 = at 5 6 (CCZ034 ∷ []) (pw2 c4 (CCZ014 ∷ Toff104 ∷ CZ13 ∷ Toff104 ∷ CCZ014 ∷ CZ13 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Toff412 ∷ CCZ124 ∷ CZ12 ∷ []) (lw0 c4 (CCZ124 ∷ Toff412 ∷ []) (Toff412 ∷ CCZ124 ∷ CZ12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ034 ∷ CZ12 ∷ []) (lem-comm-CZ12-CCZ034 c4) ▸
       at 1 2 (CCZ034 ∷ CCZ124 ∷ []) (lem-cQ-at043043 c4) ▸
       at 2 4 (Toff412 ∷ []) (lw0 c4 (CCZ124 ∷ CZ12 ∷ Toff412 ∷ CCZ124 ∷ []) (Toff412 ∷ []) tt tt Eq.refl) ▸ done


-- tP @043043: 7 steps
lem-tP-at043043 : Complete 4 → ⟪ (Toff412 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ Toff412 ∷ []) ⟫ʷ
lem-tP-at043043 c4 = run b0
  where
  b0 : Chain (Toff412 ∷ Toff403 ∷ []) (Toff403 ∷ Toff412 ∷ [])
  b0 = at 0 1 (K4 ∷ CCZ124 ∷ K4⁻ ∷ []) (lw0 c4 (Toff412 ∷ []) (K4 ∷ CCZ124 ∷ K4⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 1 (K4 ∷ CCZ034 ∷ K4⁻ ∷ []) (pw1 c4 (Toff403 ∷ []) (K4 ∷ CCZ034 ∷ K4⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw0 c4 (K4⁻ ∷ K4 ∷ []) [] tt tt Eq.refl) ▸
       at 1 2 (CCZ034 ∷ CCZ124 ∷ []) (lem-cQ-at043043 c4) ▸
       at 2 0 (K4⁻ ∷ K4 ∷ []) (lw0 c4 [] (K4⁻ ∷ K4 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Toff403 ∷ []) (pw1 c4 (K4 ∷ CCZ034 ∷ K4⁻ ∷ []) (Toff403 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Toff412 ∷ []) (lw0 c4 (K4 ∷ CCZ124 ∷ K4⁻ ∷ []) (Toff412 ∷ []) tt tt Eq.refl) ▸ done


-- VPQ @043043: 14 steps
lem-VPQ-at043043 : Complete 4 → ⟪ (Toff412 ∷ CCZ124 ∷ Toff403 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CCZ034 ∷ Toff412 ∷ CCZ124 ∷ []) ⟫ʷ
lem-VPQ-at043043 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff412 ∷ CCZ124 ∷ Toff403 ∷ CCZ034 ∷ []) (CS03⁻ ∷ CS12⁻ ∷ S4 ∷ Toff403 ∷ Toff412 ∷ S4⁻ ∷ [])
  b0 = at 0 2 (CS12⁻ ∷ S4 ∷ Toff412 ∷ S4⁻ ∷ []) (lw0 c4 (Toff412 ∷ CCZ124 ∷ []) (CS12⁻ ∷ S4 ∷ Toff412 ∷ S4⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CS03⁻ ∷ S4 ∷ Toff403 ∷ S4⁻ ∷ []) (pw1 c4 (Toff403 ∷ CCZ034 ∷ []) (CS03⁻ ∷ S4 ∷ Toff403 ∷ S4⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CS03⁻ ∷ S4⁻ ∷ []) (sym (c₄ (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑) (S • S • S))) ▸
       at 2 2 (CS03⁻ ∷ Toff412 ∷ []) (lem-comm-TOFF412-CSd03 c4) ▸
       at 1 2 (CS03⁻ ∷ S4 ∷ []) (sym (c₄ (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑) (S))) ▸
       at 0 2 (CS03⁻ ∷ CS12⁻ ∷ []) (lw4 c4 (CS12⁻ ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw0 c4 (S4⁻ ∷ S4 ∷ []) [] tt tt Eq.refl) ▸
       at 3 2 (Toff403 ∷ Toff412 ∷ []) (lem-tP-at043043 c4) ▸ done

  b1 : Chain (CS03⁻ ∷ CS12⁻ ∷ S4 ∷ Toff403 ∷ Toff412 ∷ S4⁻ ∷ []) (Toff403 ∷ CCZ034 ∷ Toff412 ∷ CCZ124 ∷ [])
  b1 = at 4 0 (S4⁻ ∷ S4 ∷ []) (lw0 c4 [] (S4⁻ ∷ S4 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (S4 ∷ CS12⁻ ∷ []) (c₃ ((CS • CS • CS) ↑) (S ↑)) ▸
       at 2 2 (Toff403 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-TOFF403 c4) ▸
       at 3 2 (S4⁻ ∷ CS12⁻ ∷ []) (c₃ ((CS • CS • CS) ↑) ((S • S • S) ↑)) ▸
       at 0 4 (Toff403 ∷ CCZ034 ∷ []) (pw1 c4 (CS03⁻ ∷ S4 ∷ Toff403 ∷ S4⁻ ∷ []) (Toff403 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Toff412 ∷ CCZ124 ∷ []) (lw0 c4 (CS12⁻ ∷ S4 ∷ Toff412 ∷ S4⁻ ∷ []) (Toff412 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸ done


-- QVQ @043043: 3 steps
lem-QVQ-at043043 : Complete 4 → ⟪ (CCZ034 ∷ Toff412 ∷ CCZ124 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ Toff412 ∷ CCZ124 ∷ Toff403 ∷ []) ⟫ʷ
lem-QVQ-at043043 c4 = run b0
  where
  b0 : Chain (CCZ034 ∷ Toff412 ∷ CCZ124 ∷ CCZ034 ∷ []) (Toff403 ∷ Toff412 ∷ CCZ124 ∷ Toff403 ∷ [])
  b0 = at 0 0 (Toff403 ∷ Toff403 ∷ []) (pw1 c4 [] (Toff403 ∷ Toff403 ∷ []) tt tt Eq.refl) ▸
       at 1 4 (Toff412 ∷ CCZ124 ∷ Toff403 ∷ CCZ034 ∷ []) (sym (lem-VPQ-at043043 c4)) ▸
       at 4 2 [] (pw1 c4 (CCZ034 ∷ CCZ034 ∷ []) [] tt tt Eq.refl) ▸ done


-- box-cP @043043: 12 steps
lem-box-cP-at043043 : Complete 4 → ⟪ (Bx4-1203 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ []) ⟫ʷ
lem-box-cP-at043043 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx4-1203 ∷ []) (CCZ124 ∷ Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ124 ∷ CCZ014 ∷ Toff104 ∷ CZ13 ∷ Toff104 ∷ CCZ014 ∷ CZ13 ∷ [])
  b0 = at 0 1 (CCZ124 ∷ Toff412 ∷ Bx1-403 ∷ Toff412 ∷ CCZ124 ∷ Bx1-403 ∷ []) (refl) ▸
       at 2 1 (CCZ014 ∷ Toff104 ∷ Bx4-13 ∷ Toff104 ∷ CCZ014 ∷ Bx4-13 ∷ []) (refl) ▸
       at 4 1 (CZ13 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 2 6 (CCZ034 ∷ []) (pw2 c4 (CCZ014 ∷ Toff104 ∷ CZ13 ∷ Toff104 ∷ CCZ014 ∷ CZ13 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ014 ∷ Toff104 ∷ Bx4-13 ∷ Toff104 ∷ CCZ014 ∷ Bx4-13 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 10 1 (CZ13 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ124 ∷ Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ124 ∷ CCZ014 ∷ Toff104 ∷ CZ13 ∷ Toff104 ∷ CCZ014 ∷ CZ13 ∷ []) (CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ [])
  b1 = at 5 6 (CCZ034 ∷ []) (pw2 c4 (CCZ014 ∷ Toff104 ∷ CZ13 ∷ Toff104 ∷ CCZ014 ∷ CZ13 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Toff403 ∷ Toff412 ∷ CCZ124 ∷ Toff403 ∷ []) (lem-QVQ-at043043 c4) ▸
       at 1 2 (Toff403 ∷ Toff412 ∷ []) (lem-tP-at043043 c4) ▸
       at 2 2 [] (lw0 c4 (Toff412 ∷ Toff412 ∷ []) [] tt tt Eq.refl) ▸ done


-- CSdu-box-3 @043043: 17 steps
lem-CSdu-box-3-at043043 : Complete 4 → ⟪ (CS04⁻ ∷ Bx4-1203 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1203 ∷ CS04⁻ ∷ []) ⟫ʷ
lem-CSdu-box-3-at043043 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS04⁻ ∷ Bx4-1203 ∷ []) (CCZ124 ∷ Toff403 ∷ CS04⁻ ∷ CS03⁻ ∷ CS03 ∷ CCZ124 ∷ CX40 ∷ CS03⁻ ∷ CX40 ∷ CS34 ∷ Toff403 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ []) (lem-box-cP-at043043 c4) ▸
       at 0 2 (CCZ124 ∷ CS04⁻ ∷ []) (pw3 c4 (CS04⁻ ∷ CCZ124 ∷ []) (CCZ124 ∷ CS04⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff403 ∷ CS04⁻ ∷ CS03⁻ ∷ CCZ034 ∷ []) (pw1 c4 (CS04⁻ ∷ Toff403 ∷ []) (Toff403 ∷ CS04⁻ ∷ CS03⁻ ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CS03 ∷ CX40 ∷ CS03⁻ ∷ CX40 ∷ CS34 ∷ []) (pw1 c4 (CCZ034 ∷ []) (CS03 ∷ CX40 ∷ CS03⁻ ∷ CX40 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ124 ∷ CS34 ∷ []) (lw0 c4 (CS34 ∷ CCZ124 ∷ []) (CCZ124 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ124 ∷ CX40 ∷ []) (pw3 c4 (CX40 ∷ CCZ124 ∷ []) (CCZ124 ∷ CX40 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ124 ∷ CS03⁻ ∷ []) (lem-comm-CSd03-CCZ124 c4) ▸
       at 5 2 (CCZ124 ∷ CX40 ∷ []) (pw3 c4 (CX40 ∷ CCZ124 ∷ []) (CCZ124 ∷ CX40 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CCZ124 ∷ Toff403 ∷ CS04⁻ ∷ CS03⁻ ∷ CS03 ∷ CCZ124 ∷ CX40 ∷ CS03⁻ ∷ CX40 ∷ CS34 ∷ Toff403 ∷ []) (CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ CS04⁻ ∷ [])
  b1 = at 4 2 (CCZ124 ∷ CS03 ∷ []) (lem-comm-CS03-CCZ124 c4) ▸
       at 5 5 (CCZ034 ∷ []) (pw1 c4 (CS03 ∷ CX40 ∷ CS03⁻ ∷ CX40 ∷ CS34 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ124 ∷ CS03⁻ ∷ []) (lem-comm-CSd03-CCZ124 c4) ▸
       at 2 2 (CCZ124 ∷ CS04⁻ ∷ []) (pw3 c4 (CS04⁻ ∷ CCZ124 ∷ []) (CCZ124 ∷ CS04⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff403 ∷ CZ03 ∷ CCZ034 ∷ []) (pw1 c4 (CCZ034 ∷ Toff403 ∷ []) (Toff403 ∷ CZ03 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff403 ∷ CS03⁻ ∷ []) (pw1 c4 (CS03⁻ ∷ Toff403 ∷ []) (Toff403 ∷ CS03⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff403 ∷ CS04⁻ ∷ CS03⁻ ∷ CCZ034 ∷ []) (pw1 c4 (CS04⁻ ∷ Toff403 ∷ []) (Toff403 ∷ CS04⁻ ∷ CS03⁻ ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 4 6 (CS04⁻ ∷ []) (pw1 c4 (CS04⁻ ∷ CS03⁻ ∷ CCZ034 ∷ CS03⁻ ∷ CZ03 ∷ CCZ034 ∷ []) (CS04⁻ ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ CS04⁻ ∷ []) (Bx4-1203 ∷ CS04⁻ ∷ [])
  b2 = at 0 4 (Bx4-1203 ∷ []) (sym (lem-box-cP-at043043 c4)) ▸ done


-- F0-R: 11 steps
lem-F0-R : Complete 4 → ⟪ (CX34 ∷ Toff412 ∷ CS04 ∷ Toff412 ∷ CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ CS04 ∷ Toff412 ∷ CS04⁻ ∷ Bx4-1203 ∷ CX34 ∷ []) ⟫ʷ
lem-F0-R c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CX34 ∷ Toff412 ∷ CS04 ∷ Toff412 ∷ CS04⁻ ∷ []) (Toff412 ∷ CS04 ∷ Toff412 ∷ Toff412 ∷ CCZ034 ∷ Toff412 ∷ CS04⁻ ∷ CCZ034 ∷ CX34 ∷ [])
  b0 = at 0 2 (Toff412 ∷ CX34 ∷ []) (lw0 c4 (CX34 ∷ Toff412 ∷ []) (Toff412 ∷ CX34 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS04 ∷ CS03 ∷ CCZ034 ∷ CX34 ∷ []) (pw1 c4 (CX34 ∷ CS04 ∷ []) (CS04 ∷ CS03 ∷ CCZ034 ∷ CX34 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff412 ∷ CX34 ∷ []) (lw0 c4 (CX34 ∷ Toff412 ∷ []) (Toff412 ∷ CX34 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CS04⁻ ∷ CS03⁻ ∷ CCZ034 ∷ CX34 ∷ []) (pw1 c4 (CX34 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ CS03⁻ ∷ CCZ034 ∷ CX34 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ034 ∷ CS03 ∷ []) (pw1 c4 (CS03 ∷ CCZ034 ∷ []) (CCZ034 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff412 ∷ CS03 ∷ []) (lem-comm-CS03-TOFF412 c4) ▸
       at 4 3 (CS04⁻ ∷ []) (pw1 c4 (CS03 ∷ CS04⁻ ∷ CS03⁻ ∷ []) (CS04⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 0 (Toff412 ∷ Toff412 ∷ []) (lw0 c4 [] (Toff412 ∷ Toff412 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Toff412 ∷ CS04 ∷ Toff412 ∷ Toff412 ∷ CCZ034 ∷ Toff412 ∷ CS04⁻ ∷ CCZ034 ∷ CX34 ∷ []) (Toff412 ∷ CS04 ∷ Toff412 ∷ CS04⁻ ∷ Bx4-1203 ∷ CX34 ∷ [])
  b1 = at 6 2 (CCZ034 ∷ CS04⁻ ∷ []) (pw1 c4 (CS04⁻ ∷ CCZ034 ∷ []) (CCZ034 ∷ CS04⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 4 (Bx4-1203 ∷ []) (sym (lem-box-tQ-at043043 c4)) ▸
       at 3 2 (CS04⁻ ∷ Bx4-1203 ∷ []) (sym (lem-CSdu-box-3-at043043 c4)) ▸ done

