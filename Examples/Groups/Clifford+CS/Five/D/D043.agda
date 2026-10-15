{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D043 where

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
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-box-cP-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D006 using (lem-box-tQ-at122331 ; lem-sym-ab-at122331)
open import Examples.Groups.Clifford+CS.Five.D.D010 using (lem-box-tQ-at1331)
open import Examples.Groups.Clifford+CS.Five.D.D022 using (lem-box-tQ-at032032 ; lem-cQ-at032032)
open import Examples.Groups.Clifford+CS.Five.D.D042 using (lem-P-box-at243243)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-comm-CSd14-TOFF023)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-comm-CX24-CCZ013 ; lem-comm-CZ24-CCZ013)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-comm-CX32-CCZ014)
open import Examples.Groups.Clifford+CS.Five.D.R012 using (lem-comm-CS14-TOFF023 ; lem-comm-TOFF301-CSd24)
open import Examples.Groups.Clifford+CS.Five.D.R017 using (lem-comm-CZ24-TOFF301)
-- pairs @243243: 4 steps
lem-pairs-at243243 : Complete 4 → ⟪ (Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2314 ∷ []) ⟫ʷ
lem-pairs-at243243 c4 = run b0
  where
  b0 : Chain (Bx0-1423 ∷ []) (Bx0-2314 ∷ [])
  b0 = at 0 1 (Toff023 ∷ Bx0-1423 ∷ Toff023 ∷ []) (sym (lem-P-box-at243243 c4)) ▸
       at 1 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 4 2 [] (lw4 c4 (Toff023 ∷ Toff023 ∷ []) [] tt tt Eq.refl) ▸
       at 0 4 (Bx0-2314 ∷ []) (sym (lem-box-tQ-at122331 c4)) ▸ done


-- CXbc-box @1331: 17 steps
lem-CXbc-box-at1331 : Complete 4 → ⟪ (CX21 ∷ Bx0-3214 ∷ CX21 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3214 ∷ CCZ234 ∷ []) ⟫ʷ
lem-CXbc-box-at1331 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX21 ∷ Bx0-3214 ∷ CX21 ∷ []) (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CX21 ∷ CCZ024 ∷ CS24 ∷ CX32 ∷ CS24⁻ ∷ CCZ014 ∷ CX32 ∷ CS34 ∷ CX21 ∷ [])
  b0 = at 1 1 (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ []) (lem-box-tQ-at1331 c4) ▸
       at 0 2 (Toff023 ∷ CX21 ∷ []) (lw4 c4 (CX21 ∷ Toff023 ∷ []) (Toff023 ∷ CX21 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ014 ∷ CX21 ∷ CCZ024 ∷ []) (pw3 c4 (CX21 ∷ CCZ014 ∷ []) (CCZ014 ∷ CX21 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff023 ∷ CCZ024 ∷ CCZ234 ∷ []) (pw1 c4 (CCZ024 ∷ Toff023 ∷ []) (Toff023 ∷ CCZ024 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff023 ∷ CX21 ∷ []) (lw4 c4 (CX21 ∷ Toff023 ∷ []) (Toff023 ∷ CX21 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ []) (lw0 c4 (CCZ234 ∷ []) (CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ014 ∷ CS34 ∷ []) (pw2 c4 (CS34 ∷ CCZ014 ∷ []) (CCZ014 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ014 ∷ CX32 ∷ []) (lem-comm-CX32-CCZ014 c4) ▸ done

  b1 : Chain (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CX21 ∷ CCZ024 ∷ CS24 ∷ CX32 ∷ CS24⁻ ∷ CCZ014 ∷ CX32 ∷ CS34 ∷ CX21 ∷ []) (Bx0-3214 ∷ CX21 ∷ CCZ234 ∷ CX21 ∷ [])
  b1 = at 7 2 (CCZ014 ∷ CS24⁻ ∷ []) (pw3 c4 (CS24⁻ ∷ CCZ014 ∷ []) (CCZ014 ∷ CS24⁻ ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ014 ∷ CX32 ∷ []) (lem-comm-CX32-CCZ014 c4) ▸
       at 5 2 (CCZ014 ∷ CS24 ∷ []) (pw3 c4 (CS24 ∷ CCZ014 ∷ []) (CCZ014 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 6 5 (CCZ234 ∷ []) (lw0 c4 (CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ014 ∷ CCZ024 ∷ []) (pw3 c4 (CCZ024 ∷ CCZ014 ∷ []) (CCZ014 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ014 ∷ CX21 ∷ CCZ024 ∷ []) (pw3 c4 (CX21 ∷ CCZ014 ∷ []) (CCZ014 ∷ CX21 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CX21 ∷ []) (pw3 c4 (CX21 ∷ CCZ024 ∷ CCZ024 ∷ []) (CX21 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx0-3214 ∷ []) (sym (lem-box-tQ-at1331 c4)) ▸ done

  b2 : Chain (Bx0-3214 ∷ CX21 ∷ CCZ234 ∷ CX21 ∷ []) (Bx0-3214 ∷ CCZ234 ∷ [])
  b2 = at 1 3 (CCZ234 ∷ []) (lw0 c4 (CX21 ∷ CCZ234 ∷ CX21 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸ done


-- CXcb-box @1331: 18 steps
lem-CXcb-box-at1331 : Complete 4 → ⟪ (CX12 ∷ Bx0-3214 ∷ CX12 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3214 ∷ CCZ134 ∷ []) ⟫ʷ
lem-CXcb-box-at1331 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX12 ∷ Bx0-3214 ∷ CX12 ∷ []) (Toff023 ∷ CCZ014 ∷ CX12 ∷ Toff013 ∷ CS14 ∷ CX31 ∷ Toff023 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ CCZ014 ∷ CX12 ∷ [])
  b0 = at 1 1 (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ []) (lem-box-tQ-at1331 c4) ▸
       at 0 2 (Toff023 ∷ CX12 ∷ Toff013 ∷ []) (lw4 c4 (CX12 ∷ Toff023 ∷ []) (Toff023 ∷ CX12 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ014 ∷ Toff013 ∷ CCZ134 ∷ []) (pw2 c4 (Toff013 ∷ CCZ014 ∷ []) (CCZ014 ∷ Toff013 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ014 ∷ CX12 ∷ []) (pw3 c4 (CX12 ∷ CCZ014 ∷ []) (CCZ014 ∷ CX12 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ []) (lw0 c4 (CCZ134 ∷ []) (CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (Toff023 ∷ CS34 ∷ []) (pw1 c4 (CS34 ∷ Toff023 ∷ []) (Toff023 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff023 ∷ CX31 ∷ []) (lw4 c4 (CX31 ∷ Toff023 ∷ []) (Toff023 ∷ CX31 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Toff023 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-TOFF023 c4) ▸ done

  b1 : Chain (Toff023 ∷ CCZ014 ∷ CX12 ∷ Toff013 ∷ CS14 ∷ CX31 ∷ Toff023 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ CCZ014 ∷ CX12 ∷ []) (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ CX12 ∷ CCZ134 ∷ CX12 ∷ [])
  b1 = at 5 2 (Toff023 ∷ CX31 ∷ []) (lw4 c4 (CX31 ∷ Toff023 ∷ []) (Toff023 ∷ CX31 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff023 ∷ CS14 ∷ []) (lem-comm-CS14-TOFF023 c4) ▸
       at 5 5 (CCZ134 ∷ []) (lw0 c4 (CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff023 ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ Toff023 ∷ []) (Toff023 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff023 ∷ CX12 ∷ Toff013 ∷ []) (lw4 c4 (CX12 ∷ Toff023 ∷ []) (Toff023 ∷ CX12 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CX12 ∷ []) (lw4 c4 (CX12 ∷ Toff013 ∷ Toff013 ∷ []) (CX12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ014 ∷ CCZ134 ∷ []) (pw2 c4 (CCZ134 ∷ CCZ014 ∷ []) (CCZ014 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ014 ∷ CX12 ∷ []) (pw3 c4 (CX12 ∷ CCZ014 ∷ []) (CCZ014 ∷ CX12 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ CX12 ∷ CCZ134 ∷ CX12 ∷ []) (Bx0-3214 ∷ CCZ134 ∷ [])
  b2 = at 0 4 (Bx0-3214 ∷ []) (sym (lem-box-tQ-at1331 c4)) ▸
       at 1 3 (CCZ134 ∷ []) (lw0 c4 (CX12 ∷ CCZ134 ∷ CX12 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl) ▸ done


-- SWbc-box @1331: 11 steps
lem-SWbc-box-at1331 : Complete 4 → ⟪ (Sw12 ∷ Bx0-3214 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3214 ∷ []) ⟫ʷ
lem-SWbc-box-at1331 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw12 ∷ Bx0-3214 ∷ Sw12 ∷ []) (CX21 ∷ Bx0-3214 ∷ CX21 ∷ CCZ234 ∷ CCZ134 ∷ CCZ234 ∷ CCZ134 ∷ CCZ234 ∷ [])
  b0 = at 0 1 (CX21 ∷ CX12 ∷ CX21 ∷ []) (lw4 c4 (Sw12 ∷ []) (CX21 ∷ CX12 ∷ CX21 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CX21 ∷ CX12 ∷ CX21 ∷ []) (lw4 c4 (Sw12 ∷ []) (CX21 ∷ CX12 ∷ CX21 ∷ []) tt tt Eq.refl) ▸
       at 2 3 (Bx0-3214 ∷ CCZ234 ∷ []) (lem-CXbc-box-at1331 c4) ▸
       at 3 2 (CX12 ∷ CCZ134 ∷ CCZ234 ∷ []) (lw0 c4 (CCZ234 ∷ CX12 ∷ []) (CX12 ∷ CCZ134 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Bx0-3214 ∷ CCZ134 ∷ []) (lem-CXcb-box-at1331 c4) ▸
       at 4 2 (CX21 ∷ CCZ234 ∷ []) (lw0 c4 (CCZ234 ∷ CX21 ∷ []) (CX21 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CX21 ∷ CCZ234 ∷ CCZ134 ∷ []) (lw0 c4 (CCZ134 ∷ CX21 ∷ []) (CX21 ∷ CCZ234 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CX21 ∷ CCZ234 ∷ CCZ134 ∷ []) (lw0 c4 (CCZ134 ∷ CX21 ∷ []) (CX21 ∷ CCZ234 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CX21 ∷ Bx0-3214 ∷ CX21 ∷ CCZ234 ∷ CCZ134 ∷ CCZ234 ∷ CCZ134 ∷ CCZ234 ∷ []) (Bx0-3214 ∷ [])
  b1 = at 3 5 (CCZ234 ∷ []) (lw0 c4 (CCZ234 ∷ CCZ134 ∷ CCZ234 ∷ CCZ134 ∷ CCZ234 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Bx0-3214 ∷ CCZ234 ∷ []) (lem-CXbc-box-at1331 c4) ▸
       at 1 2 [] (lw0 c4 (CCZ234 ∷ CCZ234 ∷ []) [] tt tt Eq.refl) ▸ done


-- nat-SWbc @1331: 23 steps
lem-nat-SWbc-at1331 : Complete 4 → ⟪ (Sw12 ∷ Bx0-3214 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3124 ∷ []) ⟫ʷ
lem-nat-SWbc-at1331 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw12 ∷ Bx0-3214 ∷ Sw12 ∷ []) (CCZ013 ∷ Toff013 ∷ CCZ023 ∷ Toff302 ∷ Bx0-34 ∷ Toff302 ∷ Sw12 ∷ CCZ013 ∷ Bx0-34 ∷ Toff023 ∷ CCZ023 ∷ Bx3-014 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff023 ∷ Bx3-014 ∷ Toff023 ∷ CCZ023 ∷ Bx3-014 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ023 ∷ []) (CCZ013 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff013 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff023 ∷ []) (Toff013 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (CCZ013 ∷ Toff301 ∷ Bx0-34 ∷ Toff301 ∷ CCZ013 ∷ Bx0-34 ∷ []) (refl) ▸
       at 2 2 (CCZ023 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ013 ∷ []) (CCZ023 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff302 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff301 ∷ []) (Toff302 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Bx0-34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CZ)) ▸
       at 5 2 (Toff302 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff301 ∷ []) (Toff302 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CCZ013 ∷ Toff013 ∷ CCZ023 ∷ Toff302 ∷ Bx0-34 ∷ Toff302 ∷ Sw12 ∷ CCZ013 ∷ Bx0-34 ∷ Toff023 ∷ CCZ023 ∷ Bx3-014 ∷ Sw12 ∷ []) (CCZ013 ∷ Toff013 ∷ CCZ023 ∷ Toff302 ∷ Bx0-34 ∷ Toff302 ∷ CCZ023 ∷ Bx0-34 ∷ Toff013 ∷ CCZ013 ∷ CCZ023 ∷ Toff302 ∷ Bx0-34 ∷ Sw12 ∷ Toff301 ∷ CCZ013 ∷ Bx0-34 ∷ Sw12 ∷ [])
  b1 = at 6 2 (CCZ023 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ013 ∷ []) (CCZ023 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Bx0-34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CZ)) ▸
       at 8 2 (Toff013 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff023 ∷ []) (Toff013 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ013 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ023 ∷ []) (CCZ013 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 11 1 (CCZ013 ∷ Toff301 ∷ Bx0-34 ∷ Toff301 ∷ CCZ013 ∷ Bx0-34 ∷ []) (refl) ▸
       at 10 2 (CCZ023 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ013 ∷ []) (CCZ023 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (Toff302 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff301 ∷ []) (Toff302 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (Bx0-34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CZ)) ▸ done

  b2 : Chain (CCZ013 ∷ Toff013 ∷ CCZ023 ∷ Toff302 ∷ Bx0-34 ∷ Toff302 ∷ CCZ023 ∷ Bx0-34 ∷ Toff013 ∷ CCZ013 ∷ CCZ023 ∷ Toff302 ∷ Bx0-34 ∷ Sw12 ∷ Toff301 ∷ CCZ013 ∷ Bx0-34 ∷ Sw12 ∷ []) (Bx0-3124 ∷ [])
  b2 = at 13 2 (Toff302 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ Toff301 ∷ []) (Toff302 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 14 2 (CCZ023 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CCZ013 ∷ []) (CCZ023 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 15 2 (Bx0-34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CZ)) ▸
       at 16 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸
       at 2 6 (Bx3-024 ∷ []) (refl) ▸
       at 5 6 (Bx3-024 ∷ []) (refl) ▸
       at 0 6 (Bx0-3124 ∷ []) (refl) ▸ done


-- sym-bc @1331: 2 steps
lem-sym-bc-at1331 : Complete 4 → ⟪ (Bx0-3214 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3124 ∷ []) ⟫ʷ
lem-sym-bc-at1331 c4 = run b0
  where
  b0 : Chain (Bx0-3214 ∷ []) (Bx0-3124 ∷ [])
  b0 = at 0 1 (Sw12 ∷ Bx0-3214 ∷ Sw12 ∷ []) (sym (lem-SWbc-box-at1331 c4)) ▸
       at 0 3 (Bx0-3124 ∷ []) (lem-nat-SWbc-at1331 c4) ▸ done


-- box-perm-4132 @243243: 3 steps
lem-box-perm-4132-at243243 : Complete 4 → ⟪ (Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3124 ∷ []) ⟫ʷ
lem-box-perm-4132-at243243 c4 = run b0
  where
  b0 : Chain (Bx0-1423 ∷ []) (Bx0-3124 ∷ [])
  b0 = at 0 1 (Bx0-2314 ∷ []) (lem-pairs-at243243 c4) ▸
       at 0 1 (Bx0-3214 ∷ []) (lem-sym-ab-at122331 c4) ▸
       at 0 1 (Bx0-3124 ∷ []) (lem-sym-bc-at1331 c4) ▸ done


-- tP @032032: 7 steps
lem-tP-at032032 : Complete 4 → ⟪ (Toff301 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ Toff301 ∷ []) ⟫ʷ
lem-tP-at032032 c4 = run b0
  where
  b0 : Chain (Toff301 ∷ Toff324 ∷ []) (Toff324 ∷ Toff301 ∷ [])
  b0 = at 0 1 (K3 ∷ CCZ013 ∷ K3⁻ ∷ []) (lw4 c4 (Toff301 ∷ []) (K3 ∷ CCZ013 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 1 (K3 ∷ CCZ234 ∷ K3⁻ ∷ []) (lw0 c4 (Toff324 ∷ []) (K3 ∷ CCZ234 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (K3⁻ ∷ K3 ∷ []) [] tt tt Eq.refl) ▸
       at 1 2 (CCZ234 ∷ CCZ013 ∷ []) (lem-cQ-at032032 c4) ▸
       at 2 0 (K3⁻ ∷ K3 ∷ []) (lw4 c4 [] (K3⁻ ∷ K3 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Toff324 ∷ []) (lw0 c4 (K3 ∷ CCZ234 ∷ K3⁻ ∷ []) (Toff324 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Toff301 ∷ []) (lw4 c4 (K3 ∷ CCZ013 ∷ K3⁻ ∷ []) (Toff301 ∷ []) tt tt Eq.refl) ▸ done


-- P-box @032032: 8 steps
lem-P-box-at032032 : Complete 4 → ⟪ (Toff324 ∷ Bx3-1024 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1024 ∷ []) ⟫ʷ
lem-P-box-at032032 c4 = run b0
  where
  b0 : Chain (Toff324 ∷ Bx3-1024 ∷ Toff324 ∷ []) (Bx3-1024 ∷ [])
  b0 = at 1 1 (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ []) (lem-box-tQ-at032032 c4) ▸
       at 0 2 (Toff301 ∷ Toff324 ∷ []) (sym (lem-tP-at032032 c4)) ▸
       at 1 2 (CCZ234 ∷ CZ24 ∷ Toff324 ∷ []) (lw0 c4 (Toff324 ∷ CCZ234 ∷ []) (CCZ234 ∷ CZ24 ∷ Toff324 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff301 ∷ Toff324 ∷ []) (sym (lem-tP-at032032 c4)) ▸
       at 4 3 (CCZ234 ∷ CZ24 ∷ []) (lw0 c4 (Toff324 ∷ CCZ234 ∷ Toff324 ∷ []) (CCZ234 ∷ CZ24 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff301 ∷ CZ24 ∷ []) (lem-comm-CZ24-TOFF301 c4) ▸
       at 3 3 (CCZ234 ∷ []) (lw0 c4 (CZ24 ∷ CCZ234 ∷ CZ24 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx3-1024 ∷ []) (sym (lem-box-tQ-at032032 c4)) ▸ done


-- VPQ @032032: 14 steps
lem-VPQ-at032032 : Complete 4 → ⟪ (Toff301 ∷ CCZ013 ∷ Toff324 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CCZ234 ∷ Toff301 ∷ CCZ013 ∷ []) ⟫ʷ
lem-VPQ-at032032 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff301 ∷ CCZ013 ∷ Toff324 ∷ CCZ234 ∷ []) (CS24⁻ ∷ CS01⁻ ∷ S3 ∷ Toff324 ∷ Toff301 ∷ S3⁻ ∷ [])
  b0 = at 0 2 (CS01⁻ ∷ S3 ∷ Toff301 ∷ S3⁻ ∷ []) (lw4 c4 (Toff301 ∷ CCZ013 ∷ []) (CS01⁻ ∷ S3 ∷ Toff301 ∷ S3⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CS24⁻ ∷ S3 ∷ Toff324 ∷ S3⁻ ∷ []) (lw0 c4 (Toff324 ∷ CCZ234 ∷ []) (CS24⁻ ∷ S3 ∷ Toff324 ∷ S3⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CS24⁻ ∷ S3⁻ ∷ []) (lw0 c4 (S3⁻ ∷ CS24⁻ ∷ []) (CS24⁻ ∷ S3⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CS24⁻ ∷ Toff301 ∷ []) (lem-comm-TOFF301-CSd24 c4) ▸
       at 1 2 (CS24⁻ ∷ S3 ∷ []) (lw0 c4 (S3 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ S3 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (CS24⁻ ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (Swap ↑ • (CS • CS • CS) • Swap ↑)) ▸
       at 4 2 [] (lw4 c4 (S3⁻ ∷ S3 ∷ []) [] tt tt Eq.refl) ▸
       at 3 2 (Toff324 ∷ Toff301 ∷ []) (lem-tP-at032032 c4) ▸ done

  b1 : Chain (CS24⁻ ∷ CS01⁻ ∷ S3 ∷ Toff324 ∷ Toff301 ∷ S3⁻ ∷ []) (Toff324 ∷ CCZ234 ∷ Toff301 ∷ CCZ013 ∷ [])
  b1 = at 4 0 (S3⁻ ∷ S3 ∷ []) (lw4 c4 [] (S3⁻ ∷ S3 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (S3 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (S ↑)) ▸
       at 2 2 (Toff324 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 3 2 (S3⁻ ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) ((S • S • S) ↑)) ▸
       at 0 4 (Toff324 ∷ CCZ234 ∷ []) (lw0 c4 (CS24⁻ ∷ S3 ∷ Toff324 ∷ S3⁻ ∷ []) (Toff324 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Toff301 ∷ CCZ013 ∷ []) (lw4 c4 (CS01⁻ ∷ S3 ∷ Toff301 ∷ S3⁻ ∷ []) (Toff301 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸ done


-- QVQ @032032: 3 steps
lem-QVQ-at032032 : Complete 4 → ⟪ (CCZ234 ∷ Toff301 ∷ CCZ013 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ Toff301 ∷ CCZ013 ∷ Toff324 ∷ []) ⟫ʷ
lem-QVQ-at032032 c4 = run b0
  where
  b0 : Chain (CCZ234 ∷ Toff301 ∷ CCZ013 ∷ CCZ234 ∷ []) (Toff324 ∷ Toff301 ∷ CCZ013 ∷ Toff324 ∷ [])
  b0 = at 0 0 (Toff324 ∷ Toff324 ∷ []) (lw0 c4 [] (Toff324 ∷ Toff324 ∷ []) tt tt Eq.refl) ▸
       at 1 4 (Toff301 ∷ CCZ013 ∷ Toff324 ∷ CCZ234 ∷ []) (sym (lem-VPQ-at032032 c4)) ▸
       at 4 2 [] (lw0 c4 (CCZ234 ∷ CCZ234 ∷ []) [] tt tt Eq.refl) ▸ done


-- box-cP @032032: 12 steps
lem-box-cP-at032032 : Complete 4 → ⟪ (Bx3-1024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ []) ⟫ʷ
lem-box-cP-at032032 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-1024 ∷ []) (CCZ013 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ013 ∷ CCZ123 ∷ Toff123 ∷ CZ14 ∷ Toff123 ∷ CCZ123 ∷ CZ14 ∷ [])
  b0 = at 0 1 (CCZ013 ∷ Toff301 ∷ Bx1-324 ∷ Toff301 ∷ CCZ013 ∷ Bx1-324 ∷ []) (refl) ▸
       at 2 1 (CCZ123 ∷ Toff123 ∷ Bx3-14 ∷ Toff123 ∷ CCZ123 ∷ Bx3-14 ∷ []) (refl) ▸
       at 4 1 (CZ14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 2 6 (CCZ234 ∷ []) (lw0 c4 (CCZ123 ∷ Toff123 ∷ CZ14 ∷ Toff123 ∷ CCZ123 ∷ CZ14 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ123 ∷ Toff123 ∷ Bx3-14 ∷ Toff123 ∷ CCZ123 ∷ Bx3-14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 10 1 (CZ14 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ013 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ013 ∷ CCZ123 ∷ Toff123 ∷ CZ14 ∷ Toff123 ∷ CCZ123 ∷ CZ14 ∷ []) (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ [])
  b1 = at 5 6 (CCZ234 ∷ []) (lw0 c4 (CCZ123 ∷ Toff123 ∷ CZ14 ∷ Toff123 ∷ CCZ123 ∷ CZ14 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Toff324 ∷ Toff301 ∷ CCZ013 ∷ Toff324 ∷ []) (lem-QVQ-at032032 c4) ▸
       at 1 2 (Toff324 ∷ Toff301 ∷ []) (lem-tP-at032032 c4) ▸
       at 2 2 [] (lw4 c4 (Toff301 ∷ Toff301 ∷ []) [] tt tt Eq.refl) ▸ done


-- cQ @0312243140: 7 steps
lem-cQ-at0312243140 : Complete 4 → ⟪ (CCZ234 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ CCZ234 ∷ []) ⟫ʷ
lem-cQ-at0312243140 c4 = run b0
  where
  b0 : Chain (CCZ234 ∷ CCZ013 ∷ []) (CCZ013 ∷ CCZ234 ∷ [])
  b0 = at 0 1 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (lw0 c4 (CCZ234 ∷ []) (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ013 ∷ CS23 ∷ []) (lw4 c4 (CS23 ∷ CCZ013 ∷ []) (CCZ013 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ013 ∷ CX24 ∷ []) (lem-comm-CX24-CCZ013 c4) ▸
       at 2 2 (CCZ013 ∷ CS34⁻ ∷ []) (pw2 c4 (CS34⁻ ∷ CCZ013 ∷ []) (CCZ013 ∷ CS34⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ013 ∷ CX24 ∷ []) (lem-comm-CX24-CCZ013 c4) ▸
       at 0 2 (CCZ013 ∷ CS34 ∷ []) (pw2 c4 (CS34 ∷ CCZ013 ∷ []) (CCZ013 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 1 5 (CCZ234 ∷ []) (lw0 c4 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸ done


-- box-tQ @0312243140: 13 steps
lem-box-tQ-at0312243140 : Complete 4 → ⟪ (Bx3-2410 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ []) ⟫ʷ
lem-box-tQ-at0312243140 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-2410 ∷ []) (CCZ234 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ234 ∷ CCZ123 ∷ Toff213 ∷ CZ02 ∷ Toff213 ∷ CCZ123 ∷ CZ02 ∷ [])
  b0 = at 0 1 (CCZ234 ∷ Toff324 ∷ Bx2-310 ∷ Toff324 ∷ CCZ234 ∷ Bx2-310 ∷ []) (refl) ▸
       at 2 1 (CCZ123 ∷ Toff213 ∷ Bx3-20 ∷ Toff213 ∷ CCZ123 ∷ Bx3-20 ∷ []) (refl) ▸
       at 4 1 (CZ02 ∷ []) (refl) ▸
       at 7 1 (CZ02 ∷ []) (refl) ▸
       at 2 6 (CCZ013 ∷ []) (lw4 c4 (CCZ123 ∷ Toff213 ∷ CZ02 ∷ Toff213 ∷ CCZ123 ∷ CZ02 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ123 ∷ Toff213 ∷ Bx3-20 ∷ Toff213 ∷ CCZ123 ∷ Bx3-20 ∷ []) (refl) ▸
       at 7 1 (CZ02 ∷ []) (refl) ▸
       at 10 1 (CZ02 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ234 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ234 ∷ CCZ123 ∷ Toff213 ∷ CZ02 ∷ Toff213 ∷ CCZ123 ∷ CZ02 ∷ []) (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ [])
  b1 = at 5 6 (CCZ013 ∷ []) (lw4 c4 (CCZ123 ∷ Toff213 ∷ CZ02 ∷ Toff213 ∷ CCZ123 ∷ CZ02 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Toff324 ∷ CCZ234 ∷ CZ24 ∷ []) (lw0 c4 (CCZ234 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ234 ∷ CZ24 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ013 ∷ CZ24 ∷ []) (lem-comm-CZ24-CCZ013 c4) ▸
       at 1 2 (CCZ013 ∷ CCZ234 ∷ []) (lem-cQ-at0312243140 c4) ▸
       at 2 4 (Toff324 ∷ []) (lw0 c4 (CCZ234 ∷ CZ24 ∷ Toff324 ∷ CCZ234 ∷ []) (Toff324 ∷ []) tt tt Eq.refl) ▸ done


-- pairs @032032: 4 steps
lem-pairs-at032032 : Complete 4 → ⟪ (Bx3-1024 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2410 ∷ []) ⟫ʷ
lem-pairs-at032032 c4 = run b0
  where
  b0 : Chain (Bx3-1024 ∷ []) (Bx3-2410 ∷ [])
  b0 = at 0 1 (Toff324 ∷ Bx3-1024 ∷ Toff324 ∷ []) (sym (lem-P-box-at032032 c4)) ▸
       at 1 1 (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ []) (lem-box-cP-at032032 c4) ▸
       at 4 2 [] (lw0 c4 (Toff324 ∷ Toff324 ∷ []) [] tt tt Eq.refl) ▸
       at 0 4 (Bx3-2410 ∷ []) (sym (lem-box-tQ-at0312243140 c4)) ▸ done


-- CXbc-box @0312243140: 17 steps
lem-CXbc-box-at0312243140 : Complete 4 → ⟪ (CX41 ∷ Bx3-2410 ∷ CX41 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2410 ∷ CCZ024 ∷ []) ⟫ʷ
lem-CXbc-box-at0312243140 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX41 ∷ Bx3-2410 ∷ CX41 ∷ []) (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CX41 ∷ CCZ034 ∷ CS04 ∷ CX24 ∷ CS04⁻ ∷ CCZ013 ∷ CX24 ∷ CS02 ∷ CX41 ∷ [])
  b0 = at 1 1 (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ []) (lem-box-tQ-at0312243140 c4) ▸
       at 0 2 (Toff324 ∷ CX41 ∷ []) (lw0 c4 (CX41 ∷ Toff324 ∷ []) (Toff324 ∷ CX41 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ013 ∷ CX41 ∷ CCZ034 ∷ []) (pw2 c4 (CX41 ∷ CCZ013 ∷ []) (CCZ013 ∷ CX41 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff324 ∷ CCZ034 ∷ CCZ024 ∷ []) (pw1 c4 (CCZ034 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ034 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff324 ∷ CX41 ∷ []) (lw0 c4 (CX41 ∷ Toff324 ∷ []) (Toff324 ∷ CX41 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CS04 ∷ CX24 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ []) (pw1 c4 (CCZ024 ∷ []) (CS04 ∷ CX24 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ013 ∷ CS02 ∷ []) (lw4 c4 (CS02 ∷ CCZ013 ∷ []) (CCZ013 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ013 ∷ CX24 ∷ []) (lem-comm-CX24-CCZ013 c4) ▸ done

  b1 : Chain (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CX41 ∷ CCZ034 ∷ CS04 ∷ CX24 ∷ CS04⁻ ∷ CCZ013 ∷ CX24 ∷ CS02 ∷ CX41 ∷ []) (Bx3-2410 ∷ CX41 ∷ CCZ024 ∷ CX41 ∷ [])
  b1 = at 7 2 (CCZ013 ∷ CS04⁻ ∷ []) (pw2 c4 (CS04⁻ ∷ CCZ013 ∷ []) (CCZ013 ∷ CS04⁻ ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ013 ∷ CX24 ∷ []) (lem-comm-CX24-CCZ013 c4) ▸
       at 5 2 (CCZ013 ∷ CS04 ∷ []) (pw2 c4 (CS04 ∷ CCZ013 ∷ []) (CCZ013 ∷ CS04 ∷ []) tt tt Eq.refl) ▸
       at 6 5 (CCZ024 ∷ []) (pw1 c4 (CS04 ∷ CX24 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ []) (CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ013 ∷ CCZ034 ∷ []) (pw2 c4 (CCZ034 ∷ CCZ013 ∷ []) (CCZ013 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ013 ∷ CX41 ∷ CCZ034 ∷ []) (pw2 c4 (CX41 ∷ CCZ013 ∷ []) (CCZ013 ∷ CX41 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CX41 ∷ []) (pw2 c4 (CX41 ∷ CCZ034 ∷ CCZ034 ∷ []) (CX41 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx3-2410 ∷ []) (sym (lem-box-tQ-at0312243140 c4)) ▸ done

  b2 : Chain (Bx3-2410 ∷ CX41 ∷ CCZ024 ∷ CX41 ∷ []) (Bx3-2410 ∷ CCZ024 ∷ [])
  b2 = at 1 3 (CCZ024 ∷ []) (pw3 c4 (CX41 ∷ CCZ024 ∷ CX41 ∷ []) (CCZ024 ∷ []) tt tt Eq.refl) ▸ done

