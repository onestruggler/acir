{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D009 where

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
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-pairs)
open import Examples.Groups.Clifford+CS.Five.D.D006 using (lem-sym-ab-at13243142)
open import Examples.Groups.Clifford+CS.Five.D.D008 using (lem-box-tQ-at14233142 ; lem-cQ-at14233142)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CSd12-TOFF034 ; lem-comm-CX12-CCZ034 ; lem-comm-CZ12-CCZ034 ; lem-comm-CZ12-TOFF034)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-comm-CS12-TOFF034)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-comm-SWAP13-BOX⟨0·42⟩ ; lem-comm-TOFF034-CSd12)
-- CXbc-box @14233142: 17 steps
lem-CXbc-box-at14233142 : Complete 4 → ⟪ (CX31 ∷ Bx0-4312 ∷ CX31 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4312 ∷ CCZ234 ∷ []) ⟫ʷ
lem-CXbc-box-at14233142 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX31 ∷ Bx0-4312 ∷ CX31 ∷ []) (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CX31 ∷ CCZ023 ∷ CS23 ∷ CX43 ∷ CS23⁻ ∷ CCZ012 ∷ CX43 ∷ CS24 ∷ CX31 ∷ [])
  b0 = at 1 1 (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ []) (lem-box-tQ-at14233142 c4) ▸
       at 0 2 (Toff034 ∷ CX31 ∷ []) (pw2 c4 (CX31 ∷ Toff034 ∷ []) (Toff034 ∷ CX31 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ CX31 ∷ CCZ023 ∷ []) (lw4 c4 (CX31 ∷ CCZ012 ∷ []) (CCZ012 ∷ CX31 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff034 ∷ CCZ023 ∷ CCZ234 ∷ []) (pw1 c4 (CCZ023 ∷ Toff034 ∷ []) (Toff034 ∷ CCZ023 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff034 ∷ CX31 ∷ []) (pw2 c4 (CX31 ∷ Toff034 ∷ []) (Toff034 ∷ CX31 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CS23 ∷ CX43 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ []) (lw0 c4 (CCZ234 ∷ []) (CS23 ∷ CX43 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ012 ∷ CS24 ∷ []) (pw3 c4 (CS24 ∷ CCZ012 ∷ []) (CCZ012 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ012 ∷ CX43 ∷ []) (sym (c₃ (CCZ) (CX₁₀))) ▸ done

  b1 : Chain (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CX31 ∷ CCZ023 ∷ CS23 ∷ CX43 ∷ CS23⁻ ∷ CCZ012 ∷ CX43 ∷ CS24 ∷ CX31 ∷ []) (Bx0-4312 ∷ CX31 ∷ CCZ234 ∷ CX31 ∷ [])
  b1 = at 7 2 (CCZ012 ∷ CS23⁻ ∷ []) (lw4 c4 (CS23⁻ ∷ CCZ012 ∷ []) (CCZ012 ∷ CS23⁻ ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ012 ∷ CX43 ∷ []) (sym (c₃ (CCZ) (CX₁₀))) ▸
       at 5 2 (CCZ012 ∷ CS23 ∷ []) (lw4 c4 (CS23 ∷ CCZ012 ∷ []) (CCZ012 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 6 5 (CCZ234 ∷ []) (lw0 c4 (CS23 ∷ CX43 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ012 ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ CCZ012 ∷ []) (CCZ012 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ012 ∷ CX31 ∷ CCZ023 ∷ []) (lw4 c4 (CX31 ∷ CCZ012 ∷ []) (CCZ012 ∷ CX31 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CX31 ∷ []) (lw4 c4 (CX31 ∷ CCZ023 ∷ CCZ023 ∷ []) (CX31 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx0-4312 ∷ []) (sym (lem-box-tQ-at14233142 c4)) ▸ done

  b2 : Chain (Bx0-4312 ∷ CX31 ∷ CCZ234 ∷ CX31 ∷ []) (Bx0-4312 ∷ CCZ234 ∷ [])
  b2 = at 1 3 (CCZ234 ∷ []) (lw0 c4 (CX31 ∷ CCZ234 ∷ CX31 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸ done


-- CXcb-box @14233142: 18 steps
lem-CXcb-box-at14233142 : Complete 4 → ⟪ (CX13 ∷ Bx0-4312 ∷ CX13 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4312 ∷ CCZ124 ∷ []) ⟫ʷ
lem-CXcb-box-at14233142 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX13 ∷ Bx0-4312 ∷ CX13 ∷ []) (Toff034 ∷ CCZ012 ∷ CX13 ∷ Toff014 ∷ CS12 ∷ CX41 ∷ Toff034 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ CCZ012 ∷ CX13 ∷ [])
  b0 = at 1 1 (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ []) (lem-box-tQ-at14233142 c4) ▸
       at 0 2 (Toff034 ∷ CX13 ∷ Toff014 ∷ []) (pw2 c4 (CX13 ∷ Toff034 ∷ []) (Toff034 ∷ CX13 ∷ Toff014 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ012 ∷ Toff014 ∷ CCZ124 ∷ []) (pw3 c4 (Toff014 ∷ CCZ012 ∷ []) (CCZ012 ∷ Toff014 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ CX13 ∷ []) (lw4 c4 (CX13 ∷ CCZ012 ∷ []) (CCZ012 ∷ CX13 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ []) (lw0 c4 (CCZ124 ∷ []) (CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (Toff034 ∷ CS24 ∷ []) (pw1 c4 (CS24 ∷ Toff034 ∷ []) (Toff034 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff034 ∷ CX41 ∷ []) (pw2 c4 (CX41 ∷ Toff034 ∷ []) (Toff034 ∷ CX41 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Toff034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-TOFF034 c4) ▸ done

  b1 : Chain (Toff034 ∷ CCZ012 ∷ CX13 ∷ Toff014 ∷ CS12 ∷ CX41 ∷ Toff034 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ CCZ012 ∷ CX13 ∷ []) (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ CX13 ∷ CCZ124 ∷ CX13 ∷ [])
  b1 = at 5 2 (Toff034 ∷ CX41 ∷ []) (pw2 c4 (CX41 ∷ Toff034 ∷ []) (Toff034 ∷ CX41 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff034 ∷ CS12 ∷ []) (lem-comm-CS12-TOFF034 c4) ▸
       at 5 5 (CCZ124 ∷ []) (lw0 c4 (CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff034 ∷ Toff014 ∷ []) (pw2 c4 (Toff014 ∷ Toff034 ∷ []) (Toff034 ∷ Toff014 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff034 ∷ CX13 ∷ Toff014 ∷ []) (pw2 c4 (CX13 ∷ Toff034 ∷ []) (Toff034 ∷ CX13 ∷ Toff014 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CX13 ∷ []) (pw2 c4 (CX13 ∷ Toff014 ∷ Toff014 ∷ []) (CX13 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ012 ∷ CCZ124 ∷ []) (pw3 c4 (CCZ124 ∷ CCZ012 ∷ []) (CCZ012 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ012 ∷ CX13 ∷ []) (lw4 c4 (CX13 ∷ CCZ012 ∷ []) (CCZ012 ∷ CX13 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ CX13 ∷ CCZ124 ∷ CX13 ∷ []) (Bx0-4312 ∷ CCZ124 ∷ [])
  b2 = at 0 4 (Bx0-4312 ∷ []) (sym (lem-box-tQ-at14233142 c4)) ▸
       at 1 3 (CCZ124 ∷ []) (lw0 c4 (CX13 ∷ CCZ124 ∷ CX13 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl) ▸ done


-- SWbc-box @14233142: 11 steps
lem-SWbc-box-at14233142 : Complete 4 → ⟪ (Sw13 ∷ Bx0-4312 ∷ Sw13 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4312 ∷ []) ⟫ʷ
lem-SWbc-box-at14233142 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw13 ∷ Bx0-4312 ∷ Sw13 ∷ []) (CX31 ∷ Bx0-4312 ∷ CX31 ∷ CCZ234 ∷ CCZ124 ∷ CCZ234 ∷ CCZ124 ∷ CCZ234 ∷ [])
  b0 = at 0 1 (CX31 ∷ CX13 ∷ CX31 ∷ []) (lw4 c4 (Sw13 ∷ []) (CX31 ∷ CX13 ∷ CX31 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CX31 ∷ CX13 ∷ CX31 ∷ []) (lw4 c4 (Sw13 ∷ []) (CX31 ∷ CX13 ∷ CX31 ∷ []) tt tt Eq.refl) ▸
       at 2 3 (Bx0-4312 ∷ CCZ234 ∷ []) (lem-CXbc-box-at14233142 c4) ▸
       at 3 2 (CX13 ∷ CCZ124 ∷ CCZ234 ∷ []) (lw0 c4 (CCZ234 ∷ CX13 ∷ []) (CX13 ∷ CCZ124 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Bx0-4312 ∷ CCZ124 ∷ []) (lem-CXcb-box-at14233142 c4) ▸
       at 4 2 (CX31 ∷ CCZ234 ∷ []) (lw0 c4 (CCZ234 ∷ CX31 ∷ []) (CX31 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CX31 ∷ CCZ234 ∷ CCZ124 ∷ []) (lw0 c4 (CCZ124 ∷ CX31 ∷ []) (CX31 ∷ CCZ234 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CX31 ∷ CCZ234 ∷ CCZ124 ∷ []) (lw0 c4 (CCZ124 ∷ CX31 ∷ []) (CX31 ∷ CCZ234 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CX31 ∷ Bx0-4312 ∷ CX31 ∷ CCZ234 ∷ CCZ124 ∷ CCZ234 ∷ CCZ124 ∷ CCZ234 ∷ []) (Bx0-4312 ∷ [])
  b1 = at 3 5 (CCZ234 ∷ []) (lw0 c4 (CCZ234 ∷ CCZ124 ∷ CCZ234 ∷ CCZ124 ∷ CCZ234 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Bx0-4312 ∷ CCZ234 ∷ []) (lem-CXbc-box-at14233142 c4) ▸
       at 1 2 [] (lw0 c4 (CCZ234 ∷ CCZ234 ∷ []) [] tt tt Eq.refl) ▸ done


-- nat-SWbc @14233142: 23 steps
lem-nat-SWbc-at14233142 : Complete 4 → ⟪ (Sw13 ∷ Bx0-4312 ∷ Sw13 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4132 ∷ []) ⟫ʷ
lem-nat-SWbc-at14233142 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw13 ∷ Bx0-4312 ∷ Sw13 ∷ []) (CCZ014 ∷ Toff014 ∷ CCZ034 ∷ Toff403 ∷ Bx0-42 ∷ Toff403 ∷ Sw13 ∷ CCZ014 ∷ Bx0-42 ∷ Toff034 ∷ CCZ034 ∷ Bx4-012 ∷ Sw13 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff034 ∷ Bx4-012 ∷ Toff034 ∷ CCZ034 ∷ Bx4-012 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw13 ∷ []) (pw2 c4 (Sw13 ∷ CCZ034 ∷ []) (CCZ014 ∷ Sw13 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff014 ∷ Sw13 ∷ []) (pw2 c4 (Sw13 ∷ Toff034 ∷ []) (Toff014 ∷ Sw13 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (CCZ014 ∷ Toff401 ∷ Bx0-42 ∷ Toff401 ∷ CCZ014 ∷ Bx0-42 ∷ []) (refl) ▸
       at 2 2 (CCZ034 ∷ Sw13 ∷ []) (pw2 c4 (Sw13 ∷ CCZ014 ∷ []) (CCZ034 ∷ Sw13 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff403 ∷ Sw13 ∷ []) (pw2 c4 (Sw13 ∷ Toff401 ∷ []) (Toff403 ∷ Sw13 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Bx0-42 ∷ Sw13 ∷ []) (lem-comm-SWAP13-BOX⟨0·42⟩ c4) ▸
       at 5 2 (Toff403 ∷ Sw13 ∷ []) (pw2 c4 (Sw13 ∷ Toff401 ∷ []) (Toff403 ∷ Sw13 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CCZ014 ∷ Toff014 ∷ CCZ034 ∷ Toff403 ∷ Bx0-42 ∷ Toff403 ∷ Sw13 ∷ CCZ014 ∷ Bx0-42 ∷ Toff034 ∷ CCZ034 ∷ Bx4-012 ∷ Sw13 ∷ []) (CCZ014 ∷ Toff014 ∷ CCZ034 ∷ Toff403 ∷ Bx0-42 ∷ Toff403 ∷ CCZ034 ∷ Bx0-42 ∷ Toff014 ∷ CCZ014 ∷ CCZ034 ∷ Toff403 ∷ Bx0-42 ∷ Sw13 ∷ Toff401 ∷ CCZ014 ∷ Bx0-42 ∷ Sw13 ∷ [])
  b1 = at 6 2 (CCZ034 ∷ Sw13 ∷ []) (pw2 c4 (Sw13 ∷ CCZ014 ∷ []) (CCZ034 ∷ Sw13 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Bx0-42 ∷ Sw13 ∷ []) (lem-comm-SWAP13-BOX⟨0·42⟩ c4) ▸
       at 8 2 (Toff014 ∷ Sw13 ∷ []) (pw2 c4 (Sw13 ∷ Toff034 ∷ []) (Toff014 ∷ Sw13 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ014 ∷ Sw13 ∷ []) (pw2 c4 (Sw13 ∷ CCZ034 ∷ []) (CCZ014 ∷ Sw13 ∷ []) tt tt Eq.refl) ▸
       at 11 1 (CCZ014 ∷ Toff401 ∷ Bx0-42 ∷ Toff401 ∷ CCZ014 ∷ Bx0-42 ∷ []) (refl) ▸
       at 10 2 (CCZ034 ∷ Sw13 ∷ []) (pw2 c4 (Sw13 ∷ CCZ014 ∷ []) (CCZ034 ∷ Sw13 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (Toff403 ∷ Sw13 ∷ []) (pw2 c4 (Sw13 ∷ Toff401 ∷ []) (Toff403 ∷ Sw13 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (Bx0-42 ∷ Sw13 ∷ []) (lem-comm-SWAP13-BOX⟨0·42⟩ c4) ▸ done

  b2 : Chain (CCZ014 ∷ Toff014 ∷ CCZ034 ∷ Toff403 ∷ Bx0-42 ∷ Toff403 ∷ CCZ034 ∷ Bx0-42 ∷ Toff014 ∷ CCZ014 ∷ CCZ034 ∷ Toff403 ∷ Bx0-42 ∷ Sw13 ∷ Toff401 ∷ CCZ014 ∷ Bx0-42 ∷ Sw13 ∷ []) (Bx0-4132 ∷ [])
  b2 = at 13 2 (Toff403 ∷ Sw13 ∷ []) (pw2 c4 (Sw13 ∷ Toff401 ∷ []) (Toff403 ∷ Sw13 ∷ []) tt tt Eq.refl) ▸
       at 14 2 (CCZ034 ∷ Sw13 ∷ []) (pw2 c4 (Sw13 ∷ CCZ014 ∷ []) (CCZ034 ∷ Sw13 ∷ []) tt tt Eq.refl) ▸
       at 15 2 (Bx0-42 ∷ Sw13 ∷ []) (lem-comm-SWAP13-BOX⟨0·42⟩ c4) ▸
       at 16 2 [] (lw4 c4 (Sw13 ∷ Sw13 ∷ []) [] tt tt Eq.refl) ▸
       at 2 6 (Bx4-032 ∷ []) (refl) ▸
       at 5 6 (Bx4-032 ∷ []) (refl) ▸
       at 0 6 (Bx0-4132 ∷ []) (refl) ▸ done


-- sym-bc @14233142: 2 steps
lem-sym-bc-at14233142 : Complete 4 → ⟪ (Bx0-4312 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4132 ∷ []) ⟫ʷ
lem-sym-bc-at14233142 c4 = run b0
  where
  b0 : Chain (Bx0-4312 ∷ []) (Bx0-4132 ∷ [])
  b0 = at 0 1 (Sw13 ∷ Bx0-4312 ∷ Sw13 ∷ []) (sym (lem-SWbc-box-at14233142 c4)) ▸
       at 0 3 (Bx0-4132 ∷ []) (lem-nat-SWbc-at14233142 c4) ▸ done


-- box-perm-4132: 3 steps
lem-box-perm-4132 : Complete 4 → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4132 ∷ []) ⟫ʷ
lem-box-perm-4132 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ []) (Bx0-4132 ∷ [])
  b0 = at 0 1 (Bx0-3412 ∷ []) (lem-pairs c4) ▸
       at 0 1 (Bx0-4312 ∷ []) (lem-sym-ab-at13243142 c4) ▸
       at 0 1 (Bx0-4132 ∷ []) (lem-sym-bc-at14233142 c4) ▸ done


-- tP @14233142: 7 steps
lem-tP-at14233142 : Complete 4 → ⟪ (Toff034 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ Toff034 ∷ []) ⟫ʷ
lem-tP-at14233142 c4 = run b0
  where
  b0 : Chain (Toff034 ∷ Toff012 ∷ []) (Toff012 ∷ Toff034 ∷ [])
  b0 = at 0 1 (K0 ∷ CCZ034 ∷ K0⁻ ∷ []) (pw1 c4 (Toff034 ∷ []) (K0 ∷ CCZ034 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 1 (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (lw4 c4 (Toff012 ∷ []) (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (K0⁻ ∷ K0 ∷ []) [] tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ CCZ034 ∷ []) (lem-cQ-at14233142 c4) ▸
       at 2 0 (K0⁻ ∷ K0 ∷ []) (lw4 c4 [] (K0⁻ ∷ K0 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Toff012 ∷ []) (lw4 c4 (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (Toff012 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Toff034 ∷ []) (pw1 c4 (K0 ∷ CCZ034 ∷ K0⁻ ∷ []) (Toff034 ∷ []) tt tt Eq.refl) ▸ done


-- P-box @14233142: 8 steps
lem-P-box-at14233142 : Complete 4 → ⟪ (Toff012 ∷ Bx0-4312 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4312 ∷ []) ⟫ʷ
lem-P-box-at14233142 c4 = run b0
  where
  b0 : Chain (Toff012 ∷ Bx0-4312 ∷ Toff012 ∷ []) (Bx0-4312 ∷ [])
  b0 = at 1 1 (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ []) (lem-box-tQ-at14233142 c4) ▸
       at 0 2 (Toff034 ∷ Toff012 ∷ []) (sym (lem-tP-at14233142 c4)) ▸
       at 1 2 (CCZ012 ∷ CZ12 ∷ Toff012 ∷ []) (lw4 c4 (Toff012 ∷ CCZ012 ∷ []) (CCZ012 ∷ CZ12 ∷ Toff012 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff034 ∷ Toff012 ∷ []) (sym (lem-tP-at14233142 c4)) ▸
       at 4 3 (CCZ012 ∷ CZ12 ∷ []) (lw4 c4 (Toff012 ∷ CCZ012 ∷ Toff012 ∷ []) (CCZ012 ∷ CZ12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff034 ∷ CZ12 ∷ []) (lem-comm-CZ12-TOFF034 c4) ▸
       at 3 3 (CCZ012 ∷ []) (lw4 c4 (CZ12 ∷ CCZ012 ∷ CZ12 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx0-4312 ∷ []) (sym (lem-box-tQ-at14233142 c4)) ▸ done


-- VPQ @14233142: 14 steps
lem-VPQ-at14233142 : Complete 4 → ⟪ (Toff034 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ []) ⟫ʷ
lem-VPQ-at14233142 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff034 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ []) (CS12⁻ ∷ CS34⁻ ∷ S0 ∷ Toff012 ∷ Toff034 ∷ S0⁻ ∷ [])
  b0 = at 0 2 (CS34⁻ ∷ S0 ∷ Toff034 ∷ S0⁻ ∷ []) (pw1 c4 (Toff034 ∷ CCZ034 ∷ []) (CS34⁻ ∷ S0 ∷ Toff034 ∷ S0⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CS12⁻ ∷ S0 ∷ Toff012 ∷ S0⁻ ∷ []) (lw4 c4 (Toff012 ∷ CCZ012 ∷ []) (CS12⁻ ∷ S0 ∷ Toff012 ∷ S0⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CS12⁻ ∷ S0⁻ ∷ []) (c₁ (S • S • S) (CS • CS • CS)) ▸
       at 2 2 (CS12⁻ ∷ Toff034 ∷ []) (lem-comm-TOFF034-CSd12 c4) ▸
       at 1 2 (CS12⁻ ∷ S0 ∷ []) (c₁ (S) (CS • CS • CS)) ▸
       at 0 2 (CS12⁻ ∷ CS34⁻ ∷ []) (sym (c₃ ((CS • CS • CS) ↑) (CS • CS • CS))) ▸
       at 4 2 [] (lw4 c4 (S0⁻ ∷ S0 ∷ []) [] tt tt Eq.refl) ▸
       at 3 2 (Toff012 ∷ Toff034 ∷ []) (lem-tP-at14233142 c4) ▸ done

  b1 : Chain (CS12⁻ ∷ CS34⁻ ∷ S0 ∷ Toff012 ∷ Toff034 ∷ S0⁻ ∷ []) (Toff012 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ [])
  b1 = at 4 0 (S0⁻ ∷ S0 ∷ []) (lw4 c4 [] (S0⁻ ∷ S0 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (S0 ∷ CS34⁻ ∷ []) (sym (c₁ (S) ((CS • CS • CS) ↑ ↑))) ▸
       at 2 2 (Toff012 ∷ CS34⁻ ∷ []) (sym (c₃ (Toff) (CS • CS • CS))) ▸
       at 3 2 (S0⁻ ∷ CS34⁻ ∷ []) (sym (c₁ (S • S • S) ((CS • CS • CS) ↑ ↑))) ▸
       at 0 4 (Toff012 ∷ CCZ012 ∷ []) (lw4 c4 (CS12⁻ ∷ S0 ∷ Toff012 ∷ S0⁻ ∷ []) (Toff012 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Toff034 ∷ CCZ034 ∷ []) (pw1 c4 (CS34⁻ ∷ S0 ∷ Toff034 ∷ S0⁻ ∷ []) (Toff034 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸ done


-- QVQ @14233142: 3 steps
lem-QVQ-at14233142 : Complete 4 → ⟪ (CCZ012 ∷ Toff034 ∷ CCZ034 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ Toff034 ∷ CCZ034 ∷ Toff012 ∷ []) ⟫ʷ
lem-QVQ-at14233142 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Toff034 ∷ CCZ034 ∷ CCZ012 ∷ []) (Toff012 ∷ Toff034 ∷ CCZ034 ∷ Toff012 ∷ [])
  b0 = at 0 0 (Toff012 ∷ Toff012 ∷ []) (lw4 c4 [] (Toff012 ∷ Toff012 ∷ []) tt tt Eq.refl) ▸
       at 1 4 (Toff034 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ []) (sym (lem-VPQ-at14233142 c4)) ▸
       at 4 2 [] (lw4 c4 (CCZ012 ∷ CCZ012 ∷ []) [] tt tt Eq.refl) ▸ done


-- box-cP @14233142: 12 steps
lem-box-cP-at14233142 : Complete 4 → ⟪ (Bx0-4312 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ []) ⟫ʷ
lem-box-cP-at14233142 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-4312 ∷ []) (CCZ034 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ CCZ014 ∷ Toff401 ∷ CZ24 ∷ Toff401 ∷ CCZ014 ∷ CZ24 ∷ [])
  b0 = at 0 1 (CCZ034 ∷ Toff034 ∷ Bx4-012 ∷ Toff034 ∷ CCZ034 ∷ Bx4-012 ∷ []) (refl) ▸
       at 2 1 (CCZ014 ∷ Toff401 ∷ Bx0-42 ∷ Toff401 ∷ CCZ014 ∷ Bx0-42 ∷ []) (refl) ▸
       at 4 1 (CZ24 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 2 6 (CCZ012 ∷ []) (pw3 c4 (CCZ014 ∷ Toff401 ∷ CZ24 ∷ Toff401 ∷ CCZ014 ∷ CZ24 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ014 ∷ Toff401 ∷ Bx0-42 ∷ Toff401 ∷ CCZ014 ∷ Bx0-42 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 10 1 (CZ24 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ034 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ CCZ014 ∷ Toff401 ∷ CZ24 ∷ Toff401 ∷ CCZ014 ∷ CZ24 ∷ []) (CCZ034 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ [])
  b1 = at 5 6 (CCZ012 ∷ []) (pw3 c4 (CCZ014 ∷ Toff401 ∷ CZ24 ∷ Toff401 ∷ CCZ014 ∷ CZ24 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Toff012 ∷ Toff034 ∷ CCZ034 ∷ Toff012 ∷ []) (lem-QVQ-at14233142 c4) ▸
       at 1 2 (Toff012 ∷ Toff034 ∷ []) (lem-tP-at14233142 c4) ▸
       at 2 2 [] (pw1 c4 (Toff034 ∷ Toff034 ∷ []) [] tt tt Eq.refl) ▸ done


-- cQ @3443: 7 steps
lem-cQ-at3443 : Complete 4 → ⟪ (CCZ012 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ CCZ012 ∷ []) ⟫ʷ
lem-cQ-at3443 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ012 ∷ [])
  b0 = at 0 1 (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ034 ∷ CS01 ∷ []) (pw2 c4 (CS01 ∷ CCZ034 ∷ []) (CCZ034 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 c4) ▸
       at 2 2 (CCZ034 ∷ CS02⁻ ∷ []) (pw1 c4 (CS02⁻ ∷ CCZ034 ∷ []) (CCZ034 ∷ CS02⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 c4) ▸
       at 0 2 (CCZ034 ∷ CS02 ∷ []) (pw1 c4 (CS02 ∷ CCZ034 ∷ []) (CCZ034 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 1 5 (CCZ012 ∷ []) (lw4 c4 (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸ done


-- box-tQ @3443: 13 steps
lem-box-tQ-at3443 : Complete 4 → ⟪ (Bx0-1243 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) ⟫ʷ
lem-box-tQ-at3443 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-1243 ∷ []) (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ014 ∷ Toff104 ∷ CZ13 ∷ Toff104 ∷ CCZ014 ∷ CZ13 ∷ [])
  b0 = at 0 1 (CCZ012 ∷ Toff012 ∷ Bx1-043 ∷ Toff012 ∷ CCZ012 ∷ Bx1-043 ∷ []) (refl) ▸
       at 2 1 (CCZ014 ∷ Toff104 ∷ Bx0-13 ∷ Toff104 ∷ CCZ014 ∷ Bx0-13 ∷ []) (refl) ▸
       at 4 1 (CZ13 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 2 6 (CCZ034 ∷ []) (pw2 c4 (CCZ014 ∷ Toff104 ∷ CZ13 ∷ Toff104 ∷ CCZ014 ∷ CZ13 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ014 ∷ Toff104 ∷ Bx0-13 ∷ Toff104 ∷ CCZ014 ∷ Bx0-13 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 10 1 (CZ13 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ014 ∷ Toff104 ∷ CZ13 ∷ Toff104 ∷ CCZ014 ∷ CZ13 ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ [])
  b1 = at 5 6 (CCZ034 ∷ []) (pw2 c4 (CCZ014 ∷ Toff104 ∷ CZ13 ∷ Toff104 ∷ CCZ014 ∷ CZ13 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Toff012 ∷ CCZ012 ∷ CZ12 ∷ []) (lw4 c4 (CCZ012 ∷ Toff012 ∷ []) (Toff012 ∷ CCZ012 ∷ CZ12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ034 ∷ CZ12 ∷ []) (lem-comm-CZ12-CCZ034 c4) ▸
       at 1 2 (CCZ034 ∷ CCZ012 ∷ []) (lem-cQ-at3443 c4) ▸
       at 2 4 (Toff012 ∷ []) (lw4 c4 (CCZ012 ∷ CZ12 ∷ Toff012 ∷ CCZ012 ∷ []) (Toff012 ∷ []) tt tt Eq.refl) ▸ done


-- pairs @14233142: 4 steps
lem-pairs-at14233142 : Complete 4 → ⟪ (Bx0-4312 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1243 ∷ []) ⟫ʷ
lem-pairs-at14233142 c4 = run b0
  where
  b0 : Chain (Bx0-4312 ∷ []) (Bx0-1243 ∷ [])
  b0 = at 0 1 (Toff012 ∷ Bx0-4312 ∷ Toff012 ∷ []) (sym (lem-P-box-at14233142 c4)) ▸
       at 1 1 (CCZ034 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ []) (lem-box-cP-at14233142 c4) ▸
       at 4 2 [] (lw4 c4 (Toff012 ∷ Toff012 ∷ []) [] tt tt Eq.refl) ▸
       at 0 4 (Bx0-1243 ∷ []) (sym (lem-box-tQ-at3443 c4)) ▸ done


-- box-perm-1243: 3 steps
lem-box-perm-1243 : Complete 4 → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1243 ∷ []) ⟫ʷ
lem-box-perm-1243 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ []) (Bx0-1243 ∷ [])
  b0 = at 0 1 (Bx0-3412 ∷ []) (lem-pairs c4) ▸
       at 0 1 (Bx0-4312 ∷ []) (lem-sym-ab-at13243142 c4) ▸
       at 0 1 (Bx0-1243 ∷ []) (lem-pairs-at14233142 c4) ▸ done


-- sym-ab @13213442: 18 steps
lem-sym-ab-at13213442 : Complete 4 → ⟪ (Bx0-3142 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1342 ∷ []) ⟫ʷ
lem-sym-ab-at13213442 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx0-3142 ∷ []) (CCZ013 ∷ Toff013 ∷ CCZ014 ∷ Toff104 ∷ Bx0-12 ∷ Toff104 ∷ CCZ014 ∷ Bx0-12 ∷ Toff013 ∷ CCZ013 ∷ Bx3-042 ∷ [])
  b0 = at 0 1 (CCZ013 ∷ Toff013 ∷ Bx3-042 ∷ Toff013 ∷ CCZ013 ∷ Bx3-042 ∷ []) (refl) ▸
       at 2 1 (CCZ034 ∷ Toff304 ∷ Bx0-32 ∷ Toff304 ∷ CCZ034 ∷ Bx0-32 ∷ []) (refl) ▸
       at 4 1 (CZ23 ∷ []) (refl) ▸
       at 7 1 (CZ23 ∷ []) (refl) ▸
       at 2 6 (CCZ024 ∷ []) (pw1 c4 (CCZ034 ∷ Toff304 ∷ CZ23 ∷ Toff304 ∷ CCZ034 ∷ CZ23 ∷ []) (CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (CCZ014 ∷ Toff104 ∷ CZ12 ∷ Toff104 ∷ CCZ014 ∷ CZ12 ∷ []) (pw3 c4 (CCZ024 ∷ []) (CCZ014 ∷ Toff104 ∷ CZ12 ∷ Toff104 ∷ CCZ014 ∷ CZ12 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Bx0-12 ∷ []) (refl) ▸
       at 7 1 (Bx0-12 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ013 ∷ Toff013 ∷ CCZ014 ∷ Toff104 ∷ Bx0-12 ∷ Toff104 ∷ CCZ014 ∷ Bx0-12 ∷ Toff013 ∷ CCZ013 ∷ Bx3-042 ∷ []) (CCZ013 ∷ Toff013 ∷ Bx1-042 ∷ Toff013 ∷ CCZ013 ∷ CCZ014 ∷ Toff104 ∷ Bx0-12 ∷ Toff104 ∷ CCZ014 ∷ Bx0-12 ∷ [])
  b1 = at 2 6 (Bx1-042 ∷ []) (refl) ▸
       at 5 1 (CCZ034 ∷ Toff304 ∷ Bx0-32 ∷ Toff304 ∷ CCZ034 ∷ Bx0-32 ∷ []) (refl) ▸
       at 7 1 (CZ23 ∷ []) (refl) ▸
       at 10 1 (CZ23 ∷ []) (refl) ▸
       at 5 6 (CCZ024 ∷ []) (pw1 c4 (CCZ034 ∷ Toff304 ∷ CZ23 ∷ Toff304 ∷ CCZ034 ∷ CZ23 ∷ []) (CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ014 ∷ Toff104 ∷ CZ12 ∷ Toff104 ∷ CCZ014 ∷ CZ12 ∷ []) (pw3 c4 (CCZ024 ∷ []) (CCZ014 ∷ Toff104 ∷ CZ12 ∷ Toff104 ∷ CCZ014 ∷ CZ12 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (Bx0-12 ∷ []) (refl) ▸
       at 10 1 (Bx0-12 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ013 ∷ Toff013 ∷ Bx1-042 ∷ Toff013 ∷ CCZ013 ∷ CCZ014 ∷ Toff104 ∷ Bx0-12 ∷ Toff104 ∷ CCZ014 ∷ Bx0-12 ∷ []) (Bx0-1342 ∷ [])
  b2 = at 5 6 (Bx1-042 ∷ []) (refl) ▸
       at 0 6 (Bx0-1342 ∷ []) (refl) ▸ done

