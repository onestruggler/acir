{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D048 where

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
open import Examples.Groups.Clifford+CS.Five.D.D047 using (lem-CXbc-box-at0213243140 ; lem-CXcb-box-at0213243140 ; lem-cQ-at0213243140 ; lem-pairs-at0220 ; lem-sym-ab-at021021)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-CSd04-TOFF213 ; lem-comm-CX13-CCZ024)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-comm-CZ13-CCZ024)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-comm-CX31-CCZ024)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-comm-CS04-TOFF213)
open import Examples.Groups.Clifford+CS.Five.D.R018 using (lem-comm-SWAP14-BOX⟨2·30⟩)
-- SWbc-box @0213243140: 11 steps
lem-SWbc-box-at0213243140 : Complete 4 → ⟪ (Sw14 ∷ Bx2-3410 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3410 ∷ []) ⟫ʷ
lem-SWbc-box-at0213243140 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw14 ∷ Bx2-3410 ∷ Sw14 ∷ []) (CX41 ∷ Bx2-3410 ∷ CX41 ∷ CCZ034 ∷ CCZ013 ∷ CCZ034 ∷ CCZ013 ∷ CCZ034 ∷ [])
  b0 = at 0 1 (CX41 ∷ CX14 ∷ CX41 ∷ []) (lw0 c4 (Sw14 ∷ []) (CX41 ∷ CX14 ∷ CX41 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CX41 ∷ CX14 ∷ CX41 ∷ []) (lw0 c4 (Sw14 ∷ []) (CX41 ∷ CX14 ∷ CX41 ∷ []) tt tt Eq.refl) ▸
       at 2 3 (Bx2-3410 ∷ CCZ034 ∷ []) (lem-CXbc-box-at0213243140 c4) ▸
       at 3 2 (CX14 ∷ CCZ013 ∷ CCZ034 ∷ []) (pw2 c4 (CCZ034 ∷ CX14 ∷ []) (CX14 ∷ CCZ013 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Bx2-3410 ∷ CCZ013 ∷ []) (lem-CXcb-box-at0213243140 c4) ▸
       at 4 2 (CX41 ∷ CCZ034 ∷ []) (pw2 c4 (CCZ034 ∷ CX41 ∷ []) (CX41 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CX41 ∷ CCZ034 ∷ CCZ013 ∷ []) (pw2 c4 (CCZ013 ∷ CX41 ∷ []) (CX41 ∷ CCZ034 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CX41 ∷ CCZ034 ∷ CCZ013 ∷ []) (pw2 c4 (CCZ013 ∷ CX41 ∷ []) (CX41 ∷ CCZ034 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CX41 ∷ Bx2-3410 ∷ CX41 ∷ CCZ034 ∷ CCZ013 ∷ CCZ034 ∷ CCZ013 ∷ CCZ034 ∷ []) (Bx2-3410 ∷ [])
  b1 = at 3 5 (CCZ034 ∷ []) (pw2 c4 (CCZ034 ∷ CCZ013 ∷ CCZ034 ∷ CCZ013 ∷ CCZ034 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Bx2-3410 ∷ CCZ034 ∷ []) (lem-CXbc-box-at0213243140 c4) ▸
       at 1 2 [] (pw1 c4 (CCZ034 ∷ CCZ034 ∷ []) [] tt tt Eq.refl) ▸ done


-- nat-SWbc @0213243140: 23 steps
lem-nat-SWbc-at0213243140 : Complete 4 → ⟪ (Sw14 ∷ Bx2-3410 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3140 ∷ []) ⟫ʷ
lem-nat-SWbc-at0213243140 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw14 ∷ Bx2-3410 ∷ Sw14 ∷ []) (CCZ123 ∷ Toff213 ∷ CCZ234 ∷ Toff324 ∷ Bx2-30 ∷ Toff324 ∷ Sw14 ∷ CCZ123 ∷ Bx2-30 ∷ Toff234 ∷ CCZ234 ∷ Bx3-210 ∷ Sw14 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff234 ∷ Bx3-210 ∷ Toff234 ∷ CCZ234 ∷ Bx3-210 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw14 ∷ []) (lw0 c4 (Sw14 ∷ CCZ234 ∷ []) (CCZ123 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff213 ∷ Sw14 ∷ []) (lw0 c4 (Sw14 ∷ Toff234 ∷ []) (Toff213 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (CCZ123 ∷ Toff312 ∷ Bx2-30 ∷ Toff312 ∷ CCZ123 ∷ Bx2-30 ∷ []) (refl) ▸
       at 2 2 (CCZ234 ∷ Sw14 ∷ []) (lw0 c4 (Sw14 ∷ CCZ123 ∷ []) (CCZ234 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff324 ∷ Sw14 ∷ []) (lw0 c4 (Sw14 ∷ Toff312 ∷ []) (Toff324 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Bx2-30 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨2·30⟩ c4) ▸
       at 5 2 (Toff324 ∷ Sw14 ∷ []) (lw0 c4 (Sw14 ∷ Toff312 ∷ []) (Toff324 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CCZ123 ∷ Toff213 ∷ CCZ234 ∷ Toff324 ∷ Bx2-30 ∷ Toff324 ∷ Sw14 ∷ CCZ123 ∷ Bx2-30 ∷ Toff234 ∷ CCZ234 ∷ Bx3-210 ∷ Sw14 ∷ []) (CCZ123 ∷ Toff213 ∷ CCZ234 ∷ Toff324 ∷ Bx2-30 ∷ Toff324 ∷ CCZ234 ∷ Bx2-30 ∷ Toff213 ∷ CCZ123 ∷ CCZ234 ∷ Toff324 ∷ Bx2-30 ∷ Sw14 ∷ Toff312 ∷ CCZ123 ∷ Bx2-30 ∷ Sw14 ∷ [])
  b1 = at 6 2 (CCZ234 ∷ Sw14 ∷ []) (lw0 c4 (Sw14 ∷ CCZ123 ∷ []) (CCZ234 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Bx2-30 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨2·30⟩ c4) ▸
       at 8 2 (Toff213 ∷ Sw14 ∷ []) (lw0 c4 (Sw14 ∷ Toff234 ∷ []) (Toff213 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ123 ∷ Sw14 ∷ []) (lw0 c4 (Sw14 ∷ CCZ234 ∷ []) (CCZ123 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 11 1 (CCZ123 ∷ Toff312 ∷ Bx2-30 ∷ Toff312 ∷ CCZ123 ∷ Bx2-30 ∷ []) (refl) ▸
       at 10 2 (CCZ234 ∷ Sw14 ∷ []) (lw0 c4 (Sw14 ∷ CCZ123 ∷ []) (CCZ234 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (Toff324 ∷ Sw14 ∷ []) (lw0 c4 (Sw14 ∷ Toff312 ∷ []) (Toff324 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (Bx2-30 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨2·30⟩ c4) ▸ done

  b2 : Chain (CCZ123 ∷ Toff213 ∷ CCZ234 ∷ Toff324 ∷ Bx2-30 ∷ Toff324 ∷ CCZ234 ∷ Bx2-30 ∷ Toff213 ∷ CCZ123 ∷ CCZ234 ∷ Toff324 ∷ Bx2-30 ∷ Sw14 ∷ Toff312 ∷ CCZ123 ∷ Bx2-30 ∷ Sw14 ∷ []) (Bx2-3140 ∷ [])
  b2 = at 13 2 (Toff324 ∷ Sw14 ∷ []) (lw0 c4 (Sw14 ∷ Toff312 ∷ []) (Toff324 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 14 2 (CCZ234 ∷ Sw14 ∷ []) (lw0 c4 (Sw14 ∷ CCZ123 ∷ []) (CCZ234 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 15 2 (Bx2-30 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨2·30⟩ c4) ▸
       at 16 2 [] (lw0 c4 (Sw14 ∷ Sw14 ∷ []) [] tt tt Eq.refl) ▸
       at 2 6 (Bx3-240 ∷ []) (refl) ▸
       at 5 6 (Bx3-240 ∷ []) (refl) ▸
       at 0 6 (Bx2-3140 ∷ []) (refl) ▸ done


-- sym-bc @0213243140: 2 steps
lem-sym-bc-at0213243140 : Complete 4 → ⟪ (Bx2-3410 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3140 ∷ []) ⟫ʷ
lem-sym-bc-at0213243140 c4 = run b0
  where
  b0 : Chain (Bx2-3410 ∷ []) (Bx2-3140 ∷ [])
  b0 = at 0 1 (Sw14 ∷ Bx2-3410 ∷ Sw14 ∷ []) (sym (lem-SWbc-box-at0213243140 c4)) ▸
       at 0 3 (Bx2-3140 ∷ []) (lem-nat-SWbc-at0213243140 c4) ▸ done


-- sym-ab @0213213440: 18 steps
lem-sym-ab-at0213213440 : Complete 4 → ⟪ (Bx2-3140 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1340 ∷ []) ⟫ʷ
lem-sym-ab-at0213213440 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx2-3140 ∷ []) (CCZ123 ∷ Toff213 ∷ CCZ124 ∷ Toff124 ∷ Bx2-10 ∷ Toff124 ∷ CCZ124 ∷ Bx2-10 ∷ Toff213 ∷ CCZ123 ∷ Bx3-240 ∷ [])
  b0 = at 0 1 (CCZ123 ∷ Toff213 ∷ Bx3-240 ∷ Toff213 ∷ CCZ123 ∷ Bx3-240 ∷ []) (refl) ▸
       at 2 1 (CCZ234 ∷ Toff324 ∷ Bx2-30 ∷ Toff324 ∷ CCZ234 ∷ Bx2-30 ∷ []) (refl) ▸
       at 4 1 (CZ03 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 2 6 (CCZ024 ∷ []) (pw1 c4 (CCZ234 ∷ Toff324 ∷ CZ03 ∷ Toff324 ∷ CCZ234 ∷ CZ03 ∷ []) (CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (CCZ124 ∷ Toff124 ∷ CZ01 ∷ Toff124 ∷ CCZ124 ∷ CZ01 ∷ []) (pw3 c4 (CCZ024 ∷ []) (CCZ124 ∷ Toff124 ∷ CZ01 ∷ Toff124 ∷ CCZ124 ∷ CZ01 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Bx2-10 ∷ []) (refl) ▸
       at 7 1 (Bx2-10 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ123 ∷ Toff213 ∷ CCZ124 ∷ Toff124 ∷ Bx2-10 ∷ Toff124 ∷ CCZ124 ∷ Bx2-10 ∷ Toff213 ∷ CCZ123 ∷ Bx3-240 ∷ []) (CCZ123 ∷ Toff213 ∷ Bx1-240 ∷ Toff213 ∷ CCZ123 ∷ CCZ124 ∷ Toff124 ∷ Bx2-10 ∷ Toff124 ∷ CCZ124 ∷ Bx2-10 ∷ [])
  b1 = at 2 6 (Bx1-240 ∷ []) (refl) ▸
       at 5 1 (CCZ234 ∷ Toff324 ∷ Bx2-30 ∷ Toff324 ∷ CCZ234 ∷ Bx2-30 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 10 1 (CZ03 ∷ []) (refl) ▸
       at 5 6 (CCZ024 ∷ []) (pw1 c4 (CCZ234 ∷ Toff324 ∷ CZ03 ∷ Toff324 ∷ CCZ234 ∷ CZ03 ∷ []) (CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ124 ∷ Toff124 ∷ CZ01 ∷ Toff124 ∷ CCZ124 ∷ CZ01 ∷ []) (pw3 c4 (CCZ024 ∷ []) (CCZ124 ∷ Toff124 ∷ CZ01 ∷ Toff124 ∷ CCZ124 ∷ CZ01 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (Bx2-10 ∷ []) (refl) ▸
       at 10 1 (Bx2-10 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ123 ∷ Toff213 ∷ Bx1-240 ∷ Toff213 ∷ CCZ123 ∷ CCZ124 ∷ Toff124 ∷ Bx2-10 ∷ Toff124 ∷ CCZ124 ∷ Bx2-10 ∷ []) (Bx2-1340 ∷ [])
  b2 = at 5 6 (Bx1-240 ∷ []) (refl) ▸
       at 0 6 (Bx2-1340 ∷ []) (refl) ▸ done


-- box-perm-2341 @021021: 4 steps
lem-box-perm-2341-at021021 : Complete 4 → ⟪ (Bx2-0134 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1340 ∷ []) ⟫ʷ
lem-box-perm-2341-at021021 c4 = run b0
  where
  b0 : Chain (Bx2-0134 ∷ []) (Bx2-1340 ∷ [])
  b0 = at 0 1 (Bx2-1034 ∷ []) (lem-sym-ab-at021021 c4) ▸
       at 0 1 (Bx2-3410 ∷ []) (lem-pairs-at0220 c4) ▸
       at 0 1 (Bx2-3140 ∷ []) (lem-sym-bc-at0213243140 c4) ▸
       at 0 1 (Bx2-1340 ∷ []) (lem-sym-ab-at0213213440 c4) ▸ done


-- cQ @02233440: 7 steps
lem-cQ-at02233440 : Complete 4 → ⟪ (CCZ123 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ CCZ123 ∷ []) ⟫ʷ
lem-cQ-at02233440 c4 = run b0
  where
  b0 : Chain (CCZ123 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ123 ∷ [])
  b0 = at 0 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (lw4 c4 (CCZ123 ∷ []) (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ024 ∷ CS12 ∷ []) (pw3 c4 (CS12 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸
       at 2 2 (CCZ024 ∷ CS23⁻ ∷ []) (pw1 c4 (CS23⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ CS23⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸
       at 0 2 (CCZ024 ∷ CS23 ∷ []) (pw1 c4 (CS23 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 1 5 (CCZ123 ∷ []) (lw4 c4 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸ done


-- box-tQ @02233440: 13 steps
lem-box-tQ-at02233440 : Complete 4 → ⟪ (Bx2-1340 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ []) ⟫ʷ
lem-box-tQ-at02233440 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx2-1340 ∷ []) (CCZ123 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ CCZ124 ∷ Toff124 ∷ CZ01 ∷ Toff124 ∷ CCZ124 ∷ CZ01 ∷ [])
  b0 = at 0 1 (CCZ123 ∷ Toff213 ∷ Bx1-240 ∷ Toff213 ∷ CCZ123 ∷ Bx1-240 ∷ []) (refl) ▸
       at 2 1 (CCZ124 ∷ Toff124 ∷ Bx2-10 ∷ Toff124 ∷ CCZ124 ∷ Bx2-10 ∷ []) (refl) ▸
       at 4 1 (CZ01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 2 6 (CCZ024 ∷ []) (pw3 c4 (CCZ124 ∷ Toff124 ∷ CZ01 ∷ Toff124 ∷ CCZ124 ∷ CZ01 ∷ []) (CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ124 ∷ Toff124 ∷ Bx2-10 ∷ Toff124 ∷ CCZ124 ∷ Bx2-10 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 10 1 (CZ01 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ123 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ CCZ124 ∷ Toff124 ∷ CZ01 ∷ Toff124 ∷ CCZ124 ∷ CZ01 ∷ []) (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ [])
  b1 = at 5 6 (CCZ024 ∷ []) (pw3 c4 (CCZ124 ∷ Toff124 ∷ CZ01 ∷ Toff124 ∷ CCZ124 ∷ CZ01 ∷ []) (CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Toff213 ∷ CCZ123 ∷ CZ13 ∷ []) (lw4 c4 (CCZ123 ∷ Toff213 ∷ []) (Toff213 ∷ CCZ123 ∷ CZ13 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ024 ∷ CZ13 ∷ []) (lem-comm-CZ13-CCZ024 c4) ▸
       at 1 2 (CCZ024 ∷ CCZ123 ∷ []) (lem-cQ-at02233440 c4) ▸
       at 2 4 (Toff213 ∷ []) (lw4 c4 (CCZ123 ∷ CZ13 ∷ Toff213 ∷ CCZ123 ∷ []) (Toff213 ∷ []) tt tt Eq.refl) ▸ done


-- sym-ab @02233440: 18 steps
lem-sym-ab-at02233440 : Complete 4 → ⟪ (Bx2-1340 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3140 ∷ []) ⟫ʷ
lem-sym-ab-at02233440 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx2-1340 ∷ []) (CCZ123 ∷ Toff213 ∷ CCZ234 ∷ Toff324 ∷ Bx2-30 ∷ Toff324 ∷ CCZ234 ∷ Bx2-30 ∷ Toff213 ∷ CCZ123 ∷ Bx1-240 ∷ [])
  b0 = at 0 1 (CCZ123 ∷ Toff213 ∷ Bx1-240 ∷ Toff213 ∷ CCZ123 ∷ Bx1-240 ∷ []) (refl) ▸
       at 2 1 (CCZ124 ∷ Toff124 ∷ Bx2-10 ∷ Toff124 ∷ CCZ124 ∷ Bx2-10 ∷ []) (refl) ▸
       at 4 1 (CZ01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 2 6 (CCZ024 ∷ []) (pw3 c4 (CCZ124 ∷ Toff124 ∷ CZ01 ∷ Toff124 ∷ CCZ124 ∷ CZ01 ∷ []) (CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (CCZ234 ∷ Toff324 ∷ CZ03 ∷ Toff324 ∷ CCZ234 ∷ CZ03 ∷ []) (pw1 c4 (CCZ024 ∷ []) (CCZ234 ∷ Toff324 ∷ CZ03 ∷ Toff324 ∷ CCZ234 ∷ CZ03 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Bx2-30 ∷ []) (refl) ▸
       at 7 1 (Bx2-30 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ123 ∷ Toff213 ∷ CCZ234 ∷ Toff324 ∷ Bx2-30 ∷ Toff324 ∷ CCZ234 ∷ Bx2-30 ∷ Toff213 ∷ CCZ123 ∷ Bx1-240 ∷ []) (CCZ123 ∷ Toff213 ∷ Bx3-240 ∷ Toff213 ∷ CCZ123 ∷ CCZ234 ∷ Toff324 ∷ Bx2-30 ∷ Toff324 ∷ CCZ234 ∷ Bx2-30 ∷ [])
  b1 = at 2 6 (Bx3-240 ∷ []) (refl) ▸
       at 5 1 (CCZ124 ∷ Toff124 ∷ Bx2-10 ∷ Toff124 ∷ CCZ124 ∷ Bx2-10 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 10 1 (CZ01 ∷ []) (refl) ▸
       at 5 6 (CCZ024 ∷ []) (pw3 c4 (CCZ124 ∷ Toff124 ∷ CZ01 ∷ Toff124 ∷ CCZ124 ∷ CZ01 ∷ []) (CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ234 ∷ Toff324 ∷ CZ03 ∷ Toff324 ∷ CCZ234 ∷ CZ03 ∷ []) (pw1 c4 (CCZ024 ∷ []) (CCZ234 ∷ Toff324 ∷ CZ03 ∷ Toff324 ∷ CCZ234 ∷ CZ03 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (Bx2-30 ∷ []) (refl) ▸
       at 10 1 (Bx2-30 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ123 ∷ Toff213 ∷ Bx3-240 ∷ Toff213 ∷ CCZ123 ∷ CCZ234 ∷ Toff324 ∷ Bx2-30 ∷ Toff324 ∷ CCZ234 ∷ Bx2-30 ∷ []) (Bx2-3140 ∷ [])
  b2 = at 5 6 (Bx3-240 ∷ []) (refl) ▸
       at 0 6 (Bx2-3140 ∷ []) (refl) ▸ done


-- cQ @0213213440: 7 steps
lem-cQ-at0213213440 : Complete 4 → ⟪ (CCZ123 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ CCZ123 ∷ []) ⟫ʷ
lem-cQ-at0213213440 c4 = run b0
  where
  b0 : Chain (CCZ123 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ123 ∷ [])
  b0 = at 0 1 (CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ []) (lw4 c4 (CCZ123 ∷ []) (CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ024 ∷ CS23 ∷ []) (pw1 c4 (CS23 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 c4) ▸
       at 2 2 (CCZ024 ∷ CS12⁻ ∷ []) (pw3 c4 (CS12⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 c4) ▸
       at 0 2 (CCZ024 ∷ CS12 ∷ []) (pw3 c4 (CS12 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 1 5 (CCZ123 ∷ []) (lw4 c4 (CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸ done


-- box-tQ @0213213440: 13 steps
lem-box-tQ-at0213213440 : Complete 4 → ⟪ (Bx2-3140 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ []) ⟫ʷ
lem-box-tQ-at0213213440 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx2-3140 ∷ []) (CCZ123 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ CCZ234 ∷ Toff324 ∷ CZ03 ∷ Toff324 ∷ CCZ234 ∷ CZ03 ∷ [])
  b0 = at 0 1 (CCZ123 ∷ Toff213 ∷ Bx3-240 ∷ Toff213 ∷ CCZ123 ∷ Bx3-240 ∷ []) (refl) ▸
       at 2 1 (CCZ234 ∷ Toff324 ∷ Bx2-30 ∷ Toff324 ∷ CCZ234 ∷ Bx2-30 ∷ []) (refl) ▸
       at 4 1 (CZ03 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 2 6 (CCZ024 ∷ []) (pw1 c4 (CCZ234 ∷ Toff324 ∷ CZ03 ∷ Toff324 ∷ CCZ234 ∷ CZ03 ∷ []) (CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ234 ∷ Toff324 ∷ Bx2-30 ∷ Toff324 ∷ CCZ234 ∷ Bx2-30 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 10 1 (CZ03 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ123 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ CCZ234 ∷ Toff324 ∷ CZ03 ∷ Toff324 ∷ CCZ234 ∷ CZ03 ∷ []) (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ [])
  b1 = at 5 6 (CCZ024 ∷ []) (pw1 c4 (CCZ234 ∷ Toff324 ∷ CZ03 ∷ Toff324 ∷ CCZ234 ∷ CZ03 ∷ []) (CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Toff213 ∷ CCZ123 ∷ CZ13 ∷ []) (lw4 c4 (CCZ123 ∷ Toff213 ∷ []) (Toff213 ∷ CCZ123 ∷ CZ13 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ024 ∷ CZ13 ∷ []) (lem-comm-CZ13-CCZ024 c4) ▸
       at 1 2 (CCZ024 ∷ CCZ123 ∷ []) (lem-cQ-at0213213440 c4) ▸
       at 2 4 (Toff213 ∷ []) (lw4 c4 (CCZ123 ∷ CZ13 ∷ Toff213 ∷ CCZ123 ∷ []) (Toff213 ∷ []) tt tt Eq.refl) ▸ done


-- CXbc-box @0213213440: 17 steps
lem-CXbc-box-at0213213440 : Complete 4 → ⟪ (CX14 ∷ Bx2-3140 ∷ CX14 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3140 ∷ CCZ013 ∷ []) ⟫ʷ
lem-CXbc-box-at0213213440 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX14 ∷ Bx2-3140 ∷ CX14 ∷ []) (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CX14 ∷ CCZ012 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CCZ024 ∷ CX31 ∷ CS03 ∷ CX14 ∷ [])
  b0 = at 1 1 (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ []) (lem-box-tQ-at0213213440 c4) ▸
       at 0 2 (Toff213 ∷ CX14 ∷ []) (lw0 c4 (CX14 ∷ Toff213 ∷ []) (Toff213 ∷ CX14 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ024 ∷ CX14 ∷ CCZ012 ∷ []) (pw3 c4 (CX14 ∷ CCZ024 ∷ []) (CCZ024 ∷ CX14 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff213 ∷ CCZ012 ∷ CCZ013 ∷ []) (lw4 c4 (CCZ012 ∷ Toff213 ∷ []) (Toff213 ∷ CCZ012 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff213 ∷ CX14 ∷ []) (lw0 c4 (CX14 ∷ Toff213 ∷ []) (Toff213 ∷ CX14 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ []) (lw4 c4 (CCZ013 ∷ []) (CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ024 ∷ CS03 ∷ []) (pw1 c4 (CS03 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 c4) ▸ done

  b1 : Chain (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CX14 ∷ CCZ012 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CCZ024 ∷ CX31 ∷ CS03 ∷ CX14 ∷ []) (Bx2-3140 ∷ CX14 ∷ CCZ013 ∷ CX14 ∷ [])
  b1 = at 7 2 (CCZ024 ∷ CS01⁻ ∷ []) (pw3 c4 (CS01⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ CS01⁻ ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 c4) ▸
       at 5 2 (CCZ024 ∷ CS01 ∷ []) (pw3 c4 (CS01 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 6 5 (CCZ013 ∷ []) (lw4 c4 (CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ024 ∷ CCZ012 ∷ []) (pw3 c4 (CCZ012 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ024 ∷ CX14 ∷ CCZ012 ∷ []) (pw3 c4 (CX14 ∷ CCZ024 ∷ []) (CCZ024 ∷ CX14 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CX14 ∷ []) (pw3 c4 (CX14 ∷ CCZ012 ∷ CCZ012 ∷ []) (CX14 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx2-3140 ∷ []) (sym (lem-box-tQ-at0213213440 c4)) ▸ done

  b2 : Chain (Bx2-3140 ∷ CX14 ∷ CCZ013 ∷ CX14 ∷ []) (Bx2-3140 ∷ CCZ013 ∷ [])
  b2 = at 1 3 (CCZ013 ∷ []) (pw2 c4 (CX14 ∷ CCZ013 ∷ CX14 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸ done


-- CXcb-box @0213213440: 18 steps
lem-CXcb-box-at0213213440 : Complete 4 → ⟪ (CX41 ∷ Bx2-3140 ∷ CX41 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3140 ∷ CCZ034 ∷ []) ⟫ʷ
lem-CXcb-box-at0213213440 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX41 ∷ Bx2-3140 ∷ CX41 ∷ []) (Toff213 ∷ CCZ024 ∷ CX41 ∷ Toff234 ∷ CS04 ∷ CX34 ∷ Toff213 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ CCZ024 ∷ CX41 ∷ [])
  b0 = at 1 1 (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ []) (lem-box-tQ-at0213213440 c4) ▸
       at 0 2 (Toff213 ∷ CX41 ∷ Toff234 ∷ []) (lw0 c4 (CX41 ∷ Toff213 ∷ []) (Toff213 ∷ CX41 ∷ Toff234 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ024 ∷ Toff234 ∷ CCZ034 ∷ []) (pw1 c4 (Toff234 ∷ CCZ024 ∷ []) (CCZ024 ∷ Toff234 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ024 ∷ CX41 ∷ []) (pw3 c4 (CX41 ∷ CCZ024 ∷ []) (CCZ024 ∷ CX41 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CS04 ∷ CX34 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ []) (pw1 c4 (CCZ034 ∷ []) (CS04 ∷ CX34 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (Toff213 ∷ CS03 ∷ []) (lw4 c4 (CS03 ∷ Toff213 ∷ []) (Toff213 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff213 ∷ CX34 ∷ []) (lw0 c4 (CX34 ∷ Toff213 ∷ []) (Toff213 ∷ CX34 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Toff213 ∷ CS04⁻ ∷ []) (lem-comm-CSd04-TOFF213 c4) ▸ done

  b1 : Chain (Toff213 ∷ CCZ024 ∷ CX41 ∷ Toff234 ∷ CS04 ∷ CX34 ∷ Toff213 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ CCZ024 ∷ CX41 ∷ []) (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ CX41 ∷ CCZ034 ∷ CX41 ∷ [])
  b1 = at 5 2 (Toff213 ∷ CX34 ∷ []) (lw0 c4 (CX34 ∷ Toff213 ∷ []) (Toff213 ∷ CX34 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff213 ∷ CS04 ∷ []) (lem-comm-CS04-TOFF213 c4) ▸
       at 5 5 (CCZ034 ∷ []) (pw1 c4 (CS04 ∷ CX34 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff213 ∷ Toff234 ∷ []) (lw0 c4 (Toff234 ∷ Toff213 ∷ []) (Toff213 ∷ Toff234 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff213 ∷ CX41 ∷ Toff234 ∷ []) (lw0 c4 (CX41 ∷ Toff213 ∷ []) (Toff213 ∷ CX41 ∷ Toff234 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CX41 ∷ []) (lw0 c4 (CX41 ∷ Toff234 ∷ Toff234 ∷ []) (CX41 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ024 ∷ CCZ034 ∷ []) (pw1 c4 (CCZ034 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ024 ∷ CX41 ∷ []) (pw3 c4 (CX41 ∷ CCZ024 ∷ []) (CCZ024 ∷ CX41 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ CX41 ∷ CCZ034 ∷ CX41 ∷ []) (Bx2-3140 ∷ CCZ034 ∷ [])
  b2 = at 0 4 (Bx2-3140 ∷ []) (sym (lem-box-tQ-at0213213440 c4)) ▸
       at 1 3 (CCZ034 ∷ []) (pw2 c4 (CX41 ∷ CCZ034 ∷ CX41 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl) ▸ done


-- SWbc-box @0213213440: 11 steps
lem-SWbc-box-at0213213440 : Complete 4 → ⟪ (Sw14 ∷ Bx2-3140 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3140 ∷ []) ⟫ʷ
lem-SWbc-box-at0213213440 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw14 ∷ Bx2-3140 ∷ Sw14 ∷ []) (CX14 ∷ Bx2-3140 ∷ CX14 ∷ CCZ013 ∷ CCZ034 ∷ CCZ013 ∷ CCZ034 ∷ CCZ013 ∷ [])
  b0 = at 0 1 (CX14 ∷ CX41 ∷ CX14 ∷ []) (lw0 c4 (Sw14 ∷ []) (CX14 ∷ CX41 ∷ CX14 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CX14 ∷ CX41 ∷ CX14 ∷ []) (lw0 c4 (Sw14 ∷ []) (CX14 ∷ CX41 ∷ CX14 ∷ []) tt tt Eq.refl) ▸
       at 2 3 (Bx2-3140 ∷ CCZ013 ∷ []) (lem-CXbc-box-at0213213440 c4) ▸
       at 3 2 (CX41 ∷ CCZ034 ∷ CCZ013 ∷ []) (pw2 c4 (CCZ013 ∷ CX41 ∷ []) (CX41 ∷ CCZ034 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Bx2-3140 ∷ CCZ034 ∷ []) (lem-CXcb-box-at0213213440 c4) ▸
       at 4 2 (CX14 ∷ CCZ013 ∷ []) (pw2 c4 (CCZ013 ∷ CX14 ∷ []) (CX14 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CX14 ∷ CCZ013 ∷ CCZ034 ∷ []) (pw2 c4 (CCZ034 ∷ CX14 ∷ []) (CX14 ∷ CCZ013 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CX14 ∷ CCZ013 ∷ CCZ034 ∷ []) (pw2 c4 (CCZ034 ∷ CX14 ∷ []) (CX14 ∷ CCZ013 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CX14 ∷ Bx2-3140 ∷ CX14 ∷ CCZ013 ∷ CCZ034 ∷ CCZ013 ∷ CCZ034 ∷ CCZ013 ∷ []) (Bx2-3140 ∷ [])
  b1 = at 3 5 (CCZ013 ∷ []) (pw2 c4 (CCZ013 ∷ CCZ034 ∷ CCZ013 ∷ CCZ034 ∷ CCZ013 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Bx2-3140 ∷ CCZ013 ∷ []) (lem-CXbc-box-at0213213440 c4) ▸
       at 1 2 [] (lw4 c4 (CCZ013 ∷ CCZ013 ∷ []) [] tt tt Eq.refl) ▸ done


-- nat-SWbc @0213213440: 23 steps
lem-nat-SWbc-at0213213440 : Complete 4 → ⟪ (Sw14 ∷ Bx2-3140 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3410 ∷ []) ⟫ʷ
lem-nat-SWbc-at0213213440 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw14 ∷ Bx2-3140 ∷ Sw14 ∷ []) (CCZ234 ∷ Toff234 ∷ CCZ123 ∷ Toff312 ∷ Bx2-30 ∷ Toff312 ∷ Sw14 ∷ CCZ234 ∷ Bx2-30 ∷ Toff213 ∷ CCZ123 ∷ Bx3-240 ∷ Sw14 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff213 ∷ Bx3-240 ∷ Toff213 ∷ CCZ123 ∷ Bx3-240 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw14 ∷ []) (lw0 c4 (Sw14 ∷ CCZ123 ∷ []) (CCZ234 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff234 ∷ Sw14 ∷ []) (lw0 c4 (Sw14 ∷ Toff213 ∷ []) (Toff234 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (CCZ234 ∷ Toff324 ∷ Bx2-30 ∷ Toff324 ∷ CCZ234 ∷ Bx2-30 ∷ []) (refl) ▸
       at 2 2 (CCZ123 ∷ Sw14 ∷ []) (lw0 c4 (Sw14 ∷ CCZ234 ∷ []) (CCZ123 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff312 ∷ Sw14 ∷ []) (lw0 c4 (Sw14 ∷ Toff324 ∷ []) (Toff312 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Bx2-30 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨2·30⟩ c4) ▸
       at 5 2 (Toff312 ∷ Sw14 ∷ []) (lw0 c4 (Sw14 ∷ Toff324 ∷ []) (Toff312 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CCZ234 ∷ Toff234 ∷ CCZ123 ∷ Toff312 ∷ Bx2-30 ∷ Toff312 ∷ Sw14 ∷ CCZ234 ∷ Bx2-30 ∷ Toff213 ∷ CCZ123 ∷ Bx3-240 ∷ Sw14 ∷ []) (CCZ234 ∷ Toff234 ∷ CCZ123 ∷ Toff312 ∷ Bx2-30 ∷ Toff312 ∷ CCZ123 ∷ Bx2-30 ∷ Toff234 ∷ CCZ234 ∷ CCZ123 ∷ Toff312 ∷ Bx2-30 ∷ Sw14 ∷ Toff324 ∷ CCZ234 ∷ Bx2-30 ∷ Sw14 ∷ [])
  b1 = at 6 2 (CCZ123 ∷ Sw14 ∷ []) (lw0 c4 (Sw14 ∷ CCZ234 ∷ []) (CCZ123 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Bx2-30 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨2·30⟩ c4) ▸
       at 8 2 (Toff234 ∷ Sw14 ∷ []) (lw0 c4 (Sw14 ∷ Toff213 ∷ []) (Toff234 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ234 ∷ Sw14 ∷ []) (lw0 c4 (Sw14 ∷ CCZ123 ∷ []) (CCZ234 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 11 1 (CCZ234 ∷ Toff324 ∷ Bx2-30 ∷ Toff324 ∷ CCZ234 ∷ Bx2-30 ∷ []) (refl) ▸
       at 10 2 (CCZ123 ∷ Sw14 ∷ []) (lw0 c4 (Sw14 ∷ CCZ234 ∷ []) (CCZ123 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (Toff312 ∷ Sw14 ∷ []) (lw0 c4 (Sw14 ∷ Toff324 ∷ []) (Toff312 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (Bx2-30 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨2·30⟩ c4) ▸ done

  b2 : Chain (CCZ234 ∷ Toff234 ∷ CCZ123 ∷ Toff312 ∷ Bx2-30 ∷ Toff312 ∷ CCZ123 ∷ Bx2-30 ∷ Toff234 ∷ CCZ234 ∷ CCZ123 ∷ Toff312 ∷ Bx2-30 ∷ Sw14 ∷ Toff324 ∷ CCZ234 ∷ Bx2-30 ∷ Sw14 ∷ []) (Bx2-3410 ∷ [])
  b2 = at 13 2 (Toff312 ∷ Sw14 ∷ []) (lw0 c4 (Sw14 ∷ Toff324 ∷ []) (Toff312 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 14 2 (CCZ123 ∷ Sw14 ∷ []) (lw0 c4 (Sw14 ∷ CCZ234 ∷ []) (CCZ123 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 15 2 (Bx2-30 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨2·30⟩ c4) ▸
       at 16 2 [] (lw0 c4 (Sw14 ∷ Sw14 ∷ []) [] tt tt Eq.refl) ▸
       at 2 6 (Bx3-210 ∷ []) (refl) ▸
       at 5 6 (Bx3-210 ∷ []) (refl) ▸
       at 0 6 (Bx2-3410 ∷ []) (refl) ▸ done


-- sym-bc @0213213440: 2 steps
lem-sym-bc-at0213213440 : Complete 4 → ⟪ (Bx2-3140 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3410 ∷ []) ⟫ʷ
lem-sym-bc-at0213213440 c4 = run b0
  where
  b0 : Chain (Bx2-3140 ∷ []) (Bx2-3410 ∷ [])
  b0 = at 0 1 (Sw14 ∷ Bx2-3140 ∷ Sw14 ∷ []) (sym (lem-SWbc-box-at0213213440 c4)) ▸
       at 0 3 (Bx2-3410 ∷ []) (lem-nat-SWbc-at0213213440 c4) ▸ done


-- tP @0213243140: 7 steps
lem-tP-at0213243140 : Complete 4 → ⟪ (Toff234 ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ Toff234 ∷ []) ⟫ʷ
lem-tP-at0213243140 c4 = run b0
  where
  b0 : Chain (Toff234 ∷ Toff201 ∷ []) (Toff201 ∷ Toff234 ∷ [])
  b0 = at 0 1 (K2 ∷ CCZ234 ∷ K2⁻ ∷ []) (lw0 c4 (Toff234 ∷ []) (K2 ∷ CCZ234 ∷ K2⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 1 (K2 ∷ CCZ012 ∷ K2⁻ ∷ []) (lw4 c4 (Toff201 ∷ []) (K2 ∷ CCZ012 ∷ K2⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (K2⁻ ∷ K2 ∷ []) [] tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ CCZ234 ∷ []) (lem-cQ-at0213243140 c4) ▸
       at 2 0 (K2⁻ ∷ K2 ∷ []) (lw4 c4 [] (K2⁻ ∷ K2 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Toff201 ∷ []) (lw4 c4 (K2 ∷ CCZ012 ∷ K2⁻ ∷ []) (Toff201 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Toff234 ∷ []) (lw0 c4 (K2 ∷ CCZ234 ∷ K2⁻ ∷ []) (Toff234 ∷ []) tt tt Eq.refl) ▸ done

