{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D004 where

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
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-box-cP)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-P-box ; lem-box-tQ-at13243142 ; lem-sym-ab ; lem-sym-bc)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CSd12-TOFF034 ; lem-comm-CZ12-CCZ034)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-comm-CX21-CCZ034 ; lem-comm-SWAP13-BOX⟨0·24⟩)
-- pairs: 4 steps
lem-pairs : Complete 4 → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3412 ∷ []) ⟫ʷ
lem-pairs c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ []) (Bx0-3412 ∷ [])
  b0 = at 0 1 (Toff034 ∷ Bx0-1234 ∷ Toff034 ∷ []) (sym (lem-P-box c4)) ▸
       at 1 1 (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ []) (lem-box-cP c4) ▸
       at 4 2 [] (pw1 c4 (Toff034 ∷ Toff034 ∷ []) [] tt tt Eq.refl) ▸
       at 0 4 (Bx0-3412 ∷ []) (sym (lem-box-tQ-at13243142 c4)) ▸ done


-- box-perm-2134: 1 steps
lem-box-perm-2134 : Complete 4 → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ []) ⟫ʷ
lem-box-perm-2134 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ []) (Bx0-2134 ∷ [])
  b0 = at 0 1 (Bx0-2134 ∷ []) (lem-sym-ab c4) ▸ done


-- box-perm-1324: 1 steps
lem-box-perm-1324 : Complete 4 → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ []) ⟫ʷ
lem-box-perm-1324 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ []) (Bx0-1324 ∷ [])
  b0 = at 0 1 (Bx0-1324 ∷ []) (lem-sym-bc c4) ▸ done


-- box-perm-3412: 1 steps
lem-box-perm-3412 : Complete 4 → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3412 ∷ []) ⟫ʷ
lem-box-perm-3412 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ []) (Bx0-3412 ∷ [])
  b0 = at 0 1 (Bx0-3412 ∷ []) (lem-pairs c4) ▸ done


-- cQ @1221: 7 steps
lem-cQ-at1221 : Complete 4 → ⟪ (CCZ012 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ CCZ012 ∷ []) ⟫ʷ
lem-cQ-at1221 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ012 ∷ [])
  b0 = at 0 1 (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ034 ∷ CS02 ∷ []) (pw1 c4 (CS02 ∷ CCZ034 ∷ []) (CCZ034 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ034 ∷ CX21 ∷ []) (lem-comm-CX21-CCZ034 c4) ▸
       at 2 2 (CCZ034 ∷ CS01⁻ ∷ []) (pw2 c4 (CS01⁻ ∷ CCZ034 ∷ []) (CCZ034 ∷ CS01⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ034 ∷ CX21 ∷ []) (lem-comm-CX21-CCZ034 c4) ▸
       at 0 2 (CCZ034 ∷ CS01 ∷ []) (pw2 c4 (CS01 ∷ CCZ034 ∷ []) (CCZ034 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 1 5 (CCZ012 ∷ []) (lw4 c4 (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸ done


-- box-tQ @1221: 13 steps
lem-box-tQ-at1221 : Complete 4 → ⟪ (Bx0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) ⟫ʷ
lem-box-tQ-at1221 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-2134 ∷ []) (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ023 ∷ Toff203 ∷ CZ24 ∷ Toff203 ∷ CCZ023 ∷ CZ24 ∷ [])
  b0 = at 0 1 (CCZ012 ∷ Toff012 ∷ Bx2-034 ∷ Toff012 ∷ CCZ012 ∷ Bx2-034 ∷ []) (refl) ▸
       at 2 1 (CCZ023 ∷ Toff203 ∷ Bx0-24 ∷ Toff203 ∷ CCZ023 ∷ Bx0-24 ∷ []) (refl) ▸
       at 4 1 (CZ24 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 2 6 (CCZ034 ∷ []) (pw1 c4 (CCZ023 ∷ Toff203 ∷ CZ24 ∷ Toff203 ∷ CCZ023 ∷ CZ24 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ023 ∷ Toff203 ∷ Bx0-24 ∷ Toff203 ∷ CCZ023 ∷ Bx0-24 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 10 1 (CZ24 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ012 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ023 ∷ Toff203 ∷ CZ24 ∷ Toff203 ∷ CCZ023 ∷ CZ24 ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ [])
  b1 = at 5 6 (CCZ034 ∷ []) (pw1 c4 (CCZ023 ∷ Toff203 ∷ CZ24 ∷ Toff203 ∷ CCZ023 ∷ CZ24 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Toff012 ∷ CCZ012 ∷ CZ12 ∷ []) (lw4 c4 (CCZ012 ∷ Toff012 ∷ []) (Toff012 ∷ CCZ012 ∷ CZ12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ034 ∷ CZ12 ∷ []) (lem-comm-CZ12-CCZ034 c4) ▸
       at 1 2 (CCZ034 ∷ CCZ012 ∷ []) (lem-cQ-at1221 c4) ▸
       at 2 4 (Toff012 ∷ []) (lw4 c4 (CCZ012 ∷ CZ12 ∷ Toff012 ∷ CCZ012 ∷ []) (Toff012 ∷ []) tt tt Eq.refl) ▸ done


-- CXbc-box @1221: 17 steps
lem-CXbc-box-at1221 : Complete 4 → ⟪ (CX13 ∷ Bx0-2134 ∷ CX13 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ CCZ124 ∷ []) ⟫ʷ
lem-CXbc-box-at1221 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX13 ∷ Bx0-2134 ∷ CX13 ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CX13 ∷ CCZ014 ∷ CS14 ∷ CX21 ∷ CS14⁻ ∷ CCZ034 ∷ CX21 ∷ CS24 ∷ CX13 ∷ [])
  b0 = at 1 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-box-tQ-at1221 c4) ▸
       at 0 2 (Toff012 ∷ CX13 ∷ []) (lw4 c4 (CX13 ∷ Toff012 ∷ []) (Toff012 ∷ CX13 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ034 ∷ CX13 ∷ CCZ014 ∷ []) (pw2 c4 (CX13 ∷ CCZ034 ∷ []) (CCZ034 ∷ CX13 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff012 ∷ CCZ014 ∷ CCZ124 ∷ []) (pw3 c4 (CCZ014 ∷ Toff012 ∷ []) (Toff012 ∷ CCZ014 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff012 ∷ CX13 ∷ []) (lw4 c4 (CX13 ∷ Toff012 ∷ []) (Toff012 ∷ CX13 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CS14 ∷ CX21 ∷ CS14⁻ ∷ CX21 ∷ CS24 ∷ []) (lw0 c4 (CCZ124 ∷ []) (CS14 ∷ CX21 ∷ CS14⁻ ∷ CX21 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ034 ∷ CS24 ∷ []) (pw1 c4 (CS24 ∷ CCZ034 ∷ []) (CCZ034 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ034 ∷ CX21 ∷ []) (lem-comm-CX21-CCZ034 c4) ▸ done

  b1 : Chain (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CX13 ∷ CCZ014 ∷ CS14 ∷ CX21 ∷ CS14⁻ ∷ CCZ034 ∷ CX21 ∷ CS24 ∷ CX13 ∷ []) (Bx0-2134 ∷ CX13 ∷ CCZ124 ∷ CX13 ∷ [])
  b1 = at 7 2 (CCZ034 ∷ CS14⁻ ∷ []) (pw2 c4 (CS14⁻ ∷ CCZ034 ∷ []) (CCZ034 ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ034 ∷ CX21 ∷ []) (lem-comm-CX21-CCZ034 c4) ▸
       at 5 2 (CCZ034 ∷ CS14 ∷ []) (pw2 c4 (CS14 ∷ CCZ034 ∷ []) (CCZ034 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 6 5 (CCZ124 ∷ []) (lw0 c4 (CS14 ∷ CX21 ∷ CS14⁻ ∷ CX21 ∷ CS24 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ034 ∷ CCZ014 ∷ []) (pw2 c4 (CCZ014 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ034 ∷ CX13 ∷ CCZ014 ∷ []) (pw2 c4 (CX13 ∷ CCZ034 ∷ []) (CCZ034 ∷ CX13 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CX13 ∷ []) (pw2 c4 (CX13 ∷ CCZ014 ∷ CCZ014 ∷ []) (CX13 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx0-2134 ∷ []) (sym (lem-box-tQ-at1221 c4)) ▸ done

  b2 : Chain (Bx0-2134 ∷ CX13 ∷ CCZ124 ∷ CX13 ∷ []) (Bx0-2134 ∷ CCZ124 ∷ [])
  b2 = at 1 3 (CCZ124 ∷ []) (lw0 c4 (CX13 ∷ CCZ124 ∷ CX13 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl) ▸ done


-- CXcb-box @1221: 18 steps
lem-CXcb-box-at1221 : Complete 4 → ⟪ (CX31 ∷ Bx0-2134 ∷ CX31 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ CCZ234 ∷ []) ⟫ʷ
lem-CXcb-box-at1221 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX31 ∷ Bx0-2134 ∷ CX31 ∷ []) (Toff012 ∷ CCZ034 ∷ CX31 ∷ Toff023 ∷ CS34 ∷ CX23 ∷ Toff012 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ CCZ034 ∷ CX31 ∷ [])
  b0 = at 1 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-box-tQ-at1221 c4) ▸
       at 0 2 (Toff012 ∷ CX31 ∷ Toff023 ∷ []) (lw4 c4 (CX31 ∷ Toff012 ∷ []) (Toff012 ∷ CX31 ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ034 ∷ Toff023 ∷ CCZ234 ∷ []) (pw1 c4 (Toff023 ∷ CCZ034 ∷ []) (CCZ034 ∷ Toff023 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ034 ∷ CX31 ∷ []) (pw2 c4 (CX31 ∷ CCZ034 ∷ []) (CCZ034 ∷ CX31 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ []) (lw0 c4 (CCZ234 ∷ []) (CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (Toff012 ∷ CS24 ∷ []) (pw3 c4 (CS24 ∷ Toff012 ∷ []) (Toff012 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff012 ∷ CX23 ∷ []) (lw4 c4 (CX23 ∷ Toff012 ∷ []) (Toff012 ∷ CX23 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Toff012 ∷ CS34⁻ ∷ []) (sym (c₃ (Toff) (CS • CS • CS))) ▸ done

  b1 : Chain (Toff012 ∷ CCZ034 ∷ CX31 ∷ Toff023 ∷ CS34 ∷ CX23 ∷ Toff012 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ CCZ034 ∷ CX31 ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ CX31 ∷ CCZ234 ∷ CX31 ∷ [])
  b1 = at 5 2 (Toff012 ∷ CX23 ∷ []) (lw4 c4 (CX23 ∷ Toff012 ∷ []) (Toff012 ∷ CX23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff012 ∷ CS34 ∷ []) (sym (c₃ (Toff) (CS))) ▸
       at 5 5 (CCZ234 ∷ []) (lw0 c4 (CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff012 ∷ Toff023 ∷ []) (lw4 c4 (Toff023 ∷ Toff012 ∷ []) (Toff012 ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff012 ∷ CX31 ∷ Toff023 ∷ []) (lw4 c4 (CX31 ∷ Toff012 ∷ []) (Toff012 ∷ CX31 ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CX31 ∷ []) (lw4 c4 (CX31 ∷ Toff023 ∷ Toff023 ∷ []) (CX31 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ034 ∷ CCZ234 ∷ []) (pw1 c4 (CCZ234 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ034 ∷ CX31 ∷ []) (pw2 c4 (CX31 ∷ CCZ034 ∷ []) (CCZ034 ∷ CX31 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ CX31 ∷ CCZ234 ∷ CX31 ∷ []) (Bx0-2134 ∷ CCZ234 ∷ [])
  b2 = at 0 4 (Bx0-2134 ∷ []) (sym (lem-box-tQ-at1221 c4)) ▸
       at 1 3 (CCZ234 ∷ []) (lw0 c4 (CX31 ∷ CCZ234 ∷ CX31 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸ done


-- SWbc-box @1221: 11 steps
lem-SWbc-box-at1221 : Complete 4 → ⟪ (Sw13 ∷ Bx0-2134 ∷ Sw13 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ []) ⟫ʷ
lem-SWbc-box-at1221 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw13 ∷ Bx0-2134 ∷ Sw13 ∷ []) (CX13 ∷ Bx0-2134 ∷ CX13 ∷ CCZ124 ∷ CCZ234 ∷ CCZ124 ∷ CCZ234 ∷ CCZ124 ∷ [])
  b0 = at 0 1 (CX13 ∷ CX31 ∷ CX13 ∷ []) (lw4 c4 (Sw13 ∷ []) (CX13 ∷ CX31 ∷ CX13 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CX13 ∷ CX31 ∷ CX13 ∷ []) (lw4 c4 (Sw13 ∷ []) (CX13 ∷ CX31 ∷ CX13 ∷ []) tt tt Eq.refl) ▸
       at 2 3 (Bx0-2134 ∷ CCZ124 ∷ []) (lem-CXbc-box-at1221 c4) ▸
       at 3 2 (CX31 ∷ CCZ234 ∷ CCZ124 ∷ []) (lw0 c4 (CCZ124 ∷ CX31 ∷ []) (CX31 ∷ CCZ234 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Bx0-2134 ∷ CCZ234 ∷ []) (lem-CXcb-box-at1221 c4) ▸
       at 4 2 (CX13 ∷ CCZ124 ∷ []) (lw0 c4 (CCZ124 ∷ CX13 ∷ []) (CX13 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CX13 ∷ CCZ124 ∷ CCZ234 ∷ []) (lw0 c4 (CCZ234 ∷ CX13 ∷ []) (CX13 ∷ CCZ124 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CX13 ∷ CCZ124 ∷ CCZ234 ∷ []) (lw0 c4 (CCZ234 ∷ CX13 ∷ []) (CX13 ∷ CCZ124 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CX13 ∷ Bx0-2134 ∷ CX13 ∷ CCZ124 ∷ CCZ234 ∷ CCZ124 ∷ CCZ234 ∷ CCZ124 ∷ []) (Bx0-2134 ∷ [])
  b1 = at 3 5 (CCZ124 ∷ []) (lw0 c4 (CCZ124 ∷ CCZ234 ∷ CCZ124 ∷ CCZ234 ∷ CCZ124 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Bx0-2134 ∷ CCZ124 ∷ []) (lem-CXbc-box-at1221 c4) ▸
       at 1 2 [] (lw0 c4 (CCZ124 ∷ CCZ124 ∷ []) [] tt tt Eq.refl) ▸ done


-- nat-SWbc @1221: 23 steps
lem-nat-SWbc-at1221 : Complete 4 → ⟪ (Sw13 ∷ Bx0-2134 ∷ Sw13 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2314 ∷ []) ⟫ʷ
lem-nat-SWbc-at1221 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw13 ∷ Bx0-2134 ∷ Sw13 ∷ []) (CCZ023 ∷ Toff023 ∷ CCZ012 ∷ Toff201 ∷ Bx0-24 ∷ Toff201 ∷ Sw13 ∷ CCZ023 ∷ Bx0-24 ∷ Toff012 ∷ CCZ012 ∷ Bx2-034 ∷ Sw13 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff012 ∷ Bx2-034 ∷ Toff012 ∷ CCZ012 ∷ Bx2-034 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw13 ∷ []) (lw4 c4 (Sw13 ∷ CCZ012 ∷ []) (CCZ023 ∷ Sw13 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff023 ∷ Sw13 ∷ []) (lw4 c4 (Sw13 ∷ Toff012 ∷ []) (Toff023 ∷ Sw13 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (CCZ023 ∷ Toff203 ∷ Bx0-24 ∷ Toff203 ∷ CCZ023 ∷ Bx0-24 ∷ []) (refl) ▸
       at 2 2 (CCZ012 ∷ Sw13 ∷ []) (lw4 c4 (Sw13 ∷ CCZ023 ∷ []) (CCZ012 ∷ Sw13 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff201 ∷ Sw13 ∷ []) (lw4 c4 (Sw13 ∷ Toff203 ∷ []) (Toff201 ∷ Sw13 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Bx0-24 ∷ Sw13 ∷ []) (lem-comm-SWAP13-BOX⟨0·24⟩ c4) ▸
       at 5 2 (Toff201 ∷ Sw13 ∷ []) (lw4 c4 (Sw13 ∷ Toff203 ∷ []) (Toff201 ∷ Sw13 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CCZ023 ∷ Toff023 ∷ CCZ012 ∷ Toff201 ∷ Bx0-24 ∷ Toff201 ∷ Sw13 ∷ CCZ023 ∷ Bx0-24 ∷ Toff012 ∷ CCZ012 ∷ Bx2-034 ∷ Sw13 ∷ []) (CCZ023 ∷ Toff023 ∷ CCZ012 ∷ Toff201 ∷ Bx0-24 ∷ Toff201 ∷ CCZ012 ∷ Bx0-24 ∷ Toff023 ∷ CCZ023 ∷ CCZ012 ∷ Toff201 ∷ Bx0-24 ∷ Sw13 ∷ Toff203 ∷ CCZ023 ∷ Bx0-24 ∷ Sw13 ∷ [])
  b1 = at 6 2 (CCZ012 ∷ Sw13 ∷ []) (lw4 c4 (Sw13 ∷ CCZ023 ∷ []) (CCZ012 ∷ Sw13 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Bx0-24 ∷ Sw13 ∷ []) (lem-comm-SWAP13-BOX⟨0·24⟩ c4) ▸
       at 8 2 (Toff023 ∷ Sw13 ∷ []) (lw4 c4 (Sw13 ∷ Toff012 ∷ []) (Toff023 ∷ Sw13 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ023 ∷ Sw13 ∷ []) (lw4 c4 (Sw13 ∷ CCZ012 ∷ []) (CCZ023 ∷ Sw13 ∷ []) tt tt Eq.refl) ▸
       at 11 1 (CCZ023 ∷ Toff203 ∷ Bx0-24 ∷ Toff203 ∷ CCZ023 ∷ Bx0-24 ∷ []) (refl) ▸
       at 10 2 (CCZ012 ∷ Sw13 ∷ []) (lw4 c4 (Sw13 ∷ CCZ023 ∷ []) (CCZ012 ∷ Sw13 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (Toff201 ∷ Sw13 ∷ []) (lw4 c4 (Sw13 ∷ Toff203 ∷ []) (Toff201 ∷ Sw13 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (Bx0-24 ∷ Sw13 ∷ []) (lem-comm-SWAP13-BOX⟨0·24⟩ c4) ▸ done

  b2 : Chain (CCZ023 ∷ Toff023 ∷ CCZ012 ∷ Toff201 ∷ Bx0-24 ∷ Toff201 ∷ CCZ012 ∷ Bx0-24 ∷ Toff023 ∷ CCZ023 ∷ CCZ012 ∷ Toff201 ∷ Bx0-24 ∷ Sw13 ∷ Toff203 ∷ CCZ023 ∷ Bx0-24 ∷ Sw13 ∷ []) (Bx0-2314 ∷ [])
  b2 = at 13 2 (Toff201 ∷ Sw13 ∷ []) (lw4 c4 (Sw13 ∷ Toff203 ∷ []) (Toff201 ∷ Sw13 ∷ []) tt tt Eq.refl) ▸
       at 14 2 (CCZ012 ∷ Sw13 ∷ []) (lw4 c4 (Sw13 ∷ CCZ023 ∷ []) (CCZ012 ∷ Sw13 ∷ []) tt tt Eq.refl) ▸
       at 15 2 (Bx0-24 ∷ Sw13 ∷ []) (lem-comm-SWAP13-BOX⟨0·24⟩ c4) ▸
       at 16 2 [] (lw4 c4 (Sw13 ∷ Sw13 ∷ []) [] tt tt Eq.refl) ▸
       at 2 6 (Bx2-014 ∷ []) (refl) ▸
       at 5 6 (Bx2-014 ∷ []) (refl) ▸
       at 0 6 (Bx0-2314 ∷ []) (refl) ▸ done


-- sym-bc @1221: 2 steps
lem-sym-bc-at1221 : Complete 4 → ⟪ (Bx0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2314 ∷ []) ⟫ʷ
lem-sym-bc-at1221 c4 = run b0
  where
  b0 : Chain (Bx0-2134 ∷ []) (Bx0-2314 ∷ [])
  b0 = at 0 1 (Sw13 ∷ Bx0-2134 ∷ Sw13 ∷ []) (sym (lem-SWbc-box-at1221 c4)) ▸
       at 0 3 (Bx0-2314 ∷ []) (lem-nat-SWbc-at1221 c4) ▸ done


-- box-perm-2314: 2 steps
lem-box-perm-2314 : Complete 4 → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2314 ∷ []) ⟫ʷ
lem-box-perm-2314 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ []) (Bx0-2314 ∷ [])
  b0 = at 0 1 (Bx0-2134 ∷ []) (lem-sym-ab c4) ▸
       at 0 1 (Bx0-2314 ∷ []) (lem-sym-bc-at1221 c4) ▸ done


-- tP @1221: 7 steps
lem-tP-at1221 : Complete 4 → ⟪ (Toff012 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ Toff012 ∷ []) ⟫ʷ
lem-tP-at1221 c4 = run b0
  where
  b0 : Chain (Toff012 ∷ Toff034 ∷ []) (Toff034 ∷ Toff012 ∷ [])
  b0 = at 0 1 (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (lw4 c4 (Toff012 ∷ []) (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 1 (K0 ∷ CCZ034 ∷ K0⁻ ∷ []) (pw1 c4 (Toff034 ∷ []) (K0 ∷ CCZ034 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (K0⁻ ∷ K0 ∷ []) [] tt tt Eq.refl) ▸
       at 1 2 (CCZ034 ∷ CCZ012 ∷ []) (lem-cQ-at1221 c4) ▸
       at 2 0 (K0⁻ ∷ K0 ∷ []) (lw4 c4 [] (K0⁻ ∷ K0 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Toff034 ∷ []) (pw1 c4 (K0 ∷ CCZ034 ∷ K0⁻ ∷ []) (Toff034 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Toff012 ∷ []) (lw4 c4 (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (Toff012 ∷ []) tt tt Eq.refl) ▸ done


-- P-box @1221: 8 steps
lem-P-box-at1221 : Complete 4 → ⟪ (Toff034 ∷ Bx0-2134 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ []) ⟫ʷ
lem-P-box-at1221 c4 = run b0
  where
  b0 : Chain (Toff034 ∷ Bx0-2134 ∷ Toff034 ∷ []) (Bx0-2134 ∷ [])
  b0 = at 1 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-box-tQ-at1221 c4) ▸
       at 0 2 (Toff012 ∷ Toff034 ∷ []) (sym (lem-tP-at1221 c4)) ▸
       at 1 2 (CCZ034 ∷ CZ34 ∷ Toff034 ∷ []) (pw1 c4 (Toff034 ∷ CCZ034 ∷ []) (CCZ034 ∷ CZ34 ∷ Toff034 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff012 ∷ Toff034 ∷ []) (sym (lem-tP-at1221 c4)) ▸
       at 4 3 (CCZ034 ∷ CZ34 ∷ []) (pw1 c4 (Toff034 ∷ CCZ034 ∷ Toff034 ∷ []) (CCZ034 ∷ CZ34 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff012 ∷ CZ34 ∷ []) (sym (c₃ (Toff) (CZ))) ▸
       at 3 3 (CCZ034 ∷ []) (pw1 c4 (CZ34 ∷ CCZ034 ∷ CZ34 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx0-2134 ∷ []) (sym (lem-box-tQ-at1221 c4)) ▸ done


-- VPQ @1221: 14 steps
lem-VPQ-at1221 : Complete 4 → ⟪ (Toff012 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ []) ⟫ʷ
lem-VPQ-at1221 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff012 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ []) (CS34⁻ ∷ CS12⁻ ∷ S0 ∷ Toff034 ∷ Toff012 ∷ S0⁻ ∷ [])
  b0 = at 0 2 (CS12⁻ ∷ S0 ∷ Toff012 ∷ S0⁻ ∷ []) (lw4 c4 (Toff012 ∷ CCZ012 ∷ []) (CS12⁻ ∷ S0 ∷ Toff012 ∷ S0⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CS34⁻ ∷ S0 ∷ Toff034 ∷ S0⁻ ∷ []) (pw1 c4 (Toff034 ∷ CCZ034 ∷ []) (CS34⁻ ∷ S0 ∷ Toff034 ∷ S0⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CS34⁻ ∷ S0⁻ ∷ []) (c₁ (S • S • S) ((CS • CS • CS) ↑ ↑)) ▸
       at 2 2 (CS34⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (CS • CS • CS)) ▸
       at 1 2 (CS34⁻ ∷ S0 ∷ []) (c₁ (S) ((CS • CS • CS) ↑ ↑)) ▸
       at 0 2 (CS34⁻ ∷ CS12⁻ ∷ []) (c₃ ((CS • CS • CS) ↑) (CS • CS • CS)) ▸
       at 4 2 [] (lw4 c4 (S0⁻ ∷ S0 ∷ []) [] tt tt Eq.refl) ▸
       at 3 2 (Toff034 ∷ Toff012 ∷ []) (lem-tP-at1221 c4) ▸ done

  b1 : Chain (CS34⁻ ∷ CS12⁻ ∷ S0 ∷ Toff034 ∷ Toff012 ∷ S0⁻ ∷ []) (Toff034 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ [])
  b1 = at 4 0 (S0⁻ ∷ S0 ∷ []) (lw4 c4 [] (S0⁻ ∷ S0 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (S0 ∷ CS12⁻ ∷ []) (sym (c₁ (S) (CS • CS • CS))) ▸
       at 2 2 (Toff034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-TOFF034 c4) ▸
       at 3 2 (S0⁻ ∷ CS12⁻ ∷ []) (sym (c₁ (S • S • S) (CS • CS • CS))) ▸
       at 0 4 (Toff034 ∷ CCZ034 ∷ []) (pw1 c4 (CS34⁻ ∷ S0 ∷ Toff034 ∷ S0⁻ ∷ []) (Toff034 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Toff012 ∷ CCZ012 ∷ []) (lw4 c4 (CS12⁻ ∷ S0 ∷ Toff012 ∷ S0⁻ ∷ []) (Toff012 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸ done


-- QVQ @1221: 3 steps
lem-QVQ-at1221 : Complete 4 → ⟪ (CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ Toff012 ∷ CCZ012 ∷ Toff034 ∷ []) ⟫ʷ
lem-QVQ-at1221 c4 = run b0
  where
  b0 : Chain (CCZ034 ∷ Toff012 ∷ CCZ012 ∷ CCZ034 ∷ []) (Toff034 ∷ Toff012 ∷ CCZ012 ∷ Toff034 ∷ [])
  b0 = at 0 0 (Toff034 ∷ Toff034 ∷ []) (pw1 c4 [] (Toff034 ∷ Toff034 ∷ []) tt tt Eq.refl) ▸
       at 1 4 (Toff012 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ []) (sym (lem-VPQ-at1221 c4)) ▸
       at 4 2 [] (pw1 c4 (CCZ034 ∷ CCZ034 ∷ []) [] tt tt Eq.refl) ▸ done

