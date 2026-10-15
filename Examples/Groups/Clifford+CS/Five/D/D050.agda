{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D050 where

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
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-box-cP-at0210243143 ; lem-box-tQ-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-box-cP-at122441)
open import Examples.Groups.Clifford+CS.Five.D.D006 using (lem-box-tQ-at122331)
open import Examples.Groups.Clifford+CS.Five.D.D015 using (lem-sym-ab-at1221)
open import Examples.Groups.Clifford+CS.Five.D.D043 using (lem-pairs-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D046 using (lem-CSdu-box-3-at122441 ; lem-CSu-box-3-at122441)
open import Examples.Groups.Clifford+CS.Five.D.D047 using (lem-box-perm-1342-at0210243143 ; lem-box-perm-1432-at122441 ; lem-sym-ab-at021021)
open import Examples.Groups.Clifford+CS.Five.D.D049 using (lem-P-box-at022330 ; lem-VPQ-at022330 ; lem-box-box-1-at021021 ; lem-box-perm-1432-at1221 ; lem-sym-bc-at0220 ; lem-tP-at022330)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-CS13-CCZ024 ; lem-comm-CSd13-CCZ024 ; lem-comm-CX13-CCZ024)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-comm-CSd14-TOFF023 ; lem-comm-CX23-CCZ014)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-comm-CSd24-TOFF013)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-comm-CZ13-CCZ024 ; lem-comm-SWAP13-BOX⟨0·24⟩)
open import Examples.Groups.Clifford+CS.Five.D.R012 using (lem-comm-CS14-TOFF023 ; lem-comm-CS24-TOFF013)
open import Examples.Groups.Clifford+CS.Five.D.R016 using (lem-comm-CCZ024-CX13 ; lem-comm-TOFF213-CX04)
open import Examples.Groups.Clifford+CS.Five.D.R018 using (lem-comm-CCZ024-CX31 ; lem-comm-CCZ124-CS03)
-- QVQ @022330: 3 steps
lem-QVQ-at022330 : Complete 4 → ⟪ (CCZ024 ∷ Toff213 ∷ CCZ123 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ Toff213 ∷ CCZ123 ∷ Toff204 ∷ []) ⟫ʷ
lem-QVQ-at022330 c4 = run b0
  where
  b0 : Chain (CCZ024 ∷ Toff213 ∷ CCZ123 ∷ CCZ024 ∷ []) (Toff204 ∷ Toff213 ∷ CCZ123 ∷ Toff204 ∷ [])
  b0 = at 0 0 (Toff204 ∷ Toff204 ∷ []) (pw1 c4 [] (Toff204 ∷ Toff204 ∷ []) tt tt Eq.refl) ▸
       at 1 4 (Toff213 ∷ CCZ123 ∷ Toff204 ∷ CCZ024 ∷ []) (sym (lem-VPQ-at022330 c4)) ▸
       at 4 2 [] (pw1 c4 (CCZ024 ∷ CCZ024 ∷ []) [] tt tt Eq.refl) ▸ done


-- box-cP @022330: 12 steps
lem-box-cP-at022330 : Complete 4 → ⟪ (Bx2-1304 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ []) ⟫ʷ
lem-box-cP-at022330 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx2-1304 ∷ []) (CCZ123 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ CCZ012 ∷ Toff102 ∷ CZ14 ∷ Toff102 ∷ CCZ012 ∷ CZ14 ∷ [])
  b0 = at 0 1 (CCZ123 ∷ Toff213 ∷ Bx1-204 ∷ Toff213 ∷ CCZ123 ∷ Bx1-204 ∷ []) (refl) ▸
       at 2 1 (CCZ012 ∷ Toff102 ∷ Bx2-14 ∷ Toff102 ∷ CCZ012 ∷ Bx2-14 ∷ []) (refl) ▸
       at 4 1 (CZ14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 2 6 (CCZ024 ∷ []) (pw3 c4 (CCZ012 ∷ Toff102 ∷ CZ14 ∷ Toff102 ∷ CCZ012 ∷ CZ14 ∷ []) (CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ012 ∷ Toff102 ∷ Bx2-14 ∷ Toff102 ∷ CCZ012 ∷ Bx2-14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 10 1 (CZ14 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ123 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ CCZ012 ∷ Toff102 ∷ CZ14 ∷ Toff102 ∷ CCZ012 ∷ CZ14 ∷ []) (CCZ123 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ [])
  b1 = at 5 6 (CCZ024 ∷ []) (pw3 c4 (CCZ012 ∷ Toff102 ∷ CZ14 ∷ Toff102 ∷ CCZ012 ∷ CZ14 ∷ []) (CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Toff204 ∷ Toff213 ∷ CCZ123 ∷ Toff204 ∷ []) (lem-QVQ-at022330 c4) ▸
       at 1 2 (Toff204 ∷ Toff213 ∷ []) (lem-tP-at022330 c4) ▸
       at 2 2 [] (lw4 c4 (Toff213 ∷ Toff213 ∷ []) [] tt tt Eq.refl) ▸ done


-- pairs @022330: 4 steps
lem-pairs-at022330 : Complete 4 → ⟪ (Bx2-1304 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ []) ⟫ʷ
lem-pairs-at022330 c4 = run b0
  where
  b0 : Chain (Bx2-1304 ∷ []) (Bx2-0413 ∷ [])
  b0 = at 0 1 (Toff204 ∷ Bx2-1304 ∷ Toff204 ∷ []) (sym (lem-P-box-at022330 c4)) ▸
       at 1 1 (CCZ123 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ []) (lem-box-cP-at022330 c4) ▸
       at 4 2 [] (pw1 c4 (Toff204 ∷ Toff204 ∷ []) [] tt tt Eq.refl) ▸
       at 0 4 (Bx2-0413 ∷ []) (sym (lem-box-tQ-at0210243143 c4)) ▸ done


-- box-perm-1423 @021021: 3 steps
lem-box-perm-1423-at021021 : Complete 4 → ⟪ (Bx2-0134 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ []) ⟫ʷ
lem-box-perm-1423-at021021 c4 = run b0
  where
  b0 : Chain (Bx2-0134 ∷ []) (Bx2-0413 ∷ [])
  b0 = at 0 1 (Bx2-1034 ∷ []) (lem-sym-ab-at021021 c4) ▸
       at 0 1 (Bx2-1304 ∷ []) (lem-sym-bc-at0220 c4) ▸
       at 0 1 (Bx2-0413 ∷ []) (lem-pairs-at022330 c4) ▸ done


-- CSu-box-3 @0210243143: 17 steps
lem-CSu-box-3-at0210243143 : Complete 4 → ⟪ (CS12 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ CS12 ∷ []) ⟫ʷ
lem-CSu-box-3-at0210243143 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS12 ∷ Bx2-0413 ∷ []) (CCZ024 ∷ Toff213 ∷ CS12 ∷ CS13 ∷ CS13 ∷ CCZ024 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ Toff213 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 0 2 (CCZ024 ∷ CS12 ∷ []) (pw3 c4 (CS12 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff213 ∷ CS12 ∷ CS13 ∷ CCZ123 ∷ []) (lw4 c4 (CS12 ∷ Toff213 ∷ []) (Toff213 ∷ CS12 ∷ CS13 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ []) (lw4 c4 (CCZ123 ∷ []) (CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ024 ∷ CS23 ∷ []) (pw1 c4 (CS23 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ024 ∷ CX21 ∷ []) (pw3 c4 (CX21 ∷ CCZ024 ∷ []) (CCZ024 ∷ CX21 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-CCZ024 c4) ▸
       at 5 2 (CCZ024 ∷ CX21 ∷ []) (pw3 c4 (CX21 ∷ CCZ024 ∷ []) (CCZ024 ∷ CX21 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CCZ024 ∷ Toff213 ∷ CS12 ∷ CS13 ∷ CS13 ∷ CCZ024 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ Toff213 ∷ []) (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS12 ∷ [])
  b1 = at 4 2 (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 c4) ▸
       at 5 5 (CCZ123 ∷ []) (lw4 c4 (CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 c4) ▸
       at 2 2 (CCZ024 ∷ CS12 ∷ []) (pw3 c4 (CS12 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff213 ∷ CZ13 ∷ CCZ123 ∷ []) (lw4 c4 (CCZ123 ∷ Toff213 ∷ []) (Toff213 ∷ CZ13 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff213 ∷ CS13 ∷ []) (lw4 c4 (CS13 ∷ Toff213 ∷ []) (Toff213 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff213 ∷ CS12 ∷ CS13 ∷ CCZ123 ∷ []) (lw4 c4 (CS12 ∷ Toff213 ∷ []) (Toff213 ∷ CS12 ∷ CS13 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 4 6 (CS12 ∷ []) (lw4 c4 (CS12 ∷ CS13 ∷ CCZ123 ∷ CS13 ∷ CZ13 ∷ CCZ123 ∷ []) (CS12 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS12 ∷ []) (Bx2-0413 ∷ CS12 ∷ [])
  b2 = at 0 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸ done


-- CSdu-box-3 @0210243143: 17 steps
lem-CSdu-box-3-at0210243143 : Complete 4 → ⟪ (CS12⁻ ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ CS12⁻ ∷ []) ⟫ʷ
lem-CSdu-box-3-at0210243143 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS12⁻ ∷ Bx2-0413 ∷ []) (CCZ024 ∷ Toff213 ∷ CS12⁻ ∷ CS13⁻ ∷ CS13 ∷ CCZ024 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ Toff213 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 0 2 (CCZ024 ∷ CS12⁻ ∷ []) (pw3 c4 (CS12⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff213 ∷ CS12⁻ ∷ CS13⁻ ∷ CCZ123 ∷ []) (lw4 c4 (CS12⁻ ∷ Toff213 ∷ []) (Toff213 ∷ CS12⁻ ∷ CS13⁻ ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ []) (lw4 c4 (CCZ123 ∷ []) (CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ024 ∷ CS23 ∷ []) (pw1 c4 (CS23 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ024 ∷ CX21 ∷ []) (pw3 c4 (CX21 ∷ CCZ024 ∷ []) (CCZ024 ∷ CX21 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-CCZ024 c4) ▸
       at 5 2 (CCZ024 ∷ CX21 ∷ []) (pw3 c4 (CX21 ∷ CCZ024 ∷ []) (CCZ024 ∷ CX21 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CCZ024 ∷ Toff213 ∷ CS12⁻ ∷ CS13⁻ ∷ CS13 ∷ CCZ024 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ Toff213 ∷ []) (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS12⁻ ∷ [])
  b1 = at 4 2 (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 c4) ▸
       at 5 5 (CCZ123 ∷ []) (lw4 c4 (CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-CCZ024 c4) ▸
       at 2 2 (CCZ024 ∷ CS12⁻ ∷ []) (pw3 c4 (CS12⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff213 ∷ CZ13 ∷ CCZ123 ∷ []) (lw4 c4 (CCZ123 ∷ Toff213 ∷ []) (Toff213 ∷ CZ13 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff213 ∷ CS13⁻ ∷ []) (lw4 c4 (CS13⁻ ∷ Toff213 ∷ []) (Toff213 ∷ CS13⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff213 ∷ CS12⁻ ∷ CS13⁻ ∷ CCZ123 ∷ []) (lw4 c4 (CS12⁻ ∷ Toff213 ∷ []) (Toff213 ∷ CS12⁻ ∷ CS13⁻ ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 4 6 (CS12⁻ ∷ []) (lw4 c4 (CS12⁻ ∷ CS13⁻ ∷ CCZ123 ∷ CS13⁻ ∷ CZ13 ∷ CCZ123 ∷ []) (CS12⁻ ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS12⁻ ∷ []) (Bx2-0413 ∷ CS12⁻ ∷ [])
  b2 = at 0 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸ done


-- F4-CS0-CS2: 284 steps
lem-F4-CS0-CS2 : Complete 4 → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS0-CS2 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (run b35)))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ CCZ024 ∷ Toff013 ∷ X4 ∷ CZ02 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b0 = at 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 5 1 (CS12 ∷ []) (refl) ▸
       at 7 1 (CS12⁻ ∷ []) (refl) ▸
       at 3 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 2 2 (CCZ024 ∷ X4 ∷ CZ02 ∷ []) (pw3 c4 (X4 ∷ CCZ024 ∷ []) (CCZ024 ∷ X4 ∷ CZ02 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff013 ∷ CZ02 ∷ CCZ123 ∷ []) (lw4 c4 (CZ02 ∷ Toff013 ∷ []) (Toff013 ∷ CZ02 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • Toff • Swap ↑ ↑) (X))) ▸
       at 6 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (lw4 c4 (CCZ123 ∷ []) (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (X4 ∷ Sb2-0-41-3 ∷ CCZ024 ∷ Toff013 ∷ X4 ∷ CZ02 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (X4 ∷ Sb2-0-41-3 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ X4 ∷ CZ02 ∷ CZ02 ∷ CCZ123 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b1 = at 10 2 (CCZ024 ∷ CS12 ∷ []) (pw3 c4 (CS12 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸
       at 8 2 (CCZ024 ∷ CS23⁻ ∷ []) (pw1 c4 (CS23⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ CS23⁻ ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸
       at 6 2 (CCZ024 ∷ CS23 ∷ []) (pw1 c4 (CS23 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 7 5 (CCZ123 ∷ []) (lw4 c4 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ024 ∷ CZ02 ∷ []) (pw3 c4 (CZ02 ∷ CCZ024 ∷ []) (CCZ024 ∷ CZ02 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ024 ∷ X4 ∷ CZ02 ∷ []) (pw3 c4 (X4 ∷ CCZ024 ∷ []) (CCZ024 ∷ X4 ∷ CZ02 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (X4 ∷ Sb2-0-41-3 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ X4 ∷ CZ02 ∷ CZ02 ∷ CCZ123 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (X4 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS03⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b2 = at 5 3 (X4 ∷ []) (lw3 c4 (X4 ∷ CZ02 ∷ CZ02 ∷ []) (X4 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Toff013 ∷ CCZ123 ∷ []) (lw4 c4 (CCZ123 ∷ Toff013 ∷ []) (Toff013 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • Toff • Swap ↑ ↑) (X))) ▸
       at 2 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 5 1 (CS03⁻ ∷ []) (refl) ▸
       at 5 2 (Bx0-2431 ∷ CS03⁻ ∷ []) (lem-CSdu-box-3-at122441 c4) ▸
       at 5 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸ done

  b3 : Chain (X4 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS03⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (X4 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ CCZ024 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS03⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b3 = at 4 1 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (lw0 c4 (Toff314 ∷ []) (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 10 2 (CCZ024 ∷ K3⁻ ∷ []) (pw1 c4 (K3⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ024 ∷ CS14 ∷ []) (pw3 c4 (CS14 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸
       at 7 2 (CCZ024 ∷ CS34⁻ ∷ []) (pw1 c4 (CS34⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ CS34⁻ ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸
       at 5 2 (CCZ024 ∷ CS34 ∷ []) (pw1 c4 (CS34 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ024 ∷ K3 ∷ []) (pw1 c4 (K3 ∷ CCZ024 ∷ []) (CCZ024 ∷ K3 ∷ []) tt tt Eq.refl) ▸ done

  b4 : Chain (X4 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ CCZ024 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS03⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (X4 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ CCZ024 ∷ Toff013 ∷ Toff014 ∷ K3 ∷ CS34 ∷ CCZ024 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ Toff013 ∷ CS03⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b4 = at 5 7 (Toff314 ∷ []) (lw0 c4 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (Toff314 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff013 ∷ Toff014 ∷ Toff314 ∷ []) (pw2 c4 (Toff314 ∷ Toff013 ∷ []) (Toff013 ∷ Toff014 ∷ Toff314 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (lw0 c4 (Toff314 ∷ []) (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 13 2 (CCZ024 ∷ K3⁻ ∷ []) (pw1 c4 (K3⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 12 2 (CCZ024 ∷ CS14 ∷ []) (pw3 c4 (CS14 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸
       at 10 2 (CCZ024 ∷ CS34⁻ ∷ []) (pw1 c4 (CS34⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ CS34⁻ ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸ done

  b5 : Chain (X4 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ CCZ024 ∷ Toff013 ∷ Toff014 ∷ K3 ∷ CS34 ∷ CCZ024 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ Toff013 ∷ CS03⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (X4 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff014 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ Toff013 ∷ CX12 ∷ CS14 ∷ Toff014 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b5 = at 8 2 (CCZ024 ∷ CS34 ∷ []) (pw1 c4 (CS34 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ024 ∷ K3 ∷ []) (pw1 c4 (K3 ∷ CCZ024 ∷ []) (CCZ024 ∷ K3 ∷ []) tt tt Eq.refl) ▸
       at 8 7 (Toff314 ∷ []) (lw0 c4 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (Toff314 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ024 ∷ Toff014 ∷ CCZ124 ∷ []) (pw3 c4 (Toff014 ∷ CCZ024 ∷ []) (CCZ024 ∷ Toff014 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (Toff013 ∷ Toff014 ∷ Toff314 ∷ []) (pw2 c4 (Toff314 ∷ Toff013 ∷ []) (Toff013 ∷ Toff014 ∷ Toff314 ∷ []) tt tt Eq.refl) ▸
       at 8 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (lw0 c4 (CCZ124 ∷ []) (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (Toff013 ∷ CS14 ∷ []) (pw2 c4 (CS14 ∷ Toff013 ∷ []) (Toff013 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (Toff013 ∷ CX12 ∷ []) (lw4 c4 (CX12 ∷ Toff013 ∷ []) (Toff013 ∷ CX12 ∷ []) tt tt Eq.refl) ▸ done

  b6 : Chain (X4 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff014 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ Toff013 ∷ CX12 ∷ CS14 ∷ Toff014 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (X4 ∷ Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Bx0-2431 ∷ CCZ124 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b6 = at 10 2 (Toff013 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-TOFF013 c4) ▸
       at 9 2 (Toff013 ∷ CX12 ∷ []) (lw4 c4 (CX12 ∷ Toff013 ∷ []) (Toff013 ∷ CX12 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (Toff013 ∷ CS24 ∷ []) (lem-comm-CS24-TOFF013 c4) ▸
       at 9 5 (CCZ124 ∷ []) (lw0 c4 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff013 ∷ Toff014 ∷ []) (pw2 c4 (Toff014 ∷ Toff013 ∷ []) (Toff013 ∷ Toff014 ∷ []) tt tt Eq.refl) ▸
       at 8 3 (CCZ124 ∷ []) (pw3 c4 (Toff014 ∷ CCZ124 ∷ Toff014 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 4 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 3 1 (CS03 ∷ []) (refl) ▸ done

  b7 : Chain (X4 ∷ Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Bx0-2431 ∷ CCZ124 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (X4 ∷ Bx2-0413 ∷ K3 ∷ CS34 ∷ CCZ024 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS03 ∷ CCZ124 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b7 = at 3 2 (Bx0-2431 ∷ CS03 ∷ []) (lem-CSu-box-3-at122441 c4) ▸
       at 3 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 2 1 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (lw0 c4 (Toff314 ∷ []) (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ024 ∷ K3⁻ ∷ []) (pw1 c4 (K3⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ024 ∷ CS14 ∷ []) (pw3 c4 (CS14 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸
       at 5 2 (CCZ024 ∷ CS34⁻ ∷ []) (pw1 c4 (CS34⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ CS34⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸ done

  b8 : Chain (X4 ∷ Bx2-0413 ∷ K3 ∷ CS34 ∷ CCZ024 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS03 ∷ CCZ124 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (X4 ∷ Bx2-0413 ∷ CCZ024 ∷ Toff013 ∷ Toff014 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CCZ024 ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ Toff013 ∷ CS03 ∷ CCZ124 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b8 = at 3 2 (CCZ024 ∷ CS34 ∷ []) (pw1 c4 (CS34 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ024 ∷ K3 ∷ []) (pw1 c4 (K3 ∷ CCZ024 ∷ []) (CCZ024 ∷ K3 ∷ []) tt tt Eq.refl) ▸
       at 3 7 (Toff314 ∷ []) (lw0 c4 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (Toff314 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff013 ∷ Toff014 ∷ Toff314 ∷ []) (pw2 c4 (Toff314 ∷ Toff013 ∷ []) (Toff013 ∷ Toff014 ∷ Toff314 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (lw0 c4 (Toff314 ∷ []) (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 11 2 (CCZ024 ∷ K3⁻ ∷ []) (pw1 c4 (K3⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 10 2 (CCZ024 ∷ CS14 ∷ []) (pw3 c4 (CS14 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸ done

  b9 : Chain (X4 ∷ Bx2-0413 ∷ CCZ024 ∷ Toff013 ∷ Toff014 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CCZ024 ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ Toff013 ∷ CS03 ∷ CCZ124 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (X4 ∷ Bx2-0413 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff014 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ Toff013 ∷ Toff014 ∷ Toff314 ∷ CS03 ∷ CCZ124 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b9 = at 8 2 (CCZ024 ∷ CS34⁻ ∷ []) (pw1 c4 (CS34⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ CS34⁻ ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸
       at 6 2 (CCZ024 ∷ CS34 ∷ []) (pw1 c4 (CS34 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ024 ∷ K3 ∷ []) (pw1 c4 (K3 ∷ CCZ024 ∷ []) (CCZ024 ∷ K3 ∷ []) tt tt Eq.refl) ▸
       at 6 7 (Toff314 ∷ []) (lw0 c4 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (Toff314 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ024 ∷ Toff014 ∷ CCZ124 ∷ []) (pw3 c4 (Toff014 ∷ CCZ024 ∷ []) (CCZ024 ∷ Toff014 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff013 ∷ Toff014 ∷ Toff314 ∷ []) (pw2 c4 (Toff314 ∷ Toff013 ∷ []) (Toff013 ∷ Toff014 ∷ Toff314 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (lw0 c4 (CCZ124 ∷ []) (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) tt tt Eq.refl) ▸ done

  b10 : Chain (X4 ∷ Bx2-0413 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff014 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ Toff013 ∷ Toff014 ∷ Toff314 ∷ CS03 ∷ CCZ124 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (X4 ∷ Bx2-0413 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ124 ∷ Toff314 ∷ CS03 ∷ CCZ124 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b10 = at 10 2 (Toff013 ∷ CS14 ∷ []) (pw2 c4 (CS14 ∷ Toff013 ∷ []) (Toff013 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (Toff013 ∷ CX12 ∷ []) (lw4 c4 (CX12 ∷ Toff013 ∷ []) (Toff013 ∷ CX12 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (Toff013 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-TOFF013 c4) ▸
       at 7 2 (Toff013 ∷ CX12 ∷ []) (lw4 c4 (CX12 ∷ Toff013 ∷ []) (Toff013 ∷ CX12 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Toff013 ∷ CS24 ∷ []) (lem-comm-CS24-TOFF013 c4) ▸
       at 7 5 (CCZ124 ∷ []) (lw0 c4 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff013 ∷ Toff014 ∷ []) (pw2 c4 (Toff014 ∷ Toff013 ∷ []) (Toff013 ∷ Toff014 ∷ []) tt tt Eq.refl) ▸
       at 6 3 (CCZ124 ∷ []) (pw3 c4 (Toff014 ∷ CCZ124 ∷ Toff014 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl) ▸ done

  b11 : Chain (X4 ∷ Bx2-0413 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ124 ∷ Toff314 ∷ CS03 ∷ CCZ124 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (CCZ024 ∷ X4 ∷ CZ02 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Bx2-0413 ∷ CCZ124 ∷ Toff314 ∷ CS03 ∷ CCZ124 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b11 = at 2 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 1 1 (Bx2-0134 ∷ []) (lem-box-perm-1342-at0210243143 c4) ▸
       at 2 1 (Bx0-2134 ∷ []) (lem-box-perm-1432-at122441 c4) ▸
       at 1 2 (Bx0-2134 ∷ Bx2-0134 ∷ []) (lem-box-box-1-at021021 c4) ▸
       at 1 1 (Bx0-2431 ∷ []) (lem-box-perm-1432-at1221 c4) ▸
       at 2 1 (Bx2-0413 ∷ []) (lem-box-perm-1423-at021021 c4) ▸
       at 1 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 0 2 (CCZ024 ∷ X4 ∷ CZ02 ∷ []) (pw3 c4 (X4 ∷ CCZ024 ∷ []) (CCZ024 ∷ X4 ∷ CZ02 ∷ []) tt tt Eq.refl) ▸ done

  b12 : Chain (CCZ024 ∷ X4 ∷ CZ02 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Bx2-0413 ∷ CCZ124 ∷ Toff314 ∷ CS03 ∷ CCZ124 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (CCZ024 ∷ Toff013 ∷ X4 ∷ CZ02 ∷ CCZ024 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ Toff013 ∷ Bx2-0413 ∷ CCZ124 ∷ Toff314 ∷ CS03 ∷ CCZ124 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b12 = at 2 2 (Toff013 ∷ CZ02 ∷ CCZ123 ∷ []) (lw4 c4 (CZ02 ∷ Toff013 ∷ []) (Toff013 ∷ CZ02 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • Toff • Swap ↑ ↑) (X))) ▸
       at 4 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (lw4 c4 (CCZ123 ∷ []) (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ024 ∷ CS12 ∷ []) (pw3 c4 (CS12 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸
       at 6 2 (CCZ024 ∷ CS23⁻ ∷ []) (pw1 c4 (CS23⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ CS23⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸
       at 4 2 (CCZ024 ∷ CS23 ∷ []) (pw1 c4 (CS23 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS23 ∷ []) tt tt Eq.refl) ▸ done

  b13 : Chain (CCZ024 ∷ Toff013 ∷ X4 ∷ CZ02 ∷ CCZ024 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ Toff013 ∷ Bx2-0413 ∷ CCZ124 ∷ Toff314 ∷ CS03 ∷ CCZ124 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ X4 ∷ CCZ123 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ124 ∷ Toff314 ∷ CS03 ∷ CCZ124 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b13 = at 5 5 (CCZ123 ∷ []) (lw4 c4 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ024 ∷ CZ02 ∷ []) (pw3 c4 (CZ02 ∷ CCZ024 ∷ []) (CCZ024 ∷ CZ02 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ024 ∷ X4 ∷ CZ02 ∷ []) (pw3 c4 (X4 ∷ CCZ024 ∷ []) (CCZ024 ∷ X4 ∷ CZ02 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (X4 ∷ []) (lw3 c4 (X4 ∷ CZ02 ∷ CZ02 ∷ []) (X4 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff013 ∷ CCZ123 ∷ []) (lw4 c4 (CCZ123 ∷ Toff013 ∷ []) (Toff013 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • Toff • Swap ↑ ↑) (X))) ▸
       at 0 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 3 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸ done

  b14 : Chain (Bx0-2431 ∷ X4 ∷ CCZ123 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ124 ∷ Toff314 ∷ CS03 ∷ CCZ124 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ X4 ∷ CCZ024 ∷ Toff213 ∷ CZ13 ∷ CCZ123 ∷ CCZ024 ∷ Toff213 ∷ CCZ124 ∷ Toff314 ∷ CS03 ∷ CCZ124 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b14 = at 2 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (lw4 c4 (CCZ123 ∷ []) (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ024 ∷ CS12 ∷ []) (pw3 c4 (CS12 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸
       at 4 2 (CCZ024 ∷ CS23⁻ ∷ []) (pw1 c4 (CS23⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ CS23⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸
       at 2 2 (CCZ024 ∷ CS23 ∷ []) (pw1 c4 (CS23 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 3 5 (CCZ123 ∷ []) (lw4 c4 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff213 ∷ CZ13 ∷ CCZ123 ∷ []) (lw4 c4 (CCZ123 ∷ Toff213 ∷ []) (Toff213 ∷ CZ13 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸ done

  b15 : Chain (Bx0-2431 ∷ X4 ∷ CCZ024 ∷ Toff213 ∷ CZ13 ∷ CCZ123 ∷ CCZ024 ∷ Toff213 ∷ CCZ124 ∷ Toff314 ∷ CS03 ∷ CCZ124 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ X4 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ CZ13 ∷ CCZ123 ∷ Toff213 ∷ CCZ124 ∷ Toff314 ∷ CS03 ∷ CCZ124 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b15 = at 5 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (lw4 c4 (CCZ123 ∷ []) (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ024 ∷ CS12 ∷ []) (pw3 c4 (CS12 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸
       at 7 2 (CCZ024 ∷ CS23⁻ ∷ []) (pw1 c4 (CS23⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ CS23⁻ ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 c4) ▸
       at 5 2 (CCZ024 ∷ CS23 ∷ []) (pw1 c4 (CS23 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 6 5 (CCZ123 ∷ []) (lw4 c4 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ024 ∷ CZ13 ∷ []) (lem-comm-CZ13-CCZ024 c4) ▸ done

  b16 : Chain (Bx0-2431 ∷ X4 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ CZ13 ∷ CCZ123 ∷ Toff213 ∷ CCZ124 ∷ Toff314 ∷ CS03 ∷ CCZ124 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ X4 ∷ Bx2-0413 ∷ CCZ124 ∷ Toff314 ∷ CS03 ∷ CCZ124 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ123 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b16 = at 5 3 (Toff213 ∷ CCZ123 ∷ []) (lw4 c4 (CZ13 ∷ CCZ123 ∷ Toff213 ∷ []) (Toff213 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 3 3 (CCZ124 ∷ Toff314 ∷ CCZ123 ∷ CCZ124 ∷ []) (lw0 c4 (CCZ123 ∷ CCZ124 ∷ Toff314 ∷ []) (CCZ124 ∷ Toff314 ∷ CCZ123 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CS03 ∷ CCZ124 ∷ []) (lem-comm-CCZ124-CS03 c4) ▸
       at 5 2 (CS03 ∷ CCZ123 ∷ []) (lw4 c4 (CCZ123 ∷ CS03 ∷ []) (CS03 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 6 4 (CCZ124 ∷ Toff314 ∷ CCZ123 ∷ []) (lw0 c4 (CCZ123 ∷ CCZ124 ∷ CCZ124 ∷ Toff314 ∷ []) (CCZ124 ∷ Toff314 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CS03⁻ ∷ CCZ123 ∷ []) (lw4 c4 (CCZ123 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (X4 ∷ CCZ123 ∷ []) (lw0 c4 (CCZ123 ∷ X4 ∷ []) (X4 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸ done

  b17 : Chain (Bx0-2431 ∷ X4 ∷ Bx2-0413 ∷ CCZ124 ∷ Toff314 ∷ CS03 ∷ CCZ124 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ123 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ X4 ∷ Sb2-0-41-3 ∷ CX31 ∷ Toff134 ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b17 = at 10 2 [] (lw4 c4 (CCZ123 ∷ CCZ123 ∷ []) [] tt tt Eq.refl) ▸
       at 3 2 (Toff314 ∷ CCZ124 ∷ []) (lw0 c4 (CCZ124 ∷ Toff314 ∷ []) (Toff314 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CS03 ∷ CCZ124 ∷ []) (lem-comm-CCZ124-CS03 c4) ▸
       at 5 2 [] (lw0 c4 (CCZ124 ∷ CCZ124 ∷ []) [] tt tt Eq.refl) ▸
       at 4 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 6 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 2 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 3 2 (CX31 ∷ Toff134 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff134 ∷ []) (CX31 ∷ Toff134 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b18 : Chain (Bx0-2431 ∷ X4 ∷ Sb2-0-41-3 ∷ CX31 ∷ Toff134 ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ X4 ∷ CCZ024 ∷ Toff213 ∷ CX31 ∷ CCZ024 ∷ CX32 ∷ Toff134 ∷ Toff234 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b18 = at 2 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 4 1 (CS03 ∷ []) (refl) ▸
       at 6 1 (CS03⁻ ∷ []) (refl) ▸
       at 3 6 (CX31 ∷ Toff134 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (pw2 c4 (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CX31 ∷ Toff134 ∷ []) (CX31 ∷ Toff134 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 5 2 (CX31 ∷ CX32 ∷ Toff213 ∷ []) (lw4 c4 (Toff213 ∷ CX31 ∷ []) (CX31 ∷ CX32 ∷ Toff213 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff134 ∷ Toff234 ∷ Toff213 ∷ []) (lw0 c4 (Toff213 ∷ Toff134 ∷ []) (Toff134 ∷ Toff234 ∷ Toff213 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CX31 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX31 c4) ▸ done

  b19 : Chain (Bx0-2431 ∷ X4 ∷ CCZ024 ∷ Toff213 ∷ CX31 ∷ CCZ024 ∷ CX32 ∷ Toff134 ∷ Toff234 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ X4 ∷ CCZ024 ∷ Toff213 ∷ CX31 ∷ CX32 ∷ CCZ034 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ CCZ024 ∷ K1⁻ ∷ Toff234 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b19 = at 5 2 (CX32 ∷ CCZ034 ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ CX32 ∷ []) (CX32 ∷ CCZ034 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 8 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (lw0 c4 (Toff134 ∷ []) (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) tt tt Eq.refl) ▸
       at 7 2 (K1 ∷ CCZ024 ∷ []) (pw3 c4 (CCZ024 ∷ K1 ∷ []) (K1 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CS34 ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ CS34 ∷ []) (CS34 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 c4) ▸
       at 10 2 (CS34⁻ ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 c4) ▸
       at 12 2 (CS14 ∷ CCZ024 ∷ []) (pw3 c4 (CCZ024 ∷ CS14 ∷ []) (CS14 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸ done

  b20 : Chain (Bx0-2431 ∷ X4 ∷ CCZ024 ∷ Toff213 ∷ CX31 ∷ CX32 ∷ CCZ034 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ CCZ024 ∷ K1⁻ ∷ Toff234 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ X4 ∷ CCZ024 ∷ CX31 ∷ CX32 ∷ CX32 ∷ CS34 ∷ CX04 ∷ Toff213 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ Toff134 ∷ Toff234 ∷ CCZ034 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b20 = at 13 2 (K1⁻ ∷ CCZ024 ∷ []) (pw3 c4 (CCZ024 ∷ K1⁻ ∷ []) (K1⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 7 7 (Toff134 ∷ []) (lw0 c4 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (Toff134 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (Toff234 ∷ CCZ034 ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ Toff234 ∷ []) (Toff234 ∷ CCZ034 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CX31 ∷ CX32 ∷ Toff213 ∷ []) (lw4 c4 (Toff213 ∷ CX31 ∷ []) (CX31 ∷ CX32 ∷ Toff213 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CX32 ∷ Toff213 ∷ []) (lw4 c4 (Toff213 ∷ CX32 ∷ []) (CX32 ∷ Toff213 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ []) (pw1 c4 (CCZ034 ∷ []) (CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CS34 ∷ Toff213 ∷ []) (lw0 c4 (Toff213 ∷ CS34 ∷ []) (CS34 ∷ Toff213 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CX04 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX04 c4) ▸ done

  b21 : Chain (Bx0-2431 ∷ X4 ∷ CCZ024 ∷ CX31 ∷ CX32 ∷ CX32 ∷ CS34 ∷ CX04 ∷ Toff213 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ Toff134 ∷ Toff234 ∷ CCZ034 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ X4 ∷ CCZ024 ∷ CX31 ∷ CX32 ∷ CX32 ∷ CCZ034 ∷ Toff134 ∷ Toff234 ∷ Toff234 ∷ CS34 ∷ Toff213 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b21 = at 8 2 (CS34⁻ ∷ Toff213 ∷ []) (lw0 c4 (Toff213 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Toff213 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CX04 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX04 c4) ▸
       at 10 2 (CS03 ∷ Toff213 ∷ []) (lw4 c4 (Toff213 ∷ CS03 ∷ []) (CS03 ∷ Toff213 ∷ []) tt tt Eq.refl) ▸
       at 6 5 (CCZ034 ∷ []) (pw1 c4 (CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff134 ∷ Toff234 ∷ Toff213 ∷ []) (lw0 c4 (Toff213 ∷ Toff134 ∷ []) (Toff134 ∷ Toff234 ∷ Toff213 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (Toff234 ∷ Toff213 ∷ []) (lw0 c4 (Toff213 ∷ Toff234 ∷ []) (Toff234 ∷ Toff213 ∷ []) tt tt Eq.refl) ▸
       at 11 1 (CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ []) (pw1 c4 (CCZ034 ∷ []) (CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (CS34 ∷ Toff213 ∷ []) (lw0 c4 (Toff213 ∷ CS34 ∷ []) (CS34 ∷ Toff213 ∷ []) tt tt Eq.refl) ▸ done

  b22 : Chain (Bx0-2431 ∷ X4 ∷ CCZ024 ∷ CX31 ∷ CX32 ∷ CX32 ∷ CCZ034 ∷ Toff134 ∷ Toff234 ∷ Toff234 ∷ CS34 ∷ Toff213 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ X4 ∷ CCZ024 ∷ CX31 ∷ Toff134 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b22 = at 11 2 (CX04 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX04 c4) ▸
       at 12 2 (CS34⁻ ∷ Toff213 ∷ []) (lw0 c4 (Toff213 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Toff213 ∷ []) tt tt Eq.refl) ▸
       at 13 2 (CX04 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX04 c4) ▸
       at 14 2 (CS03 ∷ Toff213 ∷ []) (lw4 c4 (Toff213 ∷ CS03 ∷ []) (CS03 ∷ Toff213 ∷ []) tt tt Eq.refl) ▸
       at 10 5 (CCZ034 ∷ []) (pw1 c4 (CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CX31 ∷ []) (lw4 c4 (CX31 ∷ CX32 ∷ CX32 ∷ []) (CX31 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (Toff134 ∷ []) (lw0 c4 (Toff134 ∷ Toff234 ∷ Toff234 ∷ []) (Toff134 ∷ []) tt tt Eq.refl) ▸
       at 3 4 (CX31 ∷ Toff134 ∷ []) (pw2 c4 (CX31 ∷ CCZ034 ∷ Toff134 ∷ CCZ034 ∷ []) (CX31 ∷ Toff134 ∷ []) tt tt Eq.refl) ▸ done

  b23 : Chain (Bx0-2431 ∷ X4 ∷ CCZ024 ∷ CX31 ∷ Toff134 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ X4 ∷ CX31 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ CCZ024 ∷ K1⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b23 = at 2 2 (CX31 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX31 c4) ▸
       at 4 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (lw0 c4 (Toff134 ∷ []) (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 2 (K1 ∷ CCZ024 ∷ []) (pw3 c4 (CCZ024 ∷ K1 ∷ []) (K1 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CS34 ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ CS34 ∷ []) (CS34 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 c4) ▸
       at 6 2 (CS34⁻ ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 c4) ▸
       at 8 2 (CS14 ∷ CCZ024 ∷ []) (pw3 c4 (CCZ024 ∷ CS14 ∷ []) (CS14 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸ done

  b24 : Chain (Bx0-2431 ∷ X4 ∷ CX31 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ CCZ024 ∷ K1⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ Toff134 ∷ X4 ∷ Sb2-0-41-3 ∷ CS12 ∷ X4 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b24 = at 9 2 (K1⁻ ∷ CCZ024 ∷ []) (pw3 c4 (CCZ024 ∷ K1⁻ ∷ []) (K1⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 3 7 (Toff134 ∷ []) (lw0 c4 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (Toff134 ∷ []) tt tt Eq.refl) ▸
       at 4 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 6 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 8 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 4 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 1 3 (Toff134 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX31 ∷ Toff134 ∷ []) (Toff134 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CS12 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS12 ∷ []) (CS12 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b25 : Chain (Bx0-2431 ∷ Toff134 ∷ X4 ∷ Sb2-0-41-3 ∷ CS12 ∷ X4 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ Toff134 ∷ X4 ∷ CS12 ∷ Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b25 = at 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 5 1 (CS03 ∷ []) (refl) ▸
       at 7 1 (CS03⁻ ∷ []) (refl) ▸
       at 7 2 (CS12 ∷ CS03⁻ ∷ []) (lw4 c4 (CS03⁻ ∷ CS12 ∷ []) (CS12 ∷ CS03⁻ ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CS12 ∷ Toff314 ∷ []) (lw0 c4 (Toff314 ∷ CS12 ∷ []) (CS12 ∷ Toff314 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CS12 ∷ CS03 ∷ []) (lw4 c4 (CS03 ∷ CS12 ∷ []) (CS12 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CS12 ∷ Toff314 ∷ []) (lw0 c4 (Toff314 ∷ CS12 ∷ []) (CS12 ∷ Toff314 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CS12 ∷ Bx2-0413 ∷ []) (sym (lem-CSu-box-3-at0210243143 c4)) ▸ done

  b26 : Chain (Bx0-2431 ∷ Toff134 ∷ X4 ∷ CS12 ∷ Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ X4 ∷ Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CX31 ∷ Toff134 ∷ X4 ∷ CS12⁻ ∷ [])
  b26 = at 6 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 8 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 4 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 2 2 (CS12 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS12 ∷ []) (CS12 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CX31 ∷ Toff134 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ Toff134 ∷ []) (CX31 ∷ Toff134 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 6 1 (CS03 ∷ []) (refl) ▸
       at 8 1 (CS03⁻ ∷ []) (refl) ▸ done

  b27 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ X4 ∷ Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CX31 ∷ Toff134 ∷ X4 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ X4 ∷ CCZ024 ∷ Toff213 ∷ CX31 ∷ CX32 ∷ CCZ034 ∷ K1 ∷ CCZ024 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff234 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS12⁻ ∷ [])
  b27 = at 5 6 (CX31 ∷ Toff134 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (pw2 c4 (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CX31 ∷ Toff134 ∷ []) (CX31 ∷ Toff134 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 7 2 (CX31 ∷ CX32 ∷ Toff213 ∷ []) (lw4 c4 (Toff213 ∷ CX31 ∷ []) (CX31 ∷ CX32 ∷ Toff213 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (Toff134 ∷ Toff234 ∷ Toff213 ∷ []) (lw0 c4 (Toff213 ∷ Toff134 ∷ []) (Toff134 ∷ Toff234 ∷ Toff213 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CX31 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX31 c4) ▸
       at 7 2 (CX32 ∷ CCZ034 ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ CX32 ∷ []) (CX32 ∷ CCZ034 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 10 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (lw0 c4 (Toff134 ∷ []) (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) tt tt Eq.refl) ▸
       at 9 2 (K1 ∷ CCZ024 ∷ []) (pw3 c4 (CCZ024 ∷ K1 ∷ []) (K1 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸ done

  b28 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ X4 ∷ CCZ024 ∷ Toff213 ∷ CX31 ∷ CX32 ∷ CCZ034 ∷ K1 ∷ CCZ024 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff234 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ X4 ∷ CCZ024 ∷ Toff213 ∷ CX31 ∷ CX32 ∷ CCZ034 ∷ Toff134 ∷ Toff234 ∷ CCZ034 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS12⁻ ∷ [])
  b28 = at 10 2 (CS34 ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ CS34 ∷ []) (CS34 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 c4) ▸
       at 12 2 (CS34⁻ ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 13 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 c4) ▸
       at 14 2 (CS14 ∷ CCZ024 ∷ []) (pw3 c4 (CCZ024 ∷ CS14 ∷ []) (CS14 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 15 2 (K1⁻ ∷ CCZ024 ∷ []) (pw3 c4 (CCZ024 ∷ K1⁻ ∷ []) (K1⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 9 7 (Toff134 ∷ []) (lw0 c4 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (Toff134 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (Toff234 ∷ CCZ034 ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ Toff234 ∷ []) (Toff234 ∷ CCZ034 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸ done

  b29 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ X4 ∷ CCZ024 ∷ Toff213 ∷ CX31 ∷ CX32 ∷ CCZ034 ∷ Toff134 ∷ Toff234 ∷ CCZ034 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ X4 ∷ CCZ024 ∷ CX31 ∷ CX32 ∷ CX32 ∷ CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ Toff213 ∷ Toff134 ∷ Toff234 ∷ CCZ034 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS12⁻ ∷ [])
  b29 = at 5 2 (CX31 ∷ CX32 ∷ Toff213 ∷ []) (lw4 c4 (Toff213 ∷ CX31 ∷ []) (CX31 ∷ CX32 ∷ Toff213 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CX32 ∷ Toff213 ∷ []) (lw4 c4 (Toff213 ∷ CX32 ∷ []) (CX32 ∷ Toff213 ∷ []) tt tt Eq.refl) ▸
       at 9 1 (CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ []) (pw1 c4 (CCZ034 ∷ []) (CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CS34 ∷ Toff213 ∷ []) (lw0 c4 (Toff213 ∷ CS34 ∷ []) (CS34 ∷ Toff213 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CX04 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX04 c4) ▸
       at 10 2 (CS34⁻ ∷ Toff213 ∷ []) (lw0 c4 (Toff213 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Toff213 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (CX04 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX04 c4) ▸
       at 12 2 (CS03 ∷ Toff213 ∷ []) (lw4 c4 (Toff213 ∷ CS03 ∷ []) (CS03 ∷ Toff213 ∷ []) tt tt Eq.refl) ▸ done

  b30 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ X4 ∷ CCZ024 ∷ CX31 ∷ CX32 ∷ CX32 ∷ CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ Toff213 ∷ Toff134 ∷ Toff234 ∷ CCZ034 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ X4 ∷ CCZ024 ∷ CX31 ∷ CX32 ∷ CX32 ∷ CCZ034 ∷ Toff134 ∷ Toff234 ∷ Toff234 ∷ CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ Toff213 ∷ CS03 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS12⁻ ∷ [])
  b30 = at 8 5 (CCZ034 ∷ []) (pw1 c4 (CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (Toff134 ∷ Toff234 ∷ Toff213 ∷ []) (lw0 c4 (Toff213 ∷ Toff134 ∷ []) (Toff134 ∷ Toff234 ∷ Toff213 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (Toff234 ∷ Toff213 ∷ []) (lw0 c4 (Toff213 ∷ Toff234 ∷ []) (Toff234 ∷ Toff213 ∷ []) tt tt Eq.refl) ▸
       at 13 1 (CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ []) (pw1 c4 (CCZ034 ∷ []) (CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (CS34 ∷ Toff213 ∷ []) (lw0 c4 (Toff213 ∷ CS34 ∷ []) (CS34 ∷ Toff213 ∷ []) tt tt Eq.refl) ▸
       at 13 2 (CX04 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX04 c4) ▸
       at 14 2 (CS34⁻ ∷ Toff213 ∷ []) (lw0 c4 (Toff213 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Toff213 ∷ []) tt tt Eq.refl) ▸
       at 15 2 (CX04 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX04 c4) ▸ done

  b31 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ X4 ∷ CCZ024 ∷ CX31 ∷ CX32 ∷ CX32 ∷ CCZ034 ∷ Toff134 ∷ Toff234 ∷ Toff234 ∷ CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ Toff213 ∷ CS03 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ X4 ∷ CX31 ∷ K1 ∷ CCZ024 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS12⁻ ∷ [])
  b31 = at 16 2 (CS03 ∷ Toff213 ∷ []) (lw4 c4 (Toff213 ∷ CS03 ∷ []) (CS03 ∷ Toff213 ∷ []) tt tt Eq.refl) ▸
       at 12 5 (CCZ034 ∷ []) (pw1 c4 (CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (CX31 ∷ []) (lw4 c4 (CX31 ∷ CX32 ∷ CX32 ∷ []) (CX31 ∷ []) tt tt Eq.refl) ▸
       at 7 3 (Toff134 ∷ []) (lw0 c4 (Toff134 ∷ Toff234 ∷ Toff234 ∷ []) (Toff134 ∷ []) tt tt Eq.refl) ▸
       at 5 4 (CX31 ∷ Toff134 ∷ []) (pw2 c4 (CX31 ∷ CCZ034 ∷ Toff134 ∷ CCZ034 ∷ []) (CX31 ∷ Toff134 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CX31 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX31 c4) ▸
       at 6 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (lw0 c4 (Toff134 ∷ []) (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 2 (K1 ∷ CCZ024 ∷ []) (pw3 c4 (CCZ024 ∷ K1 ∷ []) (K1 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸ done

  b32 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ X4 ∷ CX31 ∷ K1 ∷ CCZ024 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ X4 ∷ CX31 ∷ Toff134 ∷ Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS12⁻ ∷ [])
  b32 = at 6 2 (CS34 ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ CS34 ∷ []) (CS34 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 c4) ▸
       at 8 2 (CS34⁻ ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 c4) ▸
       at 10 2 (CS14 ∷ CCZ024 ∷ []) (pw3 c4 (CCZ024 ∷ CS14 ∷ []) (CS14 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (K1⁻ ∷ CCZ024 ∷ []) (pw3 c4 (CCZ024 ∷ K1⁻ ∷ []) (K1⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 5 7 (Toff134 ∷ []) (lw0 c4 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (Toff134 ∷ []) tt tt Eq.refl) ▸
       at 6 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸ done

  b33 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ X4 ∷ CX31 ∷ Toff134 ∷ Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ X4 ∷ Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CS12⁻ ∷ X4 ∷ [])
  b33 = at 8 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 10 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 6 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 3 3 (Toff134 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CX31 ∷ Toff134 ∷ []) (Toff134 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CS12⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 7 1 (CS03 ∷ []) (refl) ▸
       at 9 1 (CS03⁻ ∷ []) (refl) ▸ done

  b34 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ X4 ∷ Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CS12⁻ ∷ X4 ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ X4 ∷ CS12⁻ ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  b34 = at 9 2 (CS12⁻ ∷ CS03⁻ ∷ []) (lw4 c4 (CS03⁻ ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CS03⁻ ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CS12⁻ ∷ Toff314 ∷ []) (lw0 c4 (Toff314 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ Toff314 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CS12⁻ ∷ CS03 ∷ []) (lw4 c4 (CS03 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CS12⁻ ∷ Toff314 ∷ []) (lw0 c4 (Toff314 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ Toff314 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CS12⁻ ∷ Bx2-0413 ∷ []) (sym (lem-CSdu-box-3-at0210243143 c4)) ▸
       at 8 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 10 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 6 5 (Sb2-0-41-3 ∷ []) (refl) ▸ done

  b35 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ X4 ∷ CS12⁻ ∷ Sb2-0-41-3 ∷ X4 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  b35 = at 4 2 (CS12⁻ ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 0 5 (Sb0-2-43-1 ∷ []) (refl) ▸ done


-- CXbc-box @122331: 17 steps
lem-CXbc-box-at122331 : Complete 4 → ⟪ (CX31 ∷ Bx0-2314 ∷ CX31 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2314 ∷ CCZ234 ∷ []) ⟫ʷ
lem-CXbc-box-at122331 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX31 ∷ Bx0-2314 ∷ CX31 ∷ []) (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CX31 ∷ CCZ034 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CCZ014 ∷ CX23 ∷ CS24 ∷ CX31 ∷ [])
  b0 = at 1 1 (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ []) (lem-box-tQ-at122331 c4) ▸
       at 0 2 (Toff023 ∷ CX31 ∷ []) (lw4 c4 (CX31 ∷ Toff023 ∷ []) (Toff023 ∷ CX31 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ014 ∷ CX31 ∷ CCZ034 ∷ []) (pw2 c4 (CX31 ∷ CCZ014 ∷ []) (CCZ014 ∷ CX31 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff023 ∷ CCZ034 ∷ CCZ234 ∷ []) (pw1 c4 (CCZ034 ∷ Toff023 ∷ []) (Toff023 ∷ CCZ034 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff023 ∷ CX31 ∷ []) (lw4 c4 (CX31 ∷ Toff023 ∷ []) (Toff023 ∷ CX31 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ []) (lw0 c4 (CCZ234 ∷ []) (CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ014 ∷ CS24 ∷ []) (pw3 c4 (CS24 ∷ CCZ014 ∷ []) (CCZ014 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 c4) ▸ done

  b1 : Chain (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CX31 ∷ CCZ034 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CCZ014 ∷ CX23 ∷ CS24 ∷ CX31 ∷ []) (Bx0-2314 ∷ CX31 ∷ CCZ234 ∷ CX31 ∷ [])
  b1 = at 7 2 (CCZ014 ∷ CS34⁻ ∷ []) (pw2 c4 (CS34⁻ ∷ CCZ014 ∷ []) (CCZ014 ∷ CS34⁻ ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 c4) ▸
       at 5 2 (CCZ014 ∷ CS34 ∷ []) (pw2 c4 (CS34 ∷ CCZ014 ∷ []) (CCZ014 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 6 5 (CCZ234 ∷ []) (lw0 c4 (CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ014 ∷ CCZ034 ∷ []) (pw2 c4 (CCZ034 ∷ CCZ014 ∷ []) (CCZ014 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ014 ∷ CX31 ∷ CCZ034 ∷ []) (pw2 c4 (CX31 ∷ CCZ014 ∷ []) (CCZ014 ∷ CX31 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CX31 ∷ []) (pw2 c4 (CX31 ∷ CCZ034 ∷ CCZ034 ∷ []) (CX31 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx0-2314 ∷ []) (sym (lem-box-tQ-at122331 c4)) ▸ done

  b2 : Chain (Bx0-2314 ∷ CX31 ∷ CCZ234 ∷ CX31 ∷ []) (Bx0-2314 ∷ CCZ234 ∷ [])
  b2 = at 1 3 (CCZ234 ∷ []) (lw0 c4 (CX31 ∷ CCZ234 ∷ CX31 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸ done


-- CXcb-box @122331: 18 steps
lem-CXcb-box-at122331 : Complete 4 → ⟪ (CX13 ∷ Bx0-2314 ∷ CX13 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2314 ∷ CCZ124 ∷ []) ⟫ʷ
lem-CXcb-box-at122331 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX13 ∷ Bx0-2314 ∷ CX13 ∷ []) (Toff023 ∷ CCZ014 ∷ CX13 ∷ Toff012 ∷ CS14 ∷ CX21 ∷ Toff023 ∷ CS14⁻ ∷ CX21 ∷ CS24 ∷ CCZ014 ∷ CX13 ∷ [])
  b0 = at 1 1 (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ []) (lem-box-tQ-at122331 c4) ▸
       at 0 2 (Toff023 ∷ CX13 ∷ Toff012 ∷ []) (lw4 c4 (CX13 ∷ Toff023 ∷ []) (Toff023 ∷ CX13 ∷ Toff012 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ014 ∷ Toff012 ∷ CCZ124 ∷ []) (pw3 c4 (Toff012 ∷ CCZ014 ∷ []) (CCZ014 ∷ Toff012 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ014 ∷ CX13 ∷ []) (pw2 c4 (CX13 ∷ CCZ014 ∷ []) (CCZ014 ∷ CX13 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CS14 ∷ CX21 ∷ CS14⁻ ∷ CX21 ∷ CS24 ∷ []) (lw0 c4 (CCZ124 ∷ []) (CS14 ∷ CX21 ∷ CS14⁻ ∷ CX21 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (Toff023 ∷ CS24 ∷ []) (pw1 c4 (CS24 ∷ Toff023 ∷ []) (Toff023 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff023 ∷ CX21 ∷ []) (lw4 c4 (CX21 ∷ Toff023 ∷ []) (Toff023 ∷ CX21 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Toff023 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-TOFF023 c4) ▸ done

  b1 : Chain (Toff023 ∷ CCZ014 ∷ CX13 ∷ Toff012 ∷ CS14 ∷ CX21 ∷ Toff023 ∷ CS14⁻ ∷ CX21 ∷ CS24 ∷ CCZ014 ∷ CX13 ∷ []) (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ CX13 ∷ CCZ124 ∷ CX13 ∷ [])
  b1 = at 5 2 (Toff023 ∷ CX21 ∷ []) (lw4 c4 (CX21 ∷ Toff023 ∷ []) (Toff023 ∷ CX21 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff023 ∷ CS14 ∷ []) (lem-comm-CS14-TOFF023 c4) ▸
       at 5 5 (CCZ124 ∷ []) (lw0 c4 (CS14 ∷ CX21 ∷ CS14⁻ ∷ CX21 ∷ CS24 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff023 ∷ Toff012 ∷ []) (lw4 c4 (Toff012 ∷ Toff023 ∷ []) (Toff023 ∷ Toff012 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff023 ∷ CX13 ∷ Toff012 ∷ []) (lw4 c4 (CX13 ∷ Toff023 ∷ []) (Toff023 ∷ CX13 ∷ Toff012 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CX13 ∷ []) (lw4 c4 (CX13 ∷ Toff012 ∷ Toff012 ∷ []) (CX13 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ014 ∷ CCZ124 ∷ []) (pw3 c4 (CCZ124 ∷ CCZ014 ∷ []) (CCZ014 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ014 ∷ CX13 ∷ []) (pw2 c4 (CX13 ∷ CCZ014 ∷ []) (CCZ014 ∷ CX13 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ CX13 ∷ CCZ124 ∷ CX13 ∷ []) (Bx0-2314 ∷ CCZ124 ∷ [])
  b2 = at 0 4 (Bx0-2314 ∷ []) (sym (lem-box-tQ-at122331 c4)) ▸
       at 1 3 (CCZ124 ∷ []) (lw0 c4 (CX13 ∷ CCZ124 ∷ CX13 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl) ▸ done


-- SWbc-box @122331: 11 steps
lem-SWbc-box-at122331 : Complete 4 → ⟪ (Sw13 ∷ Bx0-2314 ∷ Sw13 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2314 ∷ []) ⟫ʷ
lem-SWbc-box-at122331 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw13 ∷ Bx0-2314 ∷ Sw13 ∷ []) (CX31 ∷ Bx0-2314 ∷ CX31 ∷ CCZ234 ∷ CCZ124 ∷ CCZ234 ∷ CCZ124 ∷ CCZ234 ∷ [])
  b0 = at 0 1 (CX31 ∷ CX13 ∷ CX31 ∷ []) (lw4 c4 (Sw13 ∷ []) (CX31 ∷ CX13 ∷ CX31 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CX31 ∷ CX13 ∷ CX31 ∷ []) (lw4 c4 (Sw13 ∷ []) (CX31 ∷ CX13 ∷ CX31 ∷ []) tt tt Eq.refl) ▸
       at 2 3 (Bx0-2314 ∷ CCZ234 ∷ []) (lem-CXbc-box-at122331 c4) ▸
       at 3 2 (CX13 ∷ CCZ124 ∷ CCZ234 ∷ []) (lw0 c4 (CCZ234 ∷ CX13 ∷ []) (CX13 ∷ CCZ124 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Bx0-2314 ∷ CCZ124 ∷ []) (lem-CXcb-box-at122331 c4) ▸
       at 4 2 (CX31 ∷ CCZ234 ∷ []) (lw0 c4 (CCZ234 ∷ CX31 ∷ []) (CX31 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CX31 ∷ CCZ234 ∷ CCZ124 ∷ []) (lw0 c4 (CCZ124 ∷ CX31 ∷ []) (CX31 ∷ CCZ234 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CX31 ∷ CCZ234 ∷ CCZ124 ∷ []) (lw0 c4 (CCZ124 ∷ CX31 ∷ []) (CX31 ∷ CCZ234 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CX31 ∷ Bx0-2314 ∷ CX31 ∷ CCZ234 ∷ CCZ124 ∷ CCZ234 ∷ CCZ124 ∷ CCZ234 ∷ []) (Bx0-2314 ∷ [])
  b1 = at 3 5 (CCZ234 ∷ []) (lw0 c4 (CCZ234 ∷ CCZ124 ∷ CCZ234 ∷ CCZ124 ∷ CCZ234 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Bx0-2314 ∷ CCZ234 ∷ []) (lem-CXbc-box-at122331 c4) ▸
       at 1 2 [] (lw0 c4 (CCZ234 ∷ CCZ234 ∷ []) [] tt tt Eq.refl) ▸ done


-- nat-SWbc @122331: 23 steps
lem-nat-SWbc-at122331 : Complete 4 → ⟪ (Sw13 ∷ Bx0-2314 ∷ Sw13 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ []) ⟫ʷ
lem-nat-SWbc-at122331 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw13 ∷ Bx0-2314 ∷ Sw13 ∷ []) (CCZ012 ∷ Toff012 ∷ CCZ023 ∷ Toff203 ∷ Bx0-24 ∷ Toff203 ∷ Sw13 ∷ CCZ012 ∷ Bx0-24 ∷ Toff023 ∷ CCZ023 ∷ Bx2-014 ∷ Sw13 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff023 ∷ Bx2-014 ∷ Toff023 ∷ CCZ023 ∷ Bx2-014 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw13 ∷ []) (lw4 c4 (Sw13 ∷ CCZ023 ∷ []) (CCZ012 ∷ Sw13 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff012 ∷ Sw13 ∷ []) (lw4 c4 (Sw13 ∷ Toff023 ∷ []) (Toff012 ∷ Sw13 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (CCZ012 ∷ Toff201 ∷ Bx0-24 ∷ Toff201 ∷ CCZ012 ∷ Bx0-24 ∷ []) (refl) ▸
       at 2 2 (CCZ023 ∷ Sw13 ∷ []) (lw4 c4 (Sw13 ∷ CCZ012 ∷ []) (CCZ023 ∷ Sw13 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff203 ∷ Sw13 ∷ []) (lw4 c4 (Sw13 ∷ Toff201 ∷ []) (Toff203 ∷ Sw13 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Bx0-24 ∷ Sw13 ∷ []) (lem-comm-SWAP13-BOX⟨0·24⟩ c4) ▸
       at 5 2 (Toff203 ∷ Sw13 ∷ []) (lw4 c4 (Sw13 ∷ Toff201 ∷ []) (Toff203 ∷ Sw13 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CCZ012 ∷ Toff012 ∷ CCZ023 ∷ Toff203 ∷ Bx0-24 ∷ Toff203 ∷ Sw13 ∷ CCZ012 ∷ Bx0-24 ∷ Toff023 ∷ CCZ023 ∷ Bx2-014 ∷ Sw13 ∷ []) (CCZ012 ∷ Toff012 ∷ CCZ023 ∷ Toff203 ∷ Bx0-24 ∷ Toff203 ∷ CCZ023 ∷ Bx0-24 ∷ Toff012 ∷ CCZ012 ∷ CCZ023 ∷ Toff203 ∷ Bx0-24 ∷ Sw13 ∷ Toff201 ∷ CCZ012 ∷ Bx0-24 ∷ Sw13 ∷ [])
  b1 = at 6 2 (CCZ023 ∷ Sw13 ∷ []) (lw4 c4 (Sw13 ∷ CCZ012 ∷ []) (CCZ023 ∷ Sw13 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Bx0-24 ∷ Sw13 ∷ []) (lem-comm-SWAP13-BOX⟨0·24⟩ c4) ▸
       at 8 2 (Toff012 ∷ Sw13 ∷ []) (lw4 c4 (Sw13 ∷ Toff023 ∷ []) (Toff012 ∷ Sw13 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ012 ∷ Sw13 ∷ []) (lw4 c4 (Sw13 ∷ CCZ023 ∷ []) (CCZ012 ∷ Sw13 ∷ []) tt tt Eq.refl) ▸
       at 11 1 (CCZ012 ∷ Toff201 ∷ Bx0-24 ∷ Toff201 ∷ CCZ012 ∷ Bx0-24 ∷ []) (refl) ▸
       at 10 2 (CCZ023 ∷ Sw13 ∷ []) (lw4 c4 (Sw13 ∷ CCZ012 ∷ []) (CCZ023 ∷ Sw13 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (Toff203 ∷ Sw13 ∷ []) (lw4 c4 (Sw13 ∷ Toff201 ∷ []) (Toff203 ∷ Sw13 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (Bx0-24 ∷ Sw13 ∷ []) (lem-comm-SWAP13-BOX⟨0·24⟩ c4) ▸ done

  b2 : Chain (CCZ012 ∷ Toff012 ∷ CCZ023 ∷ Toff203 ∷ Bx0-24 ∷ Toff203 ∷ CCZ023 ∷ Bx0-24 ∷ Toff012 ∷ CCZ012 ∷ CCZ023 ∷ Toff203 ∷ Bx0-24 ∷ Sw13 ∷ Toff201 ∷ CCZ012 ∷ Bx0-24 ∷ Sw13 ∷ []) (Bx0-2134 ∷ [])
  b2 = at 13 2 (Toff203 ∷ Sw13 ∷ []) (lw4 c4 (Sw13 ∷ Toff201 ∷ []) (Toff203 ∷ Sw13 ∷ []) tt tt Eq.refl) ▸
       at 14 2 (CCZ023 ∷ Sw13 ∷ []) (lw4 c4 (Sw13 ∷ CCZ012 ∷ []) (CCZ023 ∷ Sw13 ∷ []) tt tt Eq.refl) ▸
       at 15 2 (Bx0-24 ∷ Sw13 ∷ []) (lem-comm-SWAP13-BOX⟨0·24⟩ c4) ▸
       at 16 2 [] (lw4 c4 (Sw13 ∷ Sw13 ∷ []) [] tt tt Eq.refl) ▸
       at 2 6 (Bx2-034 ∷ []) (refl) ▸
       at 5 6 (Bx2-034 ∷ []) (refl) ▸
       at 0 6 (Bx0-2134 ∷ []) (refl) ▸ done


-- sym-bc @122331: 2 steps
lem-sym-bc-at122331 : Complete 4 → ⟪ (Bx0-2314 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ []) ⟫ʷ
lem-sym-bc-at122331 c4 = run b0
  where
  b0 : Chain (Bx0-2314 ∷ []) (Bx0-2134 ∷ [])
  b0 = at 0 1 (Sw13 ∷ Bx0-2314 ∷ Sw13 ∷ []) (sym (lem-SWbc-box-at122331 c4)) ▸
       at 0 3 (Bx0-2134 ∷ []) (lem-nat-SWbc-at122331 c4) ▸ done


-- box-perm-1342 @243243: 3 steps
lem-box-perm-1342-at243243 : Complete 4 → ⟪ (Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-box-perm-1342-at243243 c4 = run b0
  where
  b0 : Chain (Bx0-1423 ∷ []) (Bx0-1234 ∷ [])
  b0 = at 0 1 (Bx0-2314 ∷ []) (lem-pairs-at243243 c4) ▸
       at 0 1 (Bx0-2134 ∷ []) (lem-sym-bc-at122331 c4) ▸
       at 0 1 (Bx0-1234 ∷ []) (lem-sym-ab-at1221 c4) ▸ done

