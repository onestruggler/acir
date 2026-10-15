{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D011 where

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
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-box-cP ; lem-box-tQ)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-sym-ab)
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-sym-bc-at1221)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-pairs-at1221)
open import Examples.Groups.Clifford+CS.Five.D.D006 using (lem-sym-ab-at122331)
open import Examples.Groups.Clifford+CS.Five.D.D007 using (lem-pairs-at122331 ; lem-sym-bc-at13243241)
open import Examples.Groups.Clifford+CS.Five.D.D010 using (lem-P-box-at1331 ; lem-tP-at1331)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-comm-CX14-CCZ023)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-comm-CZ14-CCZ023)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-comm-CSd23-TOFF014 ; lem-comm-TOFF023-CSd14)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-comm-CS12-CCZ034 ; lem-comm-CSd12-CCZ034)
-- VPQ @1331: 14 steps
lem-VPQ-at1331 : Complete 4 → ⟪ (Toff023 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ []) ⟫ʷ
lem-VPQ-at1331 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff023 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ []) (CS14⁻ ∷ CS23⁻ ∷ S0 ∷ Toff014 ∷ Toff023 ∷ S0⁻ ∷ [])
  b0 = at 0 2 (CS23⁻ ∷ S0 ∷ Toff023 ∷ S0⁻ ∷ []) (lw4 c4 (Toff023 ∷ CCZ023 ∷ []) (CS23⁻ ∷ S0 ∷ Toff023 ∷ S0⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CS14⁻ ∷ S0 ∷ Toff014 ∷ S0⁻ ∷ []) (pw2 c4 (Toff014 ∷ CCZ014 ∷ []) (CS14⁻ ∷ S0 ∷ Toff014 ∷ S0⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CS14⁻ ∷ S0⁻ ∷ []) (c₁ (S • S • S) (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑)) ▸
       at 2 2 (CS14⁻ ∷ Toff023 ∷ []) (lem-comm-TOFF023-CSd14 c4) ▸
       at 1 2 (CS14⁻ ∷ S0 ∷ []) (c₁ (S) (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑)) ▸
       at 0 2 (CS14⁻ ∷ CS23⁻ ∷ []) (lw0 c4 (CS23⁻ ∷ CS14⁻ ∷ []) (CS14⁻ ∷ CS23⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw4 c4 (S0⁻ ∷ S0 ∷ []) [] tt tt Eq.refl) ▸
       at 3 2 (Toff014 ∷ Toff023 ∷ []) (lem-tP-at1331 c4) ▸ done

  b1 : Chain (CS14⁻ ∷ CS23⁻ ∷ S0 ∷ Toff014 ∷ Toff023 ∷ S0⁻ ∷ []) (Toff014 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ [])
  b1 = at 4 0 (S0⁻ ∷ S0 ∷ []) (lw4 c4 [] (S0⁻ ∷ S0 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (S0 ∷ CS23⁻ ∷ []) (sym (c₁ (S) ((CS • CS • CS) ↑))) ▸
       at 2 2 (Toff014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-TOFF014 c4) ▸
       at 3 2 (S0⁻ ∷ CS23⁻ ∷ []) (sym (c₁ (S • S • S) ((CS • CS • CS) ↑))) ▸
       at 0 4 (Toff014 ∷ CCZ014 ∷ []) (pw2 c4 (CS14⁻ ∷ S0 ∷ Toff014 ∷ S0⁻ ∷ []) (Toff014 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Toff023 ∷ CCZ023 ∷ []) (lw4 c4 (CS23⁻ ∷ S0 ∷ Toff023 ∷ S0⁻ ∷ []) (Toff023 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸ done


-- QVQ @1331: 3 steps
lem-QVQ-at1331 : Complete 4 → ⟪ (CCZ014 ∷ Toff023 ∷ CCZ023 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ Toff023 ∷ CCZ023 ∷ Toff014 ∷ []) ⟫ʷ
lem-QVQ-at1331 c4 = run b0
  where
  b0 : Chain (CCZ014 ∷ Toff023 ∷ CCZ023 ∷ CCZ014 ∷ []) (Toff014 ∷ Toff023 ∷ CCZ023 ∷ Toff014 ∷ [])
  b0 = at 0 0 (Toff014 ∷ Toff014 ∷ []) (pw2 c4 [] (Toff014 ∷ Toff014 ∷ []) tt tt Eq.refl) ▸
       at 1 4 (Toff023 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ []) (sym (lem-VPQ-at1331 c4)) ▸
       at 4 2 [] (pw2 c4 (CCZ014 ∷ CCZ014 ∷ []) [] tt tt Eq.refl) ▸ done


-- box-cP @1331: 12 steps
lem-box-cP-at1331 : Complete 4 → ⟪ (Bx0-3214 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ []) ⟫ʷ
lem-box-cP-at1331 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-3214 ∷ []) (CCZ023 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ CCZ013 ∷ Toff301 ∷ CZ34 ∷ Toff301 ∷ CCZ013 ∷ CZ34 ∷ [])
  b0 = at 0 1 (CCZ023 ∷ Toff023 ∷ Bx3-014 ∷ Toff023 ∷ CCZ023 ∷ Bx3-014 ∷ []) (refl) ▸
       at 2 1 (CCZ013 ∷ Toff301 ∷ Bx0-34 ∷ Toff301 ∷ CCZ013 ∷ Bx0-34 ∷ []) (refl) ▸
       at 4 1 (CZ34 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 2 6 (CCZ014 ∷ []) (pw2 c4 (CCZ013 ∷ Toff301 ∷ CZ34 ∷ Toff301 ∷ CCZ013 ∷ CZ34 ∷ []) (CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ013 ∷ Toff301 ∷ Bx0-34 ∷ Toff301 ∷ CCZ013 ∷ Bx0-34 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 10 1 (CZ34 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ023 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ CCZ013 ∷ Toff301 ∷ CZ34 ∷ Toff301 ∷ CCZ013 ∷ CZ34 ∷ []) (CCZ023 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ [])
  b1 = at 5 6 (CCZ014 ∷ []) (pw2 c4 (CCZ013 ∷ Toff301 ∷ CZ34 ∷ Toff301 ∷ CCZ013 ∷ CZ34 ∷ []) (CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Toff014 ∷ Toff023 ∷ CCZ023 ∷ Toff014 ∷ []) (lem-QVQ-at1331 c4) ▸
       at 1 2 (Toff014 ∷ Toff023 ∷ []) (lem-tP-at1331 c4) ▸
       at 2 2 [] (lw4 c4 (Toff023 ∷ Toff023 ∷ []) [] tt tt Eq.refl) ▸ done


-- cQ @2442: 7 steps
lem-cQ-at2442 : Complete 4 → ⟪ (CCZ014 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ CCZ014 ∷ []) ⟫ʷ
lem-cQ-at2442 c4 = run b0
  where
  b0 : Chain (CCZ014 ∷ CCZ023 ∷ []) (CCZ023 ∷ CCZ014 ∷ [])
  b0 = at 0 1 (CS04 ∷ CX14 ∷ CS04⁻ ∷ CX14 ∷ CS01 ∷ []) (pw2 c4 (CCZ014 ∷ []) (CS04 ∷ CX14 ∷ CS04⁻ ∷ CX14 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ023 ∷ CS01 ∷ []) (lw4 c4 (CS01 ∷ CCZ023 ∷ []) (CCZ023 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ023 ∷ CX14 ∷ []) (lem-comm-CX14-CCZ023 c4) ▸
       at 2 2 (CCZ023 ∷ CS04⁻ ∷ []) (pw1 c4 (CS04⁻ ∷ CCZ023 ∷ []) (CCZ023 ∷ CS04⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ023 ∷ CX14 ∷ []) (lem-comm-CX14-CCZ023 c4) ▸
       at 0 2 (CCZ023 ∷ CS04 ∷ []) (pw1 c4 (CS04 ∷ CCZ023 ∷ []) (CCZ023 ∷ CS04 ∷ []) tt tt Eq.refl) ▸
       at 1 5 (CCZ014 ∷ []) (pw2 c4 (CS04 ∷ CX14 ∷ CS04⁻ ∷ CX14 ∷ CS01 ∷ []) (CCZ014 ∷ []) tt tt Eq.refl) ▸ done


-- box-tQ @2442: 13 steps
lem-box-tQ-at2442 : Complete 4 → ⟪ (Bx0-1432 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) ⟫ʷ
lem-box-tQ-at2442 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-1432 ∷ []) (CCZ014 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ CCZ013 ∷ Toff103 ∷ CZ12 ∷ Toff103 ∷ CCZ013 ∷ CZ12 ∷ [])
  b0 = at 0 1 (CCZ014 ∷ Toff014 ∷ Bx1-032 ∷ Toff014 ∷ CCZ014 ∷ Bx1-032 ∷ []) (refl) ▸
       at 2 1 (CCZ013 ∷ Toff103 ∷ Bx0-12 ∷ Toff103 ∷ CCZ013 ∷ Bx0-12 ∷ []) (refl) ▸
       at 4 1 (CZ12 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 2 6 (CCZ023 ∷ []) (lw4 c4 (CCZ013 ∷ Toff103 ∷ CZ12 ∷ Toff103 ∷ CCZ013 ∷ CZ12 ∷ []) (CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ013 ∷ Toff103 ∷ Bx0-12 ∷ Toff103 ∷ CCZ013 ∷ Bx0-12 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 10 1 (CZ12 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ014 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ CCZ013 ∷ Toff103 ∷ CZ12 ∷ Toff103 ∷ CCZ013 ∷ CZ12 ∷ []) (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ [])
  b1 = at 5 6 (CCZ023 ∷ []) (lw4 c4 (CCZ013 ∷ Toff103 ∷ CZ12 ∷ Toff103 ∷ CCZ013 ∷ CZ12 ∷ []) (CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Toff014 ∷ CCZ014 ∷ CZ14 ∷ []) (pw2 c4 (CCZ014 ∷ Toff014 ∷ []) (Toff014 ∷ CCZ014 ∷ CZ14 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ023 ∷ CZ14 ∷ []) (lem-comm-CZ14-CCZ023 c4) ▸
       at 1 2 (CCZ023 ∷ CCZ014 ∷ []) (lem-cQ-at2442 c4) ▸
       at 2 4 (Toff014 ∷ []) (pw2 c4 (CCZ014 ∷ CZ14 ∷ Toff014 ∷ CCZ014 ∷ []) (Toff014 ∷ []) tt tt Eq.refl) ▸ done


-- pairs @1331: 4 steps
lem-pairs-at1331 : Complete 4 → ⟪ (Bx0-3214 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1432 ∷ []) ⟫ʷ
lem-pairs-at1331 c4 = run b0
  where
  b0 : Chain (Bx0-3214 ∷ []) (Bx0-1432 ∷ [])
  b0 = at 0 1 (Toff014 ∷ Bx0-3214 ∷ Toff014 ∷ []) (sym (lem-P-box-at1331 c4)) ▸
       at 1 1 (CCZ023 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ []) (lem-box-cP-at1331 c4) ▸
       at 4 2 [] (pw2 c4 (Toff014 ∷ Toff014 ∷ []) [] tt tt Eq.refl) ▸
       at 0 4 (Bx0-1432 ∷ []) (sym (lem-box-tQ-at2442 c4)) ▸ done


-- box-perm-1432: 4 steps
lem-box-perm-1432 : Complete 4 → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1432 ∷ []) ⟫ʷ
lem-box-perm-1432 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ []) (Bx0-1432 ∷ [])
  b0 = at 0 1 (Bx0-2134 ∷ []) (lem-sym-ab c4) ▸
       at 0 1 (Bx0-2314 ∷ []) (lem-sym-bc-at1221 c4) ▸
       at 0 1 (Bx0-3214 ∷ []) (lem-sym-ab-at122331 c4) ▸
       at 0 1 (Bx0-1432 ∷ []) (lem-pairs-at1331 c4) ▸ done


-- sym-ab @243243: 18 steps
lem-sym-ab-at243243 : Complete 4 → ⟪ (Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4123 ∷ []) ⟫ʷ
lem-sym-ab-at243243 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx0-1423 ∷ []) (CCZ014 ∷ Toff014 ∷ CCZ024 ∷ Toff402 ∷ Bx0-43 ∷ Toff402 ∷ CCZ024 ∷ Bx0-43 ∷ Toff014 ∷ CCZ014 ∷ Bx1-023 ∷ [])
  b0 = at 0 1 (CCZ014 ∷ Toff014 ∷ Bx1-023 ∷ Toff014 ∷ CCZ014 ∷ Bx1-023 ∷ []) (refl) ▸
       at 2 1 (CCZ012 ∷ Toff102 ∷ Bx0-13 ∷ Toff102 ∷ CCZ012 ∷ Bx0-13 ∷ []) (refl) ▸
       at 4 1 (CZ13 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 2 6 (CCZ023 ∷ []) (lw4 c4 (CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ []) (CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (CCZ024 ∷ Toff402 ∷ CZ34 ∷ Toff402 ∷ CCZ024 ∷ CZ34 ∷ []) (pw1 c4 (CCZ023 ∷ []) (CCZ024 ∷ Toff402 ∷ CZ34 ∷ Toff402 ∷ CCZ024 ∷ CZ34 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Bx0-43 ∷ []) (refl) ▸
       at 7 1 (Bx0-43 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ014 ∷ Toff014 ∷ CCZ024 ∷ Toff402 ∷ Bx0-43 ∷ Toff402 ∷ CCZ024 ∷ Bx0-43 ∷ Toff014 ∷ CCZ014 ∷ Bx1-023 ∷ []) (CCZ014 ∷ Toff014 ∷ Bx4-023 ∷ Toff014 ∷ CCZ014 ∷ CCZ024 ∷ Toff402 ∷ Bx0-43 ∷ Toff402 ∷ CCZ024 ∷ Bx0-43 ∷ [])
  b1 = at 2 6 (Bx4-023 ∷ []) (refl) ▸
       at 5 1 (CCZ012 ∷ Toff102 ∷ Bx0-13 ∷ Toff102 ∷ CCZ012 ∷ Bx0-13 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 10 1 (CZ13 ∷ []) (refl) ▸
       at 5 6 (CCZ023 ∷ []) (lw4 c4 (CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ []) (CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ024 ∷ Toff402 ∷ CZ34 ∷ Toff402 ∷ CCZ024 ∷ CZ34 ∷ []) (pw1 c4 (CCZ023 ∷ []) (CCZ024 ∷ Toff402 ∷ CZ34 ∷ Toff402 ∷ CCZ024 ∷ CZ34 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (Bx0-43 ∷ []) (refl) ▸
       at 10 1 (Bx0-43 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ014 ∷ Toff014 ∷ Bx4-023 ∷ Toff014 ∷ CCZ014 ∷ CCZ024 ∷ Toff402 ∷ Bx0-43 ∷ Toff402 ∷ CCZ024 ∷ Bx0-43 ∷ []) (Bx0-4123 ∷ [])
  b2 = at 5 6 (Bx4-023 ∷ []) (refl) ▸
       at 0 6 (Bx0-4123 ∷ []) (refl) ▸ done


-- box-perm-4123: 4 steps
lem-box-perm-4123 : Complete 4 → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4123 ∷ []) ⟫ʷ
lem-box-perm-4123 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ []) (Bx0-4123 ∷ [])
  b0 = at 0 1 (Bx0-2134 ∷ []) (lem-sym-ab c4) ▸
       at 0 1 (Bx0-2314 ∷ []) (lem-sym-bc-at1221 c4) ▸
       at 0 1 (Bx0-1423 ∷ []) (lem-pairs-at122331 c4) ▸
       at 0 1 (Bx0-4123 ∷ []) (lem-sym-ab-at243243 c4) ▸ done


-- sym-ab @133441: 18 steps
lem-sym-ab-at133441 : Complete 4 → ⟪ (Bx0-3241 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2341 ∷ []) ⟫ʷ
lem-sym-ab-at133441 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx0-3241 ∷ []) (CCZ023 ∷ Toff023 ∷ CCZ024 ∷ Toff204 ∷ Bx0-21 ∷ Toff204 ∷ CCZ024 ∷ Bx0-21 ∷ Toff023 ∷ CCZ023 ∷ Bx3-041 ∷ [])
  b0 = at 0 1 (CCZ023 ∷ Toff023 ∷ Bx3-041 ∷ Toff023 ∷ CCZ023 ∷ Bx3-041 ∷ []) (refl) ▸
       at 2 1 (CCZ034 ∷ Toff304 ∷ Bx0-31 ∷ Toff304 ∷ CCZ034 ∷ Bx0-31 ∷ []) (refl) ▸
       at 4 1 (CZ13 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 2 6 (CCZ014 ∷ []) (pw2 c4 (CCZ034 ∷ Toff304 ∷ CZ13 ∷ Toff304 ∷ CCZ034 ∷ CZ13 ∷ []) (CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (CCZ024 ∷ Toff204 ∷ CZ12 ∷ Toff204 ∷ CCZ024 ∷ CZ12 ∷ []) (pw3 c4 (CCZ014 ∷ []) (CCZ024 ∷ Toff204 ∷ CZ12 ∷ Toff204 ∷ CCZ024 ∷ CZ12 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Bx0-21 ∷ []) (refl) ▸
       at 7 1 (Bx0-21 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ023 ∷ Toff023 ∷ CCZ024 ∷ Toff204 ∷ Bx0-21 ∷ Toff204 ∷ CCZ024 ∷ Bx0-21 ∷ Toff023 ∷ CCZ023 ∷ Bx3-041 ∷ []) (CCZ023 ∷ Toff023 ∷ Bx2-041 ∷ Toff023 ∷ CCZ023 ∷ CCZ024 ∷ Toff204 ∷ Bx0-21 ∷ Toff204 ∷ CCZ024 ∷ Bx0-21 ∷ [])
  b1 = at 2 6 (Bx2-041 ∷ []) (refl) ▸
       at 5 1 (CCZ034 ∷ Toff304 ∷ Bx0-31 ∷ Toff304 ∷ CCZ034 ∷ Bx0-31 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 10 1 (CZ13 ∷ []) (refl) ▸
       at 5 6 (CCZ014 ∷ []) (pw2 c4 (CCZ034 ∷ Toff304 ∷ CZ13 ∷ Toff304 ∷ CCZ034 ∷ CZ13 ∷ []) (CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ024 ∷ Toff204 ∷ CZ12 ∷ Toff204 ∷ CCZ024 ∷ CZ12 ∷ []) (pw3 c4 (CCZ014 ∷ []) (CCZ024 ∷ Toff204 ∷ CZ12 ∷ Toff204 ∷ CCZ024 ∷ CZ12 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (Bx0-21 ∷ []) (refl) ▸
       at 10 1 (Bx0-21 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ023 ∷ Toff023 ∷ Bx2-041 ∷ Toff023 ∷ CCZ023 ∷ CCZ024 ∷ Toff204 ∷ Bx0-21 ∷ Toff204 ∷ CCZ024 ∷ Bx0-21 ∷ []) (Bx0-2341 ∷ [])
  b2 = at 5 6 (Bx2-041 ∷ []) (refl) ▸
       at 0 6 (Bx0-2341 ∷ []) (refl) ▸ done


-- box-perm-2341: 4 steps
lem-box-perm-2341 : Complete 4 → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2341 ∷ []) ⟫ʷ
lem-box-perm-2341 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ []) (Bx0-2341 ∷ [])
  b0 = at 0 1 (Bx0-2134 ∷ []) (lem-sym-ab c4) ▸
       at 0 1 (Bx0-3421 ∷ []) (lem-pairs-at1221 c4) ▸
       at 0 1 (Bx0-3241 ∷ []) (lem-sym-bc-at13243241 c4) ▸
       at 0 1 (Bx0-2341 ∷ []) (lem-sym-ab-at133441 c4) ▸ done


-- Ku-box: 6 steps
lem-Ku-box : Complete 4 → ⟪ (K0 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ K0 ∷ []) ⟫ʷ
lem-Ku-box c4 = run b0
  where
  b0 : Chain (K0 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ K0 ∷ [])
  b0 = at 1 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-box-tQ c4) ▸
       at 0 2 (CCZ012 ∷ K0 ∷ []) (lw4 c4 (K0 ∷ Toff012 ∷ []) (CCZ012 ∷ K0 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff034 ∷ K0 ∷ []) (pw1 c4 (K0 ∷ CCZ034 ∷ []) (Toff034 ∷ K0 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ012 ∷ K0 ∷ []) (lw4 c4 (K0 ∷ Toff012 ∷ []) (CCZ012 ∷ K0 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff034 ∷ K0 ∷ []) (pw1 c4 (K0 ∷ CCZ034 ∷ []) (Toff034 ∷ K0 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx0-1234 ∷ []) (sym (lem-box-cP c4)) ▸ done


-- Kdu-box: 6 steps
lem-Kdu-box : Complete 4 → ⟪ (K0⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ K0⁻ ∷ []) ⟫ʷ
lem-Kdu-box c4 = run b0
  where
  b0 : Chain (K0⁻ ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ K0⁻ ∷ [])
  b0 = at 1 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-box-tQ c4) ▸
       at 0 2 (CCZ012 ∷ K0⁻ ∷ []) (lw4 c4 (K0⁻ ∷ Toff012 ∷ []) (CCZ012 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff034 ∷ K0⁻ ∷ []) (pw1 c4 (K0⁻ ∷ CCZ034 ∷ []) (Toff034 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ012 ∷ K0⁻ ∷ []) (lw4 c4 (K0⁻ ∷ Toff012 ∷ []) (CCZ012 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff034 ∷ K0⁻ ∷ []) (pw1 c4 (K0⁻ ∷ CCZ034 ∷ []) (Toff034 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx0-1234 ∷ []) (sym (lem-box-cP c4)) ▸ done


-- Su-box: 17 steps
lem-Su-box : Complete 4 → ⟪ (S0 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ S0 ∷ []) ⟫ʷ
lem-Su-box c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (S0 ∷ Bx0-1234 ∷ []) (Toff012 ∷ S0 ∷ CS12 ∷ CCZ034 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Toff012 ∷ CCZ034 ∷ [])
  b0 = at 1 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-box-tQ c4) ▸
       at 0 2 (Toff012 ∷ S0 ∷ CS12 ∷ CCZ012 ∷ []) (lw4 c4 (S0 ∷ Toff012 ∷ []) (Toff012 ∷ S0 ∷ CS12 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ034 ∷ CS02 ∷ []) (pw1 c4 (CS02 ∷ CCZ034 ∷ []) (CCZ034 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ034 ∷ CX01 ∷ []) (pw2 c4 (CX01 ∷ CCZ034 ∷ []) (CCZ034 ∷ CX01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-CCZ034 c4) ▸
       at 4 2 (CCZ034 ∷ CX01 ∷ []) (pw2 c4 (CX01 ∷ CCZ034 ∷ []) (CCZ034 ∷ CX01 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ034 ∷ CS12 ∷ []) (lem-comm-CS12-CCZ034 c4) ▸ done

  b1 : Chain (Toff012 ∷ S0 ∷ CS12 ∷ CCZ034 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Toff012 ∷ CCZ034 ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ S0 ∷ [])
  b1 = at 4 5 (CCZ012 ∷ []) (lw4 c4 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ034 ∷ CS12 ∷ []) (lem-comm-CS12-CCZ034 c4) ▸
       at 1 2 (CCZ034 ∷ S0 ∷ []) (pw1 c4 (S0 ∷ CCZ034 ∷ []) (CCZ034 ∷ S0 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff012 ∷ CZ12 ∷ CCZ012 ∷ []) (lw4 c4 (CCZ012 ∷ Toff012 ∷ []) (Toff012 ∷ CZ12 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff012 ∷ CS12 ∷ []) (lw4 c4 (CS12 ∷ Toff012 ∷ []) (Toff012 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff012 ∷ S0 ∷ CS12 ∷ CCZ012 ∷ []) (lw4 c4 (S0 ∷ Toff012 ∷ []) (Toff012 ∷ S0 ∷ CS12 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 3 6 (S0 ∷ []) (lw4 c4 (S0 ∷ CS12 ∷ CCZ012 ∷ CS12 ∷ CZ12 ∷ CCZ012 ∷ []) (S0 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ034 ∷ S0 ∷ []) (pw1 c4 (S0 ∷ CCZ034 ∷ []) (CCZ034 ∷ S0 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ S0 ∷ []) (Bx0-1234 ∷ S0 ∷ [])
  b2 = at 0 4 (Bx0-1234 ∷ []) (sym (lem-box-tQ c4)) ▸ done


-- Sdu-box: 17 steps
lem-Sdu-box : Complete 4 → ⟪ (S0⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ S0⁻ ∷ []) ⟫ʷ
lem-Sdu-box c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (S0⁻ ∷ Bx0-1234 ∷ []) (Toff012 ∷ S0⁻ ∷ CS12⁻ ∷ CCZ034 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Toff012 ∷ CCZ034 ∷ [])
  b0 = at 1 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-box-tQ c4) ▸
       at 0 2 (Toff012 ∷ S0⁻ ∷ CS12⁻ ∷ CCZ012 ∷ []) (lw4 c4 (S0⁻ ∷ Toff012 ∷ []) (Toff012 ∷ S0⁻ ∷ CS12⁻ ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ034 ∷ CS02 ∷ []) (pw1 c4 (CS02 ∷ CCZ034 ∷ []) (CCZ034 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ034 ∷ CX01 ∷ []) (pw2 c4 (CX01 ∷ CCZ034 ∷ []) (CCZ034 ∷ CX01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-CCZ034 c4) ▸
       at 4 2 (CCZ034 ∷ CX01 ∷ []) (pw2 c4 (CX01 ∷ CCZ034 ∷ []) (CCZ034 ∷ CX01 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ034 ∷ CS12 ∷ []) (lem-comm-CS12-CCZ034 c4) ▸ done

  b1 : Chain (Toff012 ∷ S0⁻ ∷ CS12⁻ ∷ CCZ034 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Toff012 ∷ CCZ034 ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ S0⁻ ∷ [])
  b1 = at 4 5 (CCZ012 ∷ []) (lw4 c4 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-CCZ034 c4) ▸
       at 1 2 (CCZ034 ∷ S0⁻ ∷ []) (pw1 c4 (S0⁻ ∷ CCZ034 ∷ []) (CCZ034 ∷ S0⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff012 ∷ CZ12 ∷ CCZ012 ∷ []) (lw4 c4 (CCZ012 ∷ Toff012 ∷ []) (Toff012 ∷ CZ12 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff012 ∷ CS12⁻ ∷ []) (lw4 c4 (CS12⁻ ∷ Toff012 ∷ []) (Toff012 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff012 ∷ S0⁻ ∷ CS12⁻ ∷ CCZ012 ∷ []) (lw4 c4 (S0⁻ ∷ Toff012 ∷ []) (Toff012 ∷ S0⁻ ∷ CS12⁻ ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 3 6 (S0⁻ ∷ []) (lw4 c4 (S0⁻ ∷ CS12⁻ ∷ CCZ012 ∷ CS12⁻ ∷ CZ12 ∷ CCZ012 ∷ []) (S0⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ034 ∷ S0⁻ ∷ []) (pw1 c4 (S0⁻ ∷ CCZ034 ∷ []) (CCZ034 ∷ S0⁻ ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ S0⁻ ∷ []) (Bx0-1234 ∷ S0⁻ ∷ [])
  b2 = at 0 4 (Bx0-1234 ∷ []) (sym (lem-box-tQ c4)) ▸ done


-- CSu-box-1: 17 steps
lem-CSu-box-1 : Complete 4 → ⟪ (CS01 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CS01 ∷ []) ⟫ʷ
lem-CSu-box-1 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS01 ∷ Bx0-1234 ∷ []) (Toff012 ∷ CS01 ∷ CS12 ∷ CCZ034 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Toff012 ∷ CCZ034 ∷ [])
  b0 = at 1 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-box-tQ c4) ▸
       at 0 2 (Toff012 ∷ CS01 ∷ CS12 ∷ CCZ012 ∷ []) (lw4 c4 (CS01 ∷ Toff012 ∷ []) (Toff012 ∷ CS01 ∷ CS12 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ034 ∷ CS02 ∷ []) (pw1 c4 (CS02 ∷ CCZ034 ∷ []) (CCZ034 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ034 ∷ CX01 ∷ []) (pw2 c4 (CX01 ∷ CCZ034 ∷ []) (CCZ034 ∷ CX01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-CCZ034 c4) ▸
       at 4 2 (CCZ034 ∷ CX01 ∷ []) (pw2 c4 (CX01 ∷ CCZ034 ∷ []) (CCZ034 ∷ CX01 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ034 ∷ CS12 ∷ []) (lem-comm-CS12-CCZ034 c4) ▸ done

  b1 : Chain (Toff012 ∷ CS01 ∷ CS12 ∷ CCZ034 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Toff012 ∷ CCZ034 ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ CS01 ∷ [])
  b1 = at 4 5 (CCZ012 ∷ []) (lw4 c4 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ034 ∷ CS12 ∷ []) (lem-comm-CS12-CCZ034 c4) ▸
       at 1 2 (CCZ034 ∷ CS01 ∷ []) (pw2 c4 (CS01 ∷ CCZ034 ∷ []) (CCZ034 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff012 ∷ CZ12 ∷ CCZ012 ∷ []) (lw4 c4 (CCZ012 ∷ Toff012 ∷ []) (Toff012 ∷ CZ12 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff012 ∷ CS12 ∷ []) (lw4 c4 (CS12 ∷ Toff012 ∷ []) (Toff012 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff012 ∷ CS01 ∷ CS12 ∷ CCZ012 ∷ []) (lw4 c4 (CS01 ∷ Toff012 ∷ []) (Toff012 ∷ CS01 ∷ CS12 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 3 6 (CS01 ∷ []) (lw4 c4 (CS01 ∷ CS12 ∷ CCZ012 ∷ CS12 ∷ CZ12 ∷ CCZ012 ∷ []) (CS01 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ034 ∷ CS01 ∷ []) (pw2 c4 (CS01 ∷ CCZ034 ∷ []) (CCZ034 ∷ CS01 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ CS01 ∷ []) (Bx0-1234 ∷ CS01 ∷ [])
  b2 = at 0 4 (Bx0-1234 ∷ []) (sym (lem-box-tQ c4)) ▸ done

