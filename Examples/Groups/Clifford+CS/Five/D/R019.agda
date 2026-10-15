{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.R019 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Lits using (lw0 ; lw1 ; lw2 ; lw3 ; lw4)

-- comm TOFF014 CX23: 9 steps
lem-comm-TOFF014-CX23 : Complete 4 → ⟪ (Toff014 ∷ CX23 ∷ []) ⟫ʷ ≈ ⟪ (CX23 ∷ Toff014 ∷ []) ⟫ʷ
lem-comm-TOFF014-CX23 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff014 ∷ CX23 ∷ []) (CX23 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 0 1 (Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CX24 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX34 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CX24 ∷ []) (CX34 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CX34 ∷ Toff012 ∷ []) (c₃ (Toff) (CX₀₁)) ▸
       at 1 2 (CX24 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CX34 ∷ []) (CX24 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 1 (Sw34 ∷ CX23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸ done

  b1 : Chain (CX23 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ []) (CX23 ∷ Toff014 ∷ [])
  b1 = at 1 5 (Toff014 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CCZ024 CS13: 11 steps
lem-comm-CCZ024-CS13 : Complete 4 → ⟪ (CCZ024 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ CCZ024 ∷ []) ⟫ʷ
lem-comm-CCZ024-CS13 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ024 ∷ CS13 ∷ []) (Sw12 ∷ Sw34 ∷ Sw34 ∷ CS23 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ [])
  b0 = at 0 1 (Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CS23 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS13 ∷ []) (CS23 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (CS24 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS34 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS24 ∷ []) (CS34 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CS34 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CS)) ▸
       at 2 2 (CS24 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS34 ∷ []) (CS24 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw12 ∷ Sw34 ∷ Sw34 ∷ CS23 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) (CS13 ∷ CCZ024 ∷ [])
  b1 = at 1 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 0 2 (CS13 ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS23 ∷ []) (CS13 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 7 (CCZ024 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CCZ024 CSd13: 11 steps
lem-comm-CCZ024-CSd13 : Complete 4 → ⟪ (CCZ024 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ CCZ024 ∷ []) ⟫ʷ
lem-comm-CCZ024-CSd13 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ024 ∷ CS13⁻ ∷ []) (Sw12 ∷ Sw34 ∷ Sw34 ∷ CS23⁻ ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ [])
  b0 = at 0 1 (Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CS23⁻ ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS13⁻ ∷ []) (CS23⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (CS24⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS34⁻ ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS24⁻ ∷ []) (CS34⁻ ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CS34⁻ ∷ CCZ012 ∷ []) (c₃ (CCZ) (CS • CS • CS)) ▸
       at 2 2 (CS24⁻ ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS34⁻ ∷ []) (CS24⁻ ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw12 ∷ Sw34 ∷ Sw34 ∷ CS23⁻ ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) (CS13⁻ ∷ CCZ024 ∷ [])
  b1 = at 1 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 0 2 (CS13⁻ ∷ Sw12 ∷ []) (lw4 c4 (Sw12 ∷ CS23⁻ ∷ []) (CS13⁻ ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 7 (CCZ024 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm TOFF013 CX24: 15 steps
lem-comm-TOFF013-CX24 : Complete 4 → ⟪ (Toff013 ∷ CX24 ∷ []) ⟫ʷ ≈ ⟪ (CX24 ∷ Toff013 ∷ []) ⟫ʷ
lem-comm-TOFF013-CX24 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff013 ∷ CX24 ∷ []) (Sw34 ∷ Sw34 ∷ Sw23 ∷ CX34 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ CX23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Toff014 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (lw0 c4 [] (Sw34 ∷ Sw34 ∷ []) tt tt Eq.refl) ▸
       at 5 3 (CX24 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX34 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CX24 ∷ []) (CX34 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CX34 ∷ Toff012 ∷ []) (c₃ (Toff) (CX₀₁)) ▸ done

  b1 : Chain (Sw34 ∷ Sw34 ∷ Sw23 ∷ CX34 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ []) (CX24 ∷ Toff013 ∷ [])
  b1 = at 2 2 (CX24 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CX34 ∷ []) (CX24 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sw34 ∷ CX23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 2 5 (Toff014 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ Toff013 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (lw0 c4 (Sw34 ∷ Sw34 ∷ []) [] tt tt Eq.refl) ▸
       at 0 3 (CX24 ∷ []) (by-assoc Eq.refl) ▸ done

