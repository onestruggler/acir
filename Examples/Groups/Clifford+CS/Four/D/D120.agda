{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D120 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Tools using (ax)
open import Examples.Groups.Clifford+CS.Windows using (win)
open import Examples.Groups.Clifford+CS.Completeness using (complete₃)
open import Examples.Groups.Clifford+CS.TopWeakening using (low-comm)
open import Examples.Groups.Clifford+CS.Idle using (low₁-comm)
open import Examples.Groups.Clifford+CS.Four.Chain

-- xr2 0000: 0 steps
lem-xr2-0000 : ⟪ [] ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-xr2-0000 = refl

-- xr2 1000: 0 steps
lem-xr2-1000 : ⟪ (X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ []) ⟫ʷ
lem-xr2-1000 = refl

-- xr2 0100: 0 steps
lem-xr2-0100 : ⟪ (X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ []) ⟫ʷ
lem-xr2-0100 = refl

-- xr2 1100: 0 steps
lem-xr2-1100 : ⟪ (X0 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ []) ⟫ʷ
lem-xr2-1100 = refl

-- xr2 0010: 0 steps
lem-xr2-0010 : ⟪ (X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ []) ⟫ʷ
lem-xr2-0010 = refl

-- xr2 1010: 0 steps
lem-xr2-1010 : ⟪ (X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ []) ⟫ʷ
lem-xr2-1010 = refl

-- xr2 0110: 0 steps
lem-xr2-0110 : ⟪ (X1 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X3 ∷ []) ⟫ʷ
lem-xr2-0110 = refl

-- xr2 1110: 0 steps
lem-xr2-1110 : ⟪ (X0 ∷ X1 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X3 ∷ []) ⟫ʷ
lem-xr2-1110 = refl

-- xr2 0001: 0 steps
lem-xr2-0001 : ⟪ (X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ []) ⟫ʷ
lem-xr2-0001 = refl

-- xr2 1001: 0 steps
lem-xr2-1001 : ⟪ (X0 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ []) ⟫ʷ
lem-xr2-1001 = refl

-- xr2 0101: 0 steps
lem-xr2-0101 : ⟪ (X1 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ []) ⟫ʷ
lem-xr2-0101 = refl

-- xr2 1101: 0 steps
lem-xr2-1101 : ⟪ (X0 ∷ X1 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X2 ∷ []) ⟫ʷ
lem-xr2-1101 = refl

-- xr2 0011: 1 steps
lem-xr2-0011 : ⟪ (X3 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ []) ⟫ʷ
lem-xr2-0011 = run b0
  where
  b0 : Chain (X3 ∷ X2 ∷ []) (X2 ∷ X3 ∷ [])
  b0 = at 0 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸ done


-- xr2 1011: 1 steps
lem-xr2-1011 : ⟪ (X0 ∷ X3 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-xr2-1011 = run b0
  where
  b0 : Chain (X0 ∷ X3 ∷ X2 ∷ []) (X0 ∷ X2 ∷ X3 ∷ [])
  b0 = at 1 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸ done


-- xr2 0111: 1 steps
lem-xr2-0111 : ⟪ (X1 ∷ X3 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-xr2-0111 = run b0
  where
  b0 : Chain (X1 ∷ X3 ∷ X2 ∷ []) (X1 ∷ X2 ∷ X3 ∷ [])
  b0 = at 1 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸ done


-- xr2 1111: 1 steps
lem-xr2-1111 : ⟪ (X0 ∷ X1 ∷ X3 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-xr2-1111 = run b0
  where
  b0 : Chain (X0 ∷ X1 ∷ X3 ∷ X2 ∷ []) (X0 ∷ X1 ∷ X2 ∷ X3 ∷ [])
  b0 = at 2 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸ done

