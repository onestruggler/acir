{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D118 where

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

-- xr0 0000: 0 steps
lem-xr0-0000 : ⟪ [] ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-xr0-0000 = refl

-- xr0 1000: 0 steps
lem-xr0-1000 : ⟪ (X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ []) ⟫ʷ
lem-xr0-1000 = refl

-- xr0 0100: 0 steps
lem-xr0-0100 : ⟪ (X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ []) ⟫ʷ
lem-xr0-0100 = refl

-- xr0 1100: 1 steps
lem-xr0-1100 : ⟪ (X1 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ []) ⟫ʷ
lem-xr0-1100 = run b0
  where
  b0 : Chain (X1 ∷ X0 ∷ []) (X0 ∷ X1 ∷ [])
  b0 = at 0 2 (X0 ∷ X1 ∷ []) (sym (low₁-comm (X) (X))) ▸ done


-- xr0 0010: 0 steps
lem-xr0-0010 : ⟪ (X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ []) ⟫ʷ
lem-xr0-0010 = refl

-- xr0 1010: 0 steps
lem-xr0-1010 : ⟪ (X1 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ []) ⟫ʷ
lem-xr0-1010 = refl

-- xr0 0110: 0 steps
lem-xr0-0110 : ⟪ (X0 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ []) ⟫ʷ
lem-xr0-0110 = refl

-- xr0 1110: 1 steps
lem-xr0-1110 : ⟪ (X1 ∷ X0 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X2 ∷ []) ⟫ʷ
lem-xr0-1110 = run b0
  where
  b0 : Chain (X1 ∷ X0 ∷ X2 ∷ []) (X0 ∷ X1 ∷ X2 ∷ [])
  b0 = at 0 2 (X0 ∷ X1 ∷ []) (sym (low₁-comm (X) (X))) ▸ done


-- xr0 0001: 0 steps
lem-xr0-0001 : ⟪ (X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ []) ⟫ʷ
lem-xr0-0001 = refl

-- xr0 1001: 0 steps
lem-xr0-1001 : ⟪ (X1 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X3 ∷ []) ⟫ʷ
lem-xr0-1001 = refl

-- xr0 0101: 0 steps
lem-xr0-0101 : ⟪ (X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ []) ⟫ʷ
lem-xr0-0101 = refl

-- xr0 1101: 1 steps
lem-xr0-1101 : ⟪ (X1 ∷ X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X3 ∷ []) ⟫ʷ
lem-xr0-1101 = run b0
  where
  b0 : Chain (X1 ∷ X0 ∷ X3 ∷ []) (X0 ∷ X1 ∷ X3 ∷ [])
  b0 = at 0 2 (X0 ∷ X1 ∷ []) (sym (low₁-comm (X) (X))) ▸ done


-- xr0 0011: 0 steps
lem-xr0-0011 : ⟪ (X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ []) ⟫ʷ
lem-xr0-0011 = refl

-- xr0 1011: 0 steps
lem-xr0-1011 : ⟪ (X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-xr0-1011 = refl

-- xr0 0111: 0 steps
lem-xr0-0111 : ⟪ (X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-xr0-0111 = refl

-- xr0 1111: 1 steps
lem-xr0-1111 : ⟪ (X1 ∷ X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-xr0-1111 = run b0
  where
  b0 : Chain (X1 ∷ X0 ∷ X2 ∷ X3 ∷ []) (X0 ∷ X1 ∷ X2 ∷ X3 ∷ [])
  b0 = at 0 2 (X0 ∷ X1 ∷ []) (sym (low₁-comm (X) (X))) ▸ done

