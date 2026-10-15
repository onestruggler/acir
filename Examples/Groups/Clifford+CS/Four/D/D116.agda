{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D116 where

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

-- xt3 0000: 0 steps
lem-xt3-0000 : ⟪ (X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ []) ⟫ʷ
lem-xt3-0000 = refl

-- xs3 0000: 0 steps
lem-xs3-0000 : ⟪ (X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ []) ⟫ʷ
lem-xs3-0000 = refl

-- xt3 1000: 1 steps
lem-xt3-1000 : ⟪ (X3 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ []) ⟫ʷ
lem-xt3-1000 = run b0
  where
  b0 : Chain (X3 ∷ X0 ∷ []) (X0 ∷ X3 ∷ [])
  b0 = at 0 2 (X0 ∷ X3 ∷ []) (sym (low₁-comm (X) ((X ↑ ↑)))) ▸ done


-- xs3 1000: 0 steps
lem-xs3-1000 : ⟪ (X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ []) ⟫ʷ
lem-xs3-1000 = refl

-- xt3 0100: 1 steps
lem-xt3-0100 : ⟪ (X3 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X3 ∷ []) ⟫ʷ
lem-xt3-0100 = run b0
  where
  b0 : Chain (X3 ∷ X1 ∷ []) (X1 ∷ X3 ∷ [])
  b0 = at 0 2 (X1 ∷ X3 ∷ []) (sym (low-comm ((X ↑)) ((X ↑)))) ▸ done


-- xs3 0100: 0 steps
lem-xs3-0100 : ⟪ (X1 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X3 ∷ []) ⟫ʷ
lem-xs3-0100 = refl

-- xt3 1100: 2 steps
lem-xt3-1100 : ⟪ (X3 ∷ X0 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X3 ∷ []) ⟫ʷ
lem-xt3-1100 = run b0
  where
  b0 : Chain (X3 ∷ X0 ∷ X1 ∷ []) (X0 ∷ X1 ∷ X3 ∷ [])
  b0 = at 0 2 (X0 ∷ X3 ∷ []) (sym (low₁-comm (X) ((X ↑ ↑)))) ▸
       at 1 2 (X1 ∷ X3 ∷ []) (sym (low-comm ((X ↑)) ((X ↑)))) ▸ done


-- xs3 1100: 0 steps
lem-xs3-1100 : ⟪ (X0 ∷ X1 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X3 ∷ []) ⟫ʷ
lem-xs3-1100 = refl

-- xt3 0010: 1 steps
lem-xt3-0010 : ⟪ (X3 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ []) ⟫ʷ
lem-xt3-0010 = run b0
  where
  b0 : Chain (X3 ∷ X2 ∷ []) (X2 ∷ X3 ∷ [])
  b0 = at 0 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸ done


-- xs3 0010: 0 steps
lem-xs3-0010 : ⟪ (X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ []) ⟫ʷ
lem-xs3-0010 = refl

-- xt3 1010: 2 steps
lem-xt3-1010 : ⟪ (X3 ∷ X0 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-xt3-1010 = run b0
  where
  b0 : Chain (X3 ∷ X0 ∷ X2 ∷ []) (X0 ∷ X2 ∷ X3 ∷ [])
  b0 = at 0 2 (X0 ∷ X3 ∷ []) (sym (low₁-comm (X) ((X ↑ ↑)))) ▸
       at 1 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸ done


-- xs3 1010: 0 steps
lem-xs3-1010 : ⟪ (X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-xs3-1010 = refl

-- xt3 0110: 2 steps
lem-xt3-0110 : ⟪ (X3 ∷ X1 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-xt3-0110 = run b0
  where
  b0 : Chain (X3 ∷ X1 ∷ X2 ∷ []) (X1 ∷ X2 ∷ X3 ∷ [])
  b0 = at 0 2 (X1 ∷ X3 ∷ []) (sym (low-comm ((X ↑)) ((X ↑)))) ▸
       at 1 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸ done


-- xs3 0110: 0 steps
lem-xs3-0110 : ⟪ (X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-xs3-0110 = refl

-- xt3 1110: 3 steps
lem-xt3-1110 : ⟪ (X3 ∷ X0 ∷ X1 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-xt3-1110 = run b0
  where
  b0 : Chain (X3 ∷ X0 ∷ X1 ∷ X2 ∷ []) (X0 ∷ X1 ∷ X2 ∷ X3 ∷ [])
  b0 = at 0 2 (X0 ∷ X3 ∷ []) (sym (low₁-comm (X) ((X ↑ ↑)))) ▸
       at 1 2 (X1 ∷ X3 ∷ []) (sym (low-comm ((X ↑)) ((X ↑)))) ▸
       at 2 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸ done


-- xs3 1110: 0 steps
lem-xs3-1110 : ⟪ (X0 ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-xs3-1110 = refl
