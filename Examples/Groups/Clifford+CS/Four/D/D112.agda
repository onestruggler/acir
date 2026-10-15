{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D112 where

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

-- xt1 0000: 0 steps
lem-xt1-0000 : ⟪ (X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ []) ⟫ʷ
lem-xt1-0000 = refl

-- xs1 0000: 0 steps
lem-xs1-0000 : ⟪ (X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ []) ⟫ʷ
lem-xs1-0000 = refl

-- xt1 1000: 1 steps
lem-xt1-1000 : ⟪ (X1 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ []) ⟫ʷ
lem-xt1-1000 = run b0
  where
  b0 : Chain (X1 ∷ X0 ∷ []) (X0 ∷ X1 ∷ [])
  b0 = at 0 2 (X0 ∷ X1 ∷ []) (sym (low₁-comm (X) (X))) ▸ done


-- xs1 1000: 0 steps
lem-xs1-1000 : ⟪ (X0 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ []) ⟫ʷ
lem-xs1-1000 = refl

-- xt1 0100: 1 steps
lem-xt1-0100 : ⟪ (X1 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-xt1-0100 = run b0
  where
  b0 : Chain (X1 ∷ X1 ∷ []) []
  b0 = at 0 2 [] (win 3 0 complete₃ ((X ↑) • (X ↑)) (ε) tt tt Eq.refl) ▸ done


-- xs1 0100: 1 steps
lem-xs1-0100 : ⟪ (X1 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-xs1-0100 = run b0
  where
  b0 : Chain (X1 ∷ X1 ∷ []) []
  b0 = at 0 2 [] (win 3 0 complete₃ ((X ↑) • (X ↑)) (ε) tt tt Eq.refl) ▸ done


-- xt1 1100: 2 steps
lem-xt1-1100 : ⟪ (X1 ∷ X0 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ []) ⟫ʷ
lem-xt1-1100 = run b0
  where
  b0 : Chain (X1 ∷ X0 ∷ X1 ∷ []) (X0 ∷ [])
  b0 = at 0 2 (X0 ∷ X1 ∷ []) (sym (low₁-comm (X) (X))) ▸
       at 1 2 [] (win 3 0 complete₃ ((X ↑) • (X ↑)) (ε) tt tt Eq.refl) ▸ done


-- xs1 1100: 1 steps
lem-xs1-1100 : ⟪ (X0 ∷ X1 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ []) ⟫ʷ
lem-xs1-1100 = run b0
  where
  b0 : Chain (X0 ∷ X1 ∷ X1 ∷ []) (X0 ∷ [])
  b0 = at 1 2 [] (win 3 0 complete₃ ((X ↑) • (X ↑)) (ε) tt tt Eq.refl) ▸ done


-- xt1 0010: 0 steps
lem-xt1-0010 : ⟪ (X1 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ []) ⟫ʷ
lem-xt1-0010 = refl

-- xs1 0010: 1 steps
lem-xs1-0010 : ⟪ (X2 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ []) ⟫ʷ
lem-xs1-0010 = run b0
  where
  b0 : Chain (X2 ∷ X1 ∷ []) (X1 ∷ X2 ∷ [])
  b0 = at 0 2 (X1 ∷ X2 ∷ []) (sym (low-comm ((X ↑)) (X))) ▸ done


-- xt1 1010: 1 steps
lem-xt1-1010 : ⟪ (X1 ∷ X0 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X2 ∷ []) ⟫ʷ
lem-xt1-1010 = run b0
  where
  b0 : Chain (X1 ∷ X0 ∷ X2 ∷ []) (X0 ∷ X1 ∷ X2 ∷ [])
  b0 = at 0 2 (X0 ∷ X1 ∷ []) (sym (low₁-comm (X) (X))) ▸ done


-- xs1 1010: 1 steps
lem-xs1-1010 : ⟪ (X0 ∷ X2 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X2 ∷ []) ⟫ʷ
lem-xs1-1010 = run b0
  where
  b0 : Chain (X0 ∷ X2 ∷ X1 ∷ []) (X0 ∷ X1 ∷ X2 ∷ [])
  b0 = at 1 2 (X1 ∷ X2 ∷ []) (sym (low-comm ((X ↑)) (X))) ▸ done


-- xt1 0110: 1 steps
lem-xt1-0110 : ⟪ (X1 ∷ X1 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ []) ⟫ʷ
lem-xt1-0110 = run b0
  where
  b0 : Chain (X1 ∷ X1 ∷ X2 ∷ []) (X2 ∷ [])
  b0 = at 0 2 [] (win 3 0 complete₃ ((X ↑) • (X ↑)) (ε) tt tt Eq.refl) ▸ done


-- xs1 0110: 2 steps
lem-xs1-0110 : ⟪ (X1 ∷ X2 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ []) ⟫ʷ
lem-xs1-0110 = run b0
  where
  b0 : Chain (X1 ∷ X2 ∷ X1 ∷ []) (X2 ∷ [])
  b0 = at 1 2 (X1 ∷ X2 ∷ []) (sym (low-comm ((X ↑)) (X))) ▸
       at 0 2 [] (win 3 0 complete₃ ((X ↑) • (X ↑)) (ε) tt tt Eq.refl) ▸ done


-- xt1 1110: 2 steps
lem-xt1-1110 : ⟪ (X1 ∷ X0 ∷ X1 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ []) ⟫ʷ
lem-xt1-1110 = run b0
  where
  b0 : Chain (X1 ∷ X0 ∷ X1 ∷ X2 ∷ []) (X0 ∷ X2 ∷ [])
  b0 = at 0 2 (X0 ∷ X1 ∷ []) (sym (low₁-comm (X) (X))) ▸
       at 1 2 [] (win 3 0 complete₃ ((X ↑) • (X ↑)) (ε) tt tt Eq.refl) ▸ done


-- xs1 1110: 2 steps
lem-xs1-1110 : ⟪ (X0 ∷ X1 ∷ X2 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ []) ⟫ʷ
lem-xs1-1110 = run b0
  where
  b0 : Chain (X0 ∷ X1 ∷ X2 ∷ X1 ∷ []) (X0 ∷ X2 ∷ [])
  b0 = at 2 2 (X1 ∷ X2 ∷ []) (sym (low-comm ((X ↑)) (X))) ▸
       at 1 2 [] (win 3 0 complete₃ ((X ↑) • (X ↑)) (ε) tt tt Eq.refl) ▸ done

