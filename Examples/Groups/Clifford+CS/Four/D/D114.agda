{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D114 where

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

-- xt2 0000: 0 steps
lem-xt2-0000 : ⟪ (X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ []) ⟫ʷ
lem-xt2-0000 = refl

-- xs2 0000: 0 steps
lem-xs2-0000 : ⟪ (X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ []) ⟫ʷ
lem-xs2-0000 = refl

-- xt2 1000: 1 steps
lem-xt2-1000 : ⟪ (X2 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ []) ⟫ʷ
lem-xt2-1000 = run b0
  where
  b0 : Chain (X2 ∷ X0 ∷ []) (X0 ∷ X2 ∷ [])
  b0 = at 0 2 (X0 ∷ X2 ∷ []) (sym (low₁-comm (X) ((X ↑)))) ▸ done


-- xs2 1000: 0 steps
lem-xs2-1000 : ⟪ (X0 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ []) ⟫ʷ
lem-xs2-1000 = refl

-- xt2 0100: 1 steps
lem-xt2-0100 : ⟪ (X2 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ []) ⟫ʷ
lem-xt2-0100 = run b0
  where
  b0 : Chain (X2 ∷ X1 ∷ []) (X1 ∷ X2 ∷ [])
  b0 = at 0 2 (X1 ∷ X2 ∷ []) (sym (low-comm ((X ↑)) (X))) ▸ done


-- xs2 0100: 0 steps
lem-xs2-0100 : ⟪ (X1 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ []) ⟫ʷ
lem-xs2-0100 = refl

-- xt2 1100: 2 steps
lem-xt2-1100 : ⟪ (X2 ∷ X0 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X2 ∷ []) ⟫ʷ
lem-xt2-1100 = run b0
  where
  b0 : Chain (X2 ∷ X0 ∷ X1 ∷ []) (X0 ∷ X1 ∷ X2 ∷ [])
  b0 = at 0 2 (X0 ∷ X2 ∷ []) (sym (low₁-comm (X) ((X ↑)))) ▸
       at 1 2 (X1 ∷ X2 ∷ []) (sym (low-comm ((X ↑)) (X))) ▸ done


-- xs2 1100: 0 steps
lem-xs2-1100 : ⟪ (X0 ∷ X1 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X2 ∷ []) ⟫ʷ
lem-xs2-1100 = refl

-- xt2 0010: 1 steps
lem-xt2-0010 : ⟪ (X2 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-xt2-0010 = run b0
  where
  b0 : Chain (X2 ∷ X2 ∷ []) []
  b0 = at 0 2 [] (win 3 0 complete₃ ((X ↑ ↑) • (X ↑ ↑)) (ε) tt tt Eq.refl) ▸ done


-- xs2 0010: 1 steps
lem-xs2-0010 : ⟪ (X2 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-xs2-0010 = run b0
  where
  b0 : Chain (X2 ∷ X2 ∷ []) []
  b0 = at 0 2 [] (win 3 0 complete₃ ((X ↑ ↑) • (X ↑ ↑)) (ε) tt tt Eq.refl) ▸ done


-- xt2 1010: 2 steps
lem-xt2-1010 : ⟪ (X2 ∷ X0 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ []) ⟫ʷ
lem-xt2-1010 = run b0
  where
  b0 : Chain (X2 ∷ X0 ∷ X2 ∷ []) (X0 ∷ [])
  b0 = at 0 2 (X0 ∷ X2 ∷ []) (sym (low₁-comm (X) ((X ↑)))) ▸
       at 1 2 [] (win 3 0 complete₃ ((X ↑ ↑) • (X ↑ ↑)) (ε) tt tt Eq.refl) ▸ done


-- xs2 1010: 1 steps
lem-xs2-1010 : ⟪ (X0 ∷ X2 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ []) ⟫ʷ
lem-xs2-1010 = run b0
  where
  b0 : Chain (X0 ∷ X2 ∷ X2 ∷ []) (X0 ∷ [])
  b0 = at 1 2 [] (win 3 0 complete₃ ((X ↑ ↑) • (X ↑ ↑)) (ε) tt tt Eq.refl) ▸ done


-- xt2 0110: 2 steps
lem-xt2-0110 : ⟪ (X2 ∷ X1 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ []) ⟫ʷ
lem-xt2-0110 = run b0
  where
  b0 : Chain (X2 ∷ X1 ∷ X2 ∷ []) (X1 ∷ [])
  b0 = at 0 2 (X1 ∷ X2 ∷ []) (sym (low-comm ((X ↑)) (X))) ▸
       at 1 2 [] (win 3 0 complete₃ ((X ↑ ↑) • (X ↑ ↑)) (ε) tt tt Eq.refl) ▸ done


-- xs2 0110: 1 steps
lem-xs2-0110 : ⟪ (X1 ∷ X2 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ []) ⟫ʷ
lem-xs2-0110 = run b0
  where
  b0 : Chain (X1 ∷ X2 ∷ X2 ∷ []) (X1 ∷ [])
  b0 = at 1 2 [] (win 3 0 complete₃ ((X ↑ ↑) • (X ↑ ↑)) (ε) tt tt Eq.refl) ▸ done


-- xt2 1110: 3 steps
lem-xt2-1110 : ⟪ (X2 ∷ X0 ∷ X1 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ []) ⟫ʷ
lem-xt2-1110 = run b0
  where
  b0 : Chain (X2 ∷ X0 ∷ X1 ∷ X2 ∷ []) (X0 ∷ X1 ∷ [])
  b0 = at 0 2 (X0 ∷ X2 ∷ []) (sym (low₁-comm (X) ((X ↑)))) ▸
       at 1 2 (X1 ∷ X2 ∷ []) (sym (low-comm ((X ↑)) (X))) ▸
       at 2 2 [] (win 3 0 complete₃ ((X ↑ ↑) • (X ↑ ↑)) (ε) tt tt Eq.refl) ▸ done


-- xs2 1110: 1 steps
lem-xs2-1110 : ⟪ (X0 ∷ X1 ∷ X2 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ []) ⟫ʷ
lem-xs2-1110 = run b0
  where
  b0 : Chain (X0 ∷ X1 ∷ X2 ∷ X2 ∷ []) (X0 ∷ X1 ∷ [])
  b0 = at 2 2 [] (win 3 0 complete₃ ((X ↑ ↑) • (X ↑ ↑)) (ε) tt tt Eq.refl) ▸ done

