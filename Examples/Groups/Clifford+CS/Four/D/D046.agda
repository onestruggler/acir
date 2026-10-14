{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D046 where

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
open import Examples.Groups.Clifford+CS.Four.D.D045 using (lem-B≡F)

-- ROT=[c,F]: 3 steps (scratchpad/four/lower.py)
lem-ROT≡cF : ⟪ (CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ S1 ∷ CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ []) ⟫ʷ ≈ ⟪ (CK10 ∷ CCZ023 ∷ CK10⁻ ∷ CCZ023 ∷ []) ⟫ʷ
lem-ROT≡cF = run b0
  where
  b0 : Chain (CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ S1 ∷ CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ []) (CK10 ∷ CCZ023 ∷ CK10⁻ ∷ CCZ023 ∷ [])
  b0 = at 1 6 (CCZ023 ∷ []) (lem-B≡F) ▸
       at 4 6 (CCZ023 ∷ []) (lem-B≡F) ▸
       at 2 2 (CK10⁻ ∷ []) (win 3 0 complete₃ ((S ↑) • CK₁₀) ((S ↑ • CK₁₀)) tt tt Eq.refl) ▸ done

