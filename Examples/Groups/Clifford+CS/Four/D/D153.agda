{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D153 where

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
open import Examples.Groups.Clifford+CS.Four.D.D152 using (lem-pass-TOFF012-vs-CSd23)
-- pass [CSd23] [TOFF012]: 1 steps
lem-pass-CSd23-vs-TOFF012 : ⟪ (CS23⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS23⁻ ∷ []) ⟫ʷ
lem-pass-CSd23-vs-TOFF012 = run b0
  where
  b0 : Chain (CS23⁻ ∷ Toff012 ∷ []) (Toff012 ∷ CS23⁻ ∷ [])
  b0 = at 0 2 (Toff012 ∷ CS23⁻ ∷ []) (sym lem-pass-TOFF012-vs-CSd23) ▸ done

