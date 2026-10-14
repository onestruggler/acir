{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D067 where

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
open import Examples.Groups.Clifford+CS.Four.D.D066 using (lem-PPi≡PP3^3)
open import Examples.Groups.Clifford+CS.Four.D.D036 using (lem-S3)

-- S3i: 7 steps (scratchpad/four/lower.py)
lem-S3i : ⟪ (Sw23 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ
lem-S3i = run b0
  where
  b0 : Chain (Sw23 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ Sw23 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ [])
  b0 = at 1 4 (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (lem-PPi≡PP3^3) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 12 6 (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (lem-S3) ▸
       at 6 6 (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (lem-S3) ▸
       at 0 6 (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (lem-S3) ▸
       at 0 12 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (sym lem-PPi≡PP3^3) ▸ done

