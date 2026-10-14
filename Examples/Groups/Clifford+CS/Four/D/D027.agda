{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D027 where

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
open import Examples.Groups.Clifford+CS.Four.D.D026 using (lem-comm-CCZ012-CS03)
open import Examples.Groups.Clifford+CS.Four.D.D017 using (lem-comm-CCZ012-CSd03)

-- CCZ012 passes PP3: 13 steps (scratchpad/four/lower.py)
lem-CCZ012-passes-PP3 : ⟪ (CCZ012 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CCZ012 ∷ []) ⟫ʷ
lem-CCZ012-passes-PP3 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ012 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CCZ012 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ CZ12 ∷ Sw23 ∷ Sw23 ∷ Toff012 ∷ CS03⁻ ∷ [])
  b0 = at 0 2 (Toff012 ∷ CCZ012 ∷ CZ12 ∷ []) (win 3 0 complete₃ (CCZ • Toff) (Toff • CCZ • (CZ ↑)) tt tt Eq.refl) ▸
       at 3 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 3 (CZ13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw12 ∷ CZ23 ∷ []) (win 0 3 complete₃ ((Swap ↑ • CZ • Swap ↑) • Swap) (Swap • (CZ ↑)) tt tt Eq.refl) ▸
       at 4 2 (CS01 ∷ CZ23 ∷ []) (sym (low-comm (CS) (CZ))) ▸
       at 5 2 (Sw12 ∷ CZ13 ∷ []) (win 0 3 complete₃ ((CZ ↑) • Swap) (Swap • (Swap ↑ • CZ • Swap ↑)) tt tt Eq.refl) ▸
       at 6 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Toff012 ∷ CCZ012 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ CZ12 ∷ Sw23 ∷ Sw23 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CCZ012 ∷ [])
  b1 = at 8 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 2 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (CS03 ∷ CCZ012 ∷ []) (lem-comm-CCZ012-CS03) ▸
       at 2 3 (Toff012 ∷ CCZ012 ∷ []) (win 3 0 complete₃ (CCZ • (CZ ↑) • Toff) (Toff • CCZ) tt tt Eq.refl) ▸
       at 3 2 (CS03⁻ ∷ CCZ012 ∷ []) (lem-comm-CCZ012-CSd03) ▸ done

