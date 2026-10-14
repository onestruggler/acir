{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D055 where

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
open import Examples.Groups.Clifford+CS.Four.D.D050 using (lem-PUinv)
open import Examples.Groups.Clifford+CS.Four.D.D047 using (lem-Rk)
open import Examples.Groups.Clifford+CS.Four.D.D048 using (lem-SW13-Rk)

-- ROT-form: 7 steps (scratchpad/four/lower.py)
lem-ROT-form : ⟪ (CK10 ∷ CCZ023 ∷ CK10⁻ ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ K0⁻ ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ K0⁻ ∷ []) ⟫ʷ
lem-ROT-form = run b0
  where
  b0 : Chain (CK10 ∷ CCZ023 ∷ CK10⁻ ∷ CCZ023 ∷ []) (K0 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ K0⁻ ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ K0⁻ ∷ [])
  b0 = at 0 0 (K0 ∷ K0⁻ ∷ []) (win 3 0 complete₃ (ε) (K • (K • iI)) tt tt Eq.refl) ▸
       at 6 0 (K0 ∷ K0⁻ ∷ []) (win 3 0 complete₃ (ε) (K • (K • iI)) tt tt Eq.refl) ▸
       at 1 6 (CK10 ∷ Toff023 ∷ CK10⁻ ∷ Toff023 ∷ []) (lem-Rk) ▸
       at 5 0 (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (win 0 3 complete₃ (ε) (Swap • (Swap ↑) • Swap • Swap • (Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 1 0 (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (win 0 3 complete₃ (ε) (Swap • (Swap ↑) • Swap • Swap • (Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 4 10 (CK30 ∷ Toff012 ∷ CK30⁻ ∷ Toff012 ∷ []) (lem-SW13-Rk) ▸
       at 4 4 (K0⁻ ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ []) (sym lem-PUinv) ▸ done

