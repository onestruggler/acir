{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D068 where

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
open import Examples.Groups.Clifford+CS.Four.D.D055 using (lem-ROT-form)
open import Examples.Groups.Clifford+CS.Four.D.D046 using (lem-ROT≡cF)
open import Examples.Groups.Clifford+CS.Four.D.D067 using (lem-S3i)

-- SW12-ROT: 17 steps (scratchpad/four/lower.py)
lem-SW12-ROT : ⟪ (Sw12 ∷ CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ S1 ∷ CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ S1 ∷ CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ []) ⟫ʷ
lem-SW12-ROT = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw12 ∷ CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ S1 ∷ CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ Sw12 ∷ []) (K0 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ K0⁻ ∷ S0 ∷ K0 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ Sw23 ∷ Sw23 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ K0⁻ ∷ Sw12 ∷ [])
  b0 = at 1 15 (CK10 ∷ CCZ023 ∷ CK10⁻ ∷ CCZ023 ∷ []) (lem-ROT≡cF) ▸
       at 1 4 (K0 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ K0⁻ ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ K0⁻ ∷ []) (lem-ROT-form) ▸
       at 0 2 (K0 ∷ Sw12 ∷ []) (sym (low₁-comm (K) (Swap))) ▸
       at 1 4 (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (win 0 3 complete₃ (Swap • Swap • (Swap ↑) • Swap) (Swap • (Swap ↑) • Swap • (Swap ↑)) tt tt Eq.refl) ▸
       at 4 2 (K0⁻ ∷ Sw23 ∷ []) (sym (low₁-comm ((K • iI)) ((Swap ↑)))) ▸
       at 5 2 (S0 ∷ Sw23 ∷ []) (sym (low₁-comm (S) ((Swap ↑)))) ▸
       at 6 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b1 : Chain (K0 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ K0⁻ ∷ S0 ∷ K0 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ Sw23 ∷ Sw23 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ K0⁻ ∷ Sw12 ∷ []) (CK10 ∷ CCZ023 ∷ CK10⁻ ∷ CCZ023 ∷ [])
  b1 = at 7 6 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (lem-S3i) ▸
       at 11 2 (K0⁻ ∷ Sw23 ∷ []) (sym (low₁-comm ((K • iI)) ((Swap ↑)))) ▸
       at 12 2 (S0⁻ ∷ Sw23 ∷ []) (sym (low₁-comm ((S • S • S)) ((Swap ↑)))) ▸
       at 13 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 18 2 (Sw12 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) (Swap)) ▸
       at 17 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 14 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (win 0 3 complete₃ ((Swap ↑) • Swap • (Swap ↑)) (Swap • (Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 0 18 (CK10 ∷ CCZ023 ∷ CK10⁻ ∷ CCZ023 ∷ []) (sym lem-ROT-form) ▸ done

  b2 : Chain (CK10 ∷ CCZ023 ∷ CK10⁻ ∷ CCZ023 ∷ []) (CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ S1 ∷ CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ [])
  b2 = at 0 4 (CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ S1 ∷ CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ []) (sym lem-ROT≡cF) ▸ done

