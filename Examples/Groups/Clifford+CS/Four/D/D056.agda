{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D056 where

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
open import Examples.Groups.Clifford+CS.Four.D.D054 using (lem-PPi2≡E)
open import Examples.Groups.Clifford+CS.Four.D.D055 using (lem-ROT-form)
open import Examples.Groups.Clifford+CS.Four.D.D046 using (lem-ROT≡cF)

-- ROT2=E: 17 steps (scratchpad/four/lower.py)
lem-ROT2≡E : ⟪ (CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ S1 ∷ CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ S1 ∷ CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ []) ⟫ʷ
lem-ROT2≡E = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ S1 ∷ CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ S1 ∷ CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ []) (K0 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ K0⁻ ∷ S0 ∷ K0 ∷ CCZ123 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ K0⁻ ∷ [])
  b0 = at 0 15 (CK10 ∷ CCZ023 ∷ CK10⁻ ∷ CCZ023 ∷ []) (lem-ROT≡cF) ▸
       at 4 15 (CK10 ∷ CCZ023 ∷ CK10⁻ ∷ CCZ023 ∷ []) (lem-ROT≡cF) ▸
       at 0 4 (K0 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ K0⁻ ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ K0⁻ ∷ []) (lem-ROT-form) ▸
       at 18 4 (K0 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ K0⁻ ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ K0⁻ ∷ []) (lem-ROT-form) ▸
       at 17 2 [] (win 3 0 complete₃ ((K • iI) • K) (ε) tt tt Eq.refl) ▸
       at 14 6 [] (win 0 3 complete₃ (Swap • (Swap ↑) • Swap • Swap • (Swap ↑) • Swap) (ε) tt tt Eq.refl) ▸
       at 11 6 [] (win 3 0 complete₃ ((K • iI) • (S • S • S) • K • (K • iI) • S • K) (ε) tt tt Eq.refl) ▸
       at 7 8 (CCZ123 ∷ []) (lem-PPi2≡E) ▸ done

  b1 : Chain (K0 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ K0⁻ ∷ S0 ∷ K0 ∷ CCZ123 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ K0⁻ ∷ []) (CCZ123 ∷ K0 ∷ K0⁻ ∷ [])
  b1 = at 7 2 (K0⁻ ∷ CCZ123 ∷ []) (sym (low₁-comm ((K • iI)) (CCZ))) ▸
       at 8 2 (S0⁻ ∷ CCZ123 ∷ []) (sym (low₁-comm ((S • S • S)) (CCZ))) ▸
       at 9 2 (K0 ∷ CCZ123 ∷ []) (sym (low₁-comm (K) (CCZ))) ▸
       at 4 6 [] (win 3 0 complete₃ ((K • iI) • S • K • (K • iI) • (S • S • S) • K) (ε) tt tt Eq.refl) ▸
       at 3 3 (CCZ123 ∷ []) (win 0 3 complete₃ (Swap • CCZ • Swap) (CCZ) tt tt Eq.refl) ▸
       at 2 3 (CCZ123 ∷ []) (win 0 3 complete₃ ((Swap ↑) • CCZ • (Swap ↑)) (CCZ) tt tt Eq.refl) ▸
       at 1 3 (CCZ123 ∷ []) (win 0 3 complete₃ (Swap • CCZ • Swap) (CCZ) tt tt Eq.refl) ▸
       at 0 2 (CCZ123 ∷ K0 ∷ []) (low₁-comm (K) (CCZ)) ▸ done

  b2 : Chain (CCZ123 ∷ K0 ∷ K0⁻ ∷ []) (CCZ123 ∷ [])
  b2 = at 1 2 [] (win 3 0 complete₃ (K • (K • iI)) (ε) tt tt Eq.refl) ▸ done

