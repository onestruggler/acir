{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D165 where

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
open import Examples.Groups.Clifford+CS.Four.D.D041 using (lem-ROT-gad)
open import Examples.Groups.Clifford+CS.Four.D.D148 using (lem-S2-at1023-ᵖ-1)
open import Examples.Groups.Clifford+CS.Four.D.D164 using (lem-S2-at2103-ᵖ-1)
-- resp S2 K2 CS02 TOFF213 CSd02 TOFF213 Kd2 Sd2: 1 steps
lem-resp-S2-K2-CS02-TOFF213-CSd02-TOFF213-Kd2-Sd2 : ⟪ (S2 ∷ K2 ∷ CS02 ∷ Toff213 ∷ CS02⁻ ∷ Toff213 ∷ K2⁻ ∷ S2⁻ ∷ []) ⟫ʷ ≈ ⟪ (S2 ∷ K2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ K2⁻ ∷ S2⁻ ∷ []) ⟫ʷ
lem-resp-S2-K2-CS02-TOFF213-CSd02-TOFF213-Kd2-Sd2 = run b0
  where
  b0 : Chain (S2 ∷ K2 ∷ CS02 ∷ Toff213 ∷ CS02⁻ ∷ Toff213 ∷ K2⁻ ∷ S2⁻ ∷ []) (S2 ∷ K2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ K2⁻ ∷ S2⁻ ∷ [])
  b0 = at 2 4 (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) (sym lem-S2-at2103-ᵖ-1) ▸ done


-- resp S1 K1 CS12 TOFF103 CSd12 TOFF103 Kd1 Sd1: 1 steps
lem-resp-S1-K1-CS12-TOFF103-CSd12-TOFF103-Kd1-Sd1 : ⟪ (S1 ∷ K1 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff103 ∷ K1⁻ ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ []) ⟫ʷ
lem-resp-S1-K1-CS12-TOFF103-CSd12-TOFF103-Kd1-Sd1 = run b0
  where
  b0 : Chain (S1 ∷ K1 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff103 ∷ K1⁻ ∷ S1⁻ ∷ []) (S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ [])
  b0 = at 2 4 (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (sym lem-S2-at1023-ᵖ-1) ▸ done


-- bridge G-rot: 139 steps
lem-bridge-G-rot : ⟪ (CK10 ∷ Sw01 ∷ CCZ012 ∷ Toff012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CZ23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Toff012 ∷ CCZ012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CZ23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ S1 ∷ CK10 ∷ Sw01 ∷ CCZ012 ∷ Toff012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CZ23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Toff012 ∷ CCZ012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CZ23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ
lem-bridge-G-rot = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (run b17)))))))))))))))))
  where
  b0 : Chain (CK10 ∷ Sw01 ∷ CCZ012 ∷ Toff012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CZ23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Toff012 ∷ CCZ012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CZ23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ S1 ∷ CK10 ∷ Sw01 ∷ CCZ012 ∷ Toff012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CZ23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Toff012 ∷ CCZ012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CZ23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ []) (CK10 ∷ Sw01 ∷ CCZ012 ∷ Toff012 ∷ Sw23 ∷ CZ02 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Toff012 ∷ CCZ012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CZ23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ S1 ∷ CK10 ∷ Sw01 ∷ CCZ012 ∷ Toff012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CZ23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Toff012 ∷ CCZ012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CZ23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ [])
  b0 = at 6 2 (CZ23 ∷ Sw01 ∷ []) (low-comm (Swap) (CZ)) ▸
       at 7 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 5 2 (CZ13 ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (CZ ↑)) ((Swap ↑ • CZ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 6 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 5 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 2 (CZ02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CZ ↑)) ((Swap ↑ • CZ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b1 : Chain (CK10 ∷ Sw01 ∷ CCZ012 ∷ Toff012 ∷ Sw23 ∷ CZ02 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Toff012 ∷ CCZ012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CZ23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ S1 ∷ CK10 ∷ Sw01 ∷ CCZ012 ∷ Toff012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CZ23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Toff012 ∷ CCZ012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CZ23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ []) (CK10 ∷ Sw01 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ Sw23 ∷ Sw01 ∷ CZ12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ S1 ∷ CK10 ∷ Sw01 ∷ CCZ012 ∷ Toff012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CZ23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Toff012 ∷ CCZ012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CZ23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ [])
  b1 = at 4 3 (CZ03 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 9 2 (CZ23 ∷ Sw01 ∷ []) (low-comm (Swap) (CZ)) ▸
       at 10 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 8 2 (CZ13 ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (CZ ↑)) ((Swap ↑ • CZ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 9 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 8 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b2 : Chain (CK10 ∷ Sw01 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ Sw23 ∷ Sw01 ∷ CZ12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ S1 ∷ CK10 ∷ Sw01 ∷ CCZ012 ∷ Toff012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CZ23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Toff012 ∷ CCZ012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CZ23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ []) (CK10 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ Sw01 ∷ CX01 ∷ CS02 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ Sw01 ∷ S1 ∷ CK10 ∷ Sw01 ∷ CCZ012 ∷ Toff012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CZ23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Toff012 ∷ CCZ012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CZ23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ [])
  b2 = at 8 2 (CZ02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CZ ↑)) ((Swap ↑ • CZ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 3 (CZ03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 2 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 2 2 (CX10 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • CX₀₁) (CX₁₀ • Swap) tt tt Eq.refl) ▸
       at 3 2 (CS02⁻ ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • ((CS • CS • CS) ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) tt tt Eq.refl) ▸ done

  b3 : Chain (CK10 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ Sw01 ∷ CX01 ∷ CS02 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ Sw01 ∷ S1 ∷ CK10 ∷ Sw01 ∷ CCZ012 ∷ Toff012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CZ23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Toff012 ∷ CCZ012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CZ23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ []) (CK10 ∷ CCZ012 ∷ K1 ∷ CS02 ∷ CX10 ∷ Sw01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ Sw01 ∷ S1 ∷ CK10 ∷ Sw01 ∷ CCZ012 ∷ Toff012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CZ23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Toff012 ∷ CCZ012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CZ23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ [])
  b3 = at 4 2 (CX10 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • CX₀₁) (CX₁₀ • Swap) tt tt Eq.refl) ▸
       at 5 2 (CS12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • Swap) tt tt Eq.refl) ▸
       at 1 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • CX₁₀ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • CX₁₀ • (CS ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 1 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (K1 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • K) ((K ↑) • Swap) tt tt Eq.refl) ▸
       at 3 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 4 2 (CX10 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • CX₀₁) (CX₁₀ • Swap) tt tt Eq.refl) ▸ done

  b4 : Chain (CK10 ∷ CCZ012 ∷ K1 ∷ CS02 ∷ CX10 ∷ Sw01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ Sw01 ∷ S1 ∷ CK10 ∷ Sw01 ∷ CCZ012 ∷ Toff012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CZ23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Toff012 ∷ CCZ012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CZ23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ []) (CK10 ∷ CCZ012 ∷ Toff102 ∷ Sw01 ∷ Sw23 ∷ CZ02 ∷ Sw23 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ Sw01 ∷ S1 ∷ CK10 ∷ Sw01 ∷ CCZ012 ∷ Toff012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CZ23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Toff012 ∷ CCZ012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CZ23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ [])
  b4 = at 5 2 (CS02⁻ ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • ((CS • CS • CS) ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 6 2 (CX10 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • CX₀₁) (CX₁₀ • Swap) tt tt Eq.refl) ▸
       at 7 2 (CS12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • Swap) tt tt Eq.refl) ▸
       at 8 2 (K1 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • K) ((K ↑) • Swap) tt tt Eq.refl) ▸
       at 9 2 (ι1 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • iI) ((iI ↑) • Swap) tt tt Eq.refl) ▸
       at 2 8 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (win 3 0 complete₃ ((K ↑) • (Swap ↑ • CS • Swap ↑) • CX₁₀ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • CX₁₀ • (CS ↑) • (K ↑) • (iI ↑)) ((K ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑) • iI) tt tt Eq.refl) ▸
       at 2 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (Sw23 ∷ CZ02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b5 : Chain (CK10 ∷ CCZ012 ∷ Toff102 ∷ Sw01 ∷ Sw23 ∷ CZ02 ∷ Sw23 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ Sw01 ∷ S1 ∷ CK10 ∷ Sw01 ∷ CCZ012 ∷ Toff012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CZ23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Toff012 ∷ CCZ012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CZ23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ []) (CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ K1 ∷ CS02 ∷ CX10 ∷ Sw01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ CCZ012 ∷ CZ03 ∷ Sw01 ∷ S1 ∷ CK10 ∷ Sw01 ∷ CCZ012 ∷ Toff012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CZ23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Toff012 ∷ CCZ012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CZ23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ [])
  b5 = at 3 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 4 2 (CZ12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CZ • Swap ↑)) ((CZ ↑) • Swap) tt tt Eq.refl) ▸
       at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 3 3 (CZ13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (K1 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • K) ((K ↑) • Swap) tt tt Eq.refl) ▸
       at 5 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 6 2 (CX10 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • CX₀₁) (CX₁₀ • Swap) tt tt Eq.refl) ▸ done

  b6 : Chain (CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ K1 ∷ CS02 ∷ CX10 ∷ Sw01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ CCZ012 ∷ CZ03 ∷ Sw01 ∷ S1 ∷ CK10 ∷ Sw01 ∷ CCZ012 ∷ Toff012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CZ23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Toff012 ∷ CCZ012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CZ23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ []) (CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ CZ03 ∷ Sw01 ∷ S1 ∷ CK10 ∷ Sw01 ∷ CCZ012 ∷ Toff012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CZ23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Toff012 ∷ CCZ012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CZ23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ [])
  b6 = at 7 2 (CS02⁻ ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • ((CS • CS • CS) ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 8 2 (CX10 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • CX₀₁) (CX₁₀ • Swap) tt tt Eq.refl) ▸
       at 9 2 (CS12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • Swap) tt tt Eq.refl) ▸
       at 10 2 (K1 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • K) ((K ↑) • Swap) tt tt Eq.refl) ▸
       at 11 2 (ι1 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • iI) ((iI ↑) • Swap) tt tt Eq.refl) ▸
       at 4 8 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (win 3 0 complete₃ ((K ↑) • (Swap ↑ • CS • Swap ↑) • CX₁₀ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • CX₁₀ • (CS ↑) • (K ↑) • (iI ↑)) ((K ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑) • iI) tt tt Eq.refl) ▸
       at 4 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸ done

  b7 : Chain (CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ CZ03 ∷ Sw01 ∷ S1 ∷ CK10 ∷ Sw01 ∷ CCZ012 ∷ Toff012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CZ23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Toff012 ∷ CCZ012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CZ23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ []) (CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ Sw01 ∷ Sw23 ∷ CZ02 ∷ Sw23 ∷ Sw01 ∷ S1 ∷ CK10 ∷ Sw01 ∷ CCZ012 ∷ Toff012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CZ23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Toff012 ∷ CCZ012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CZ23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ [])
  b7 = at 5 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 6 2 (CX10 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • CX₀₁) (CX₁₀ • Swap) tt tt Eq.refl) ▸
       at 7 2 (CS02⁻ ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • ((CS • CS • CS) ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 8 2 (CX10 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • CX₀₁) (CX₁₀ • Swap) tt tt Eq.refl) ▸
       at 9 2 (CS12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • Swap) tt tt Eq.refl) ▸
       at 5 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • CX₁₀ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • CX₁₀ • (CS ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 5 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (Sw23 ∷ CZ02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b8 : Chain (CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ Sw01 ∷ Sw23 ∷ CZ02 ∷ Sw23 ∷ Sw01 ∷ S1 ∷ CK10 ∷ Sw01 ∷ CCZ012 ∷ Toff012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CZ23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Toff012 ∷ CCZ012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CZ23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ []) (CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ S1 ∷ CK10 ∷ Sw01 ∷ CCZ012 ∷ Toff012 ∷ Sw01 ∷ CZ13 ∷ Sw12 ∷ Sw12 ∷ Sw01 ∷ Toff012 ∷ CCZ012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CZ23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ [])
  b8 = at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 2 (CZ12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CZ • Swap ↑)) ((CZ ↑) • Swap) tt tt Eq.refl) ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 3 (CZ13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 14 2 (CZ23 ∷ Sw01 ∷ []) (low-comm (Swap) (CZ)) ▸
       at 15 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 13 2 (CZ13 ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (CZ ↑)) ((Swap ↑ • CZ • Swap ↑) • Swap) tt tt Eq.refl) ▸ done

  b9 : Chain (CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ S1 ∷ CK10 ∷ Sw01 ∷ CCZ012 ∷ Toff012 ∷ Sw01 ∷ CZ13 ∷ Sw12 ∷ Sw12 ∷ Sw01 ∷ Toff012 ∷ CCZ012 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ CZ23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ []) (CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ S1 ∷ CK10 ∷ Sw01 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ Sw01 ∷ Sw12 ∷ CZ23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ [])
  b9 = at 14 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 13 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 13 2 (CZ02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CZ ↑)) ((Swap ↑ • CZ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 14 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 12 3 (CZ03 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 17 2 (CZ23 ∷ Sw01 ∷ []) (low-comm (Swap) (CZ)) ▸ done

  b10 : Chain (CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ S1 ∷ CK10 ∷ Sw01 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ Sw01 ∷ Sw12 ∷ CZ23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ []) (CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ S1 ∷ CK10 ∷ Sw01 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ [])
  b10 = at 18 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 16 2 (CZ13 ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (CZ ↑)) ((Swap ↑ • CZ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 17 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 16 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 15 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 16 2 (CZ02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CZ ↑)) ((Swap ↑ • CZ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 17 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 15 3 (CZ03 ∷ []) (by-assoc Eq.refl) ▸ done

  b11 : Chain (CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ S1 ∷ CK10 ∷ Sw01 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ []) (CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ S1 ∷ CK10 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw01 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ Sw01 ∷ [])
  b11 = at 16 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 10 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 10 2 (CX10 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • CX₀₁) (CX₁₀ • Swap) tt tt Eq.refl) ▸
       at 11 2 (CS02⁻ ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • ((CS • CS • CS) ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 12 2 (CX10 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • CX₀₁) (CX₁₀ • Swap) tt tt Eq.refl) ▸
       at 13 2 (CS12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • Swap) tt tt Eq.refl) ▸
       at 9 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • CX₁₀ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • CX₁₀ • (CS ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸ done

  b12 : Chain (CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ S1 ∷ CK10 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw01 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ Sw01 ∷ []) (CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ S1 ∷ CK10 ∷ CCZ012 ∷ K1 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ Sw01 ∷ K0 ∷ ι ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ Sw01 ∷ [])
  b12 = at 9 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 11 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (K1 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • K) ((K ↑) • Swap) tt tt Eq.refl) ▸
       at 11 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 12 2 (CX10 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • CX₀₁) (CX₁₀ • Swap) tt tt Eq.refl) ▸
       at 13 2 (CS02⁻ ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • ((CS • CS • CS) ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 14 2 (CX10 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • CX₀₁) (CX₁₀ • Swap) tt tt Eq.refl) ▸
       at 15 2 (CS12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • Swap) tt tt Eq.refl) ▸ done

  b13 : Chain (CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ S1 ∷ CK10 ∷ CCZ012 ∷ K1 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ Sw01 ∷ K0 ∷ ι ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ Sw01 ∷ []) (CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ S1 ∷ CK10 ∷ CCZ012 ∷ Toff102 ∷ Sw23 ∷ CZ12 ∷ Sw23 ∷ Sw01 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ Sw01 ∷ [])
  b13 = at 16 2 (K1 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • K) ((K ↑) • Swap) tt tt Eq.refl) ▸
       at 17 2 (ι1 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • iI) ((iI ↑) • Swap) tt tt Eq.refl) ▸
       at 10 8 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (win 3 0 complete₃ ((K ↑) • (Swap ↑ • CS • Swap ↑) • CX₁₀ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • CX₁₀ • (CS ↑) • (K ↑) • (iI ↑)) ((K ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑) • iI) tt tt Eq.refl) ▸
       at 10 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸
       at 12 1 (Sw23 ∷ CZ02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 12 2 (CZ12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CZ • Swap ↑)) ((CZ ↑) • Swap) tt tt Eq.refl) ▸
       at 13 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b14 : Chain (CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ S1 ∷ CK10 ∷ CCZ012 ∷ Toff102 ∷ Sw23 ∷ CZ12 ∷ Sw23 ∷ Sw01 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ Sw01 ∷ []) (CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ S1 ∷ CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ K1 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ Sw01 ∷ K0 ∷ ι ∷ CCZ012 ∷ CZ03 ∷ Sw01 ∷ [])
  b14 = at 11 3 (CZ13 ∷ []) (by-assoc Eq.refl) ▸
       at 13 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (K1 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • K) ((K ↑) • Swap) tt tt Eq.refl) ▸
       at 13 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 14 2 (CX10 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • CX₀₁) (CX₁₀ • Swap) tt tt Eq.refl) ▸
       at 15 2 (CS02⁻ ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • ((CS • CS • CS) ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 16 2 (CX10 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • CX₀₁) (CX₁₀ • Swap) tt tt Eq.refl) ▸
       at 17 2 (CS12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • Swap) tt tt Eq.refl) ▸ done

  b15 : Chain (CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ S1 ∷ CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ K1 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ Sw01 ∷ K0 ∷ ι ∷ CCZ012 ∷ CZ03 ∷ Sw01 ∷ []) (CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ S1 ∷ CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ Sw01 ∷ CX01 ∷ CS02 ∷ CZ03 ∷ Sw01 ∷ [])
  b15 = at 18 2 (K1 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • K) ((K ↑) • Swap) tt tt Eq.refl) ▸
       at 19 2 (ι1 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • iI) ((iI ↑) • Swap) tt tt Eq.refl) ▸
       at 12 8 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (win 3 0 complete₃ ((K ↑) • (Swap ↑ • CS • Swap ↑) • CX₁₀ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • CX₁₀ • (CS ↑) • (K ↑) • (iI ↑)) ((K ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑) • iI) tt tt Eq.refl) ▸
       at 12 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸
       at 14 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 14 2 (CX10 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • CX₀₁) (CX₁₀ • Swap) tt tt Eq.refl) ▸
       at 15 2 (CS02⁻ ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • ((CS • CS • CS) ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) tt tt Eq.refl) ▸ done

  b16 : Chain (CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ S1 ∷ CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ Sw01 ∷ CX01 ∷ CS02 ∷ CZ03 ∷ Sw01 ∷ []) (CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ S1 ∷ CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ Sw23 ∷ CZ12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ [])
  b16 = at 16 2 (CX10 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • CX₀₁) (CX₁₀ • Swap) tt tt Eq.refl) ▸
       at 17 2 (CS12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • Swap) tt tt Eq.refl) ▸
       at 13 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • CX₁₀ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • CX₁₀ • (CS ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 13 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 15 1 (Sw23 ∷ CZ02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 15 2 (CZ12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CZ • Swap ↑)) ((CZ ↑) • Swap) tt tt Eq.refl) ▸
       at 16 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b17 : Chain (CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ S1 ∷ CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ Sw23 ∷ CZ12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ []) (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ [])
  b17 = at 14 3 (CZ13 ∷ []) (by-assoc Eq.refl) ▸
       at 15 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 0 15 (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (lem-ROT-gad) ▸ done

