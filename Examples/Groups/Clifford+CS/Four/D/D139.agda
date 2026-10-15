{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D139 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Tools using (ax)
open import Examples.Groups.Clifford+CS.Canonical using (can-≈)
open import Examples.Groups.Clifford+CS.Windows using (win)
open import Examples.Groups.Clifford+CS.Completeness using (complete₃)
open import Examples.Groups.Clifford+CS.TopWeakening using (low-comm)
open import Examples.Groups.Clifford+CS.Idle using (low₁-comm)
open import Examples.Groups.Clifford+CS.Four.Chain
open import Examples.Groups.Clifford+CS.Four.D.D022 using (lem-pass-CCZ012-vs-CS03)
open import Examples.Groups.Clifford+CS.Four.D.D126 using (lem-pass-CS23-vs-CS03 ; lem-pass-CS23-vs-Sd0)
open import Examples.Groups.Clifford+CS.Four.D.D138 using (lem-pass-CS23-vs-Sd3 ; lem-pass-Sd0-vs-CSd23 ; lem-pass-TOFF201-vs-iI)
-- pass [Sd0] [CS23 TOFF201 CSd23 TOFF201]: 4 steps
lem-pass-Sd0-vs-CS23-TOFF201-CSd23-TOFF201 : ⟪ (S0⁻ ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S0⁻ ∷ []) ⟫ʷ
lem-pass-Sd0-vs-CS23-TOFF201-CSd23-TOFF201 = run b0
  where
  b0 : Chain (S0⁻ ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S0⁻ ∷ [])
  b0 = at 0 2 (CS23 ∷ S0⁻ ∷ []) (sym lem-pass-CS23-vs-Sd0) ▸
       at 1 2 (Toff201 ∷ S0⁻ ∷ []) (win 3 0 complete₃ ((S • S • S) • Toffᵗ) (Toffᵗ • (S • S • S)) tt tt Eq.refl) ▸
       at 2 2 (CS23⁻ ∷ S0⁻ ∷ []) (lem-pass-Sd0-vs-CSd23) ▸
       at 3 2 (Toff201 ∷ S0⁻ ∷ []) (win 3 0 complete₃ ((S • S • S) • Toffᵗ) (Toffᵗ • (S • S • S)) tt tt Eq.refl) ▸ done


-- pass [CS23 TOFF201 CSd23 TOFF201] [Sd0]: 1 steps
lem-pass-CS23-TOFF201-CSd23-TOFF201-vs-Sd0 : ⟪ (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) ⟫ʷ
lem-pass-CS23-TOFF201-CSd23-TOFF201-vs-Sd0 = run b0
  where
  b0 : Chain (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S0⁻ ∷ []) (S0⁻ ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ [])
  b0 = at 0 5 (S0⁻ ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) (sym lem-pass-Sd0-vs-CS23-TOFF201-CSd23-TOFF201) ▸ done


-- pass [Sd3] [CSd23]: 1 steps
lem-pass-Sd3-vs-CSd23 : ⟪ (S3⁻ ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ S3⁻ ∷ []) ⟫ʷ
lem-pass-Sd3-vs-CSd23 = run b0
  where
  b0 : Chain (S3⁻ ∷ CS23⁻ ∷ []) (CS23⁻ ∷ S3⁻ ∷ [])
  b0 = at 0 2 (CS23⁻ ∷ S3⁻ ∷ []) (win 0 3 complete₃ (((S • S • S) ↑ ↑) • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • ((S • S • S) ↑ ↑)) tt tt Eq.refl) ▸ done


-- pass [Sd3] [CS23 TOFF201 CSd23 TOFF201]: 4 steps
lem-pass-Sd3-vs-CS23-TOFF201-CSd23-TOFF201 : ⟪ (S3⁻ ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S3⁻ ∷ []) ⟫ʷ
lem-pass-Sd3-vs-CS23-TOFF201-CSd23-TOFF201 = run b0
  where
  b0 : Chain (S3⁻ ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S3⁻ ∷ [])
  b0 = at 0 2 (CS23 ∷ S3⁻ ∷ []) (sym lem-pass-CS23-vs-Sd3) ▸
       at 1 2 (Toff201 ∷ S3⁻ ∷ []) (sym (low₃-comm (Toffᵗ) ((S • S • S)))) ▸
       at 2 2 (CS23⁻ ∷ S3⁻ ∷ []) (lem-pass-Sd3-vs-CSd23) ▸
       at 3 2 (Toff201 ∷ S3⁻ ∷ []) (sym (low₃-comm (Toffᵗ) ((S • S • S)))) ▸ done


-- pass [CS23 TOFF201 CSd23 TOFF201] [Sd3]: 1 steps
lem-pass-CS23-TOFF201-CSd23-TOFF201-vs-Sd3 : ⟪ (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S3⁻ ∷ []) ⟫ʷ ≈ ⟪ (S3⁻ ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) ⟫ʷ
lem-pass-CS23-TOFF201-CSd23-TOFF201-vs-Sd3 = run b0
  where
  b0 : Chain (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S3⁻ ∷ []) (S3⁻ ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ [])
  b0 = at 0 5 (S3⁻ ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) (sym lem-pass-Sd3-vs-CS23-TOFF201-CSd23-TOFF201) ▸ done


-- pass [TOFF201] [CS03]: 33 steps
lem-pass-TOFF201-vs-CS03 : ⟪ (Toff201 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Toff201 ∷ []) ⟫ʷ
lem-pass-TOFF201-vs-CS03 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (run b4))))
  where
  b0 : Chain (Toff201 ∷ CS03 ∷ []) (K2 ∷ CCZ012 ∷ Sw01 ∷ K2⁻ ∷ CS13 ∷ Sw01 ∷ [])
  b0 = at 0 1 (K2 ∷ CCZ012 ∷ K2⁻ ∷ []) (win 3 0 complete₃ (Toffᵗ) ((K ↑ ↑) • CCZ • ((K • iI) ↑ ↑)) tt tt Eq.refl) ▸
       at 4 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 4 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 3 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw01 ∷ K2⁻ ∷ []) (sym (low-comm (Swap) ((K • iI)))) ▸ done

  b1 : Chain (K2 ∷ CCZ012 ∷ Sw01 ∷ K2⁻ ∷ CS13 ∷ Sw01 ∷ []) (K2 ∷ CCZ012 ∷ CS03 ∷ K2⁻ ∷ [])
  b1 = at 3 2 (CS13 ∷ K2⁻ ∷ []) (win 0 3 complete₃ (((K • iI) ↑) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • ((K • iI) ↑)) tt tt Eq.refl) ▸
       at 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 3 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 4 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 2 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (K2⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((K • iI))) ▸
       at 4 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done

  b2 : Chain (K2 ∷ CCZ012 ∷ CS03 ∷ K2⁻ ∷ []) (Sw01 ∷ K2 ∷ CS13 ∷ Sw01 ∷ CCZ012 ∷ K2⁻ ∷ [])
  b2 = at 1 2 (CS03 ∷ CCZ012 ∷ []) (lem-pass-CCZ012-vs-CS03) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 2 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 1 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 2 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw01 ∷ K2 ∷ []) (sym (low-comm (Swap) (K))) ▸ done

  b3 : Chain (Sw01 ∷ K2 ∷ CS13 ∷ Sw01 ∷ CCZ012 ∷ K2⁻ ∷ []) (CS03 ∷ K2 ∷ CCZ012 ∷ K2⁻ ∷ [])
  b3 = at 1 2 (CS13 ∷ K2 ∷ []) (win 0 3 complete₃ ((K ↑) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • (K ↑)) tt tt Eq.refl) ▸
       at 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 1 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 2 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 0 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 2 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done

  b4 : Chain (CS03 ∷ K2 ∷ CCZ012 ∷ K2⁻ ∷ []) (CS03 ∷ Toff201 ∷ [])
  b4 = at 1 3 (Toff201 ∷ []) (win 3 0 complete₃ ((K ↑ ↑) • CCZ • ((K • iI) ↑ ↑)) (Toffᵗ) tt tt Eq.refl) ▸ done


-- pass [CS03] [TOFF201]: 1 steps
lem-pass-CS03-vs-TOFF201 : ⟪ (CS03 ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CS03-vs-TOFF201 = run b0
  where
  b0 : Chain (CS03 ∷ Toff201 ∷ []) (Toff201 ∷ CS03 ∷ [])
  b0 = at 0 2 (Toff201 ∷ CS03 ∷ []) (sym lem-pass-TOFF201-vs-CS03) ▸ done


-- pass [CS03] [CSd23]: 15 steps
lem-pass-CS03-vs-CSd23 : ⟪ (CS03 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CS03-vs-CSd23 = trans (run b0) (run b1)
  where
  b0 : Chain (CS03 ∷ CS23⁻ ∷ []) (Sw01 ∷ CS23⁻ ∷ CS13 ∷ Sw01 ∷ [])
  b0 = at 2 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 1 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 1 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 0 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 1 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (CS23⁻ ∷ CS13 ∷ []) (win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸ done

  b1 : Chain (Sw01 ∷ CS23⁻ ∷ CS13 ∷ Sw01 ∷ []) (CS23⁻ ∷ CS03 ∷ [])
  b1 = at 0 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 2 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 3 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 1 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- pass [CS03] [CS23 TOFF201 CSd23 TOFF201]: 4 steps
lem-pass-CS03-vs-CS23-TOFF201-CSd23-TOFF201 : ⟪ (CS03 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CS03-vs-CS23-TOFF201-CSd23-TOFF201 = run b0
  where
  b0 : Chain (CS03 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ CS03 ∷ [])
  b0 = at 0 2 (CS23 ∷ CS03 ∷ []) (sym lem-pass-CS23-vs-CS03) ▸
       at 1 2 (Toff201 ∷ CS03 ∷ []) (lem-pass-CS03-vs-TOFF201) ▸
       at 2 2 (CS23⁻ ∷ CS03 ∷ []) (lem-pass-CS03-vs-CSd23) ▸
       at 3 2 (Toff201 ∷ CS03 ∷ []) (lem-pass-CS03-vs-TOFF201) ▸ done


-- pass [CS23 TOFF201 CSd23 TOFF201] [CS03]: 1 steps
lem-pass-CS23-TOFF201-CSd23-TOFF201-vs-CS03 : ⟪ (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) ⟫ʷ
lem-pass-CS23-TOFF201-CSd23-TOFF201-vs-CS03 = run b0
  where
  b0 : Chain (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ CS03 ∷ []) (CS03 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ [])
  b0 = at 0 5 (CS03 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) (sym lem-pass-CS03-vs-CS23-TOFF201-CSd23-TOFF201) ▸ done


-- pass [CS23] [iI Sd0 Sd3 CS03]: 23 steps
lem-pass-CS23-vs-iI-Sd0-Sd3-CS03 : ⟪ (CS23 ∷ ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ CS23 ∷ []) ⟫ʷ
lem-pass-CS23-vs-iI-Sd0-Sd3-CS03 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS23 ∷ ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ []) (CS23 ∷ ι ∷ Sw01 ∷ S1⁻ ∷ S3⁻ ∷ CS13 ∷ Sw01 ∷ [])
  b0 = at 5 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 5 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 4 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 5 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw01 ∷ S3⁻ ∷ []) (sym (low-comm (Swap) (((S • S • S) ↑)))) ▸
       at 2 2 (Sw01 ∷ S1⁻ ∷ []) (win 3 0 complete₃ ((S • S • S) • Swap) (Swap • ((S • S • S) ↑)) tt tt Eq.refl) ▸ done

  b1 : Chain (CS23 ∷ ι ∷ Sw01 ∷ S1⁻ ∷ S3⁻ ∷ CS13 ∷ Sw01 ∷ []) (ι ∷ S0⁻ ∷ S3⁻ ∷ Sw01 ∷ CS13 ∷ CS23 ∷ Sw01 ∷ [])
  b1 = at 1 2 (Sw01 ∷ ι ∷ []) (win 3 0 complete₃ (iI • Swap) (Swap • iI) tt tt Eq.refl) ▸
       at 0 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 2 1 (ι3 ∷ []) (trans (can-≈ (iI)) (sym (can-≈ ((iI ↑ ↑ ↑))))) ▸
       at 1 5 (ι3 ∷ S1⁻ ∷ S3⁻ ∷ CS13 ∷ CS23 ∷ []) (win 0 3 complete₃ ((CS ↑) • (iI ↑ ↑) • (S • S • S) • ((S • S • S) ↑ ↑) • (Swap ↑ • CS • Swap ↑)) ((iI ↑ ↑) • (S • S • S) • ((S • S • S) ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (CS ↑)) tt tt Eq.refl) ▸
       at 1 1 (ι ∷ []) (trans (can-≈ ((iI ↑ ↑ ↑))) (sym (can-≈ (iI)))) ▸
       at 0 2 (ι ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • iI) (iI • Swap) tt tt Eq.refl) ▸
       at 1 2 (S0⁻ ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • ((S • S • S) ↑)) ((S • S • S) • Swap) tt tt Eq.refl) ▸
       at 2 2 (S3⁻ ∷ Sw01 ∷ []) (low-comm (Swap) (((S • S • S) ↑))) ▸ done

  b2 : Chain (ι ∷ S0⁻ ∷ S3⁻ ∷ Sw01 ∷ CS13 ∷ CS23 ∷ Sw01 ∷ []) (ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ CS23 ∷ [])
  b2 = at 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 4 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 3 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 5 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- pass [TOFF201] [Sd0]: 1 steps
lem-pass-TOFF201-vs-Sd0 : ⟪ (Toff201 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ Toff201 ∷ []) ⟫ʷ
lem-pass-TOFF201-vs-Sd0 = run b0
  where
  b0 : Chain (Toff201 ∷ S0⁻ ∷ []) (S0⁻ ∷ Toff201 ∷ [])
  b0 = at 0 2 (S0⁻ ∷ Toff201 ∷ []) (win 3 0 complete₃ (Toffᵗ • (S • S • S)) ((S • S • S) • Toffᵗ) tt tt Eq.refl) ▸ done


-- pass [TOFF201] [Sd3]: 1 steps
lem-pass-TOFF201-vs-Sd3 : ⟪ (Toff201 ∷ S3⁻ ∷ []) ⟫ʷ ≈ ⟪ (S3⁻ ∷ Toff201 ∷ []) ⟫ʷ
lem-pass-TOFF201-vs-Sd3 = run b0
  where
  b0 : Chain (Toff201 ∷ S3⁻ ∷ []) (S3⁻ ∷ Toff201 ∷ [])
  b0 = at 0 2 (S3⁻ ∷ Toff201 ∷ []) (low₃-comm (Toffᵗ) ((S • S • S))) ▸ done


-- pass [TOFF201] [iI Sd0 Sd3 CS03]: 4 steps
lem-pass-TOFF201-vs-iI-Sd0-Sd3-CS03 : ⟪ (Toff201 ∷ ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ Toff201 ∷ []) ⟫ʷ
lem-pass-TOFF201-vs-iI-Sd0-Sd3-CS03 = run b0
  where
  b0 : Chain (Toff201 ∷ ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ []) (ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ Toff201 ∷ [])
  b0 = at 0 2 (ι ∷ Toff201 ∷ []) (lem-pass-TOFF201-vs-iI) ▸
       at 1 2 (S0⁻ ∷ Toff201 ∷ []) (lem-pass-TOFF201-vs-Sd0) ▸
       at 2 2 (S3⁻ ∷ Toff201 ∷ []) (lem-pass-TOFF201-vs-Sd3) ▸
       at 3 2 (CS03 ∷ Toff201 ∷ []) (lem-pass-TOFF201-vs-CS03) ▸ done


-- pass [CSd23] [iI Sd0 Sd3 CS03]: 23 steps
lem-pass-CSd23-vs-iI-Sd0-Sd3-CS03 : ⟪ (CS23⁻ ∷ ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ CS23⁻ ∷ []) ⟫ʷ
lem-pass-CSd23-vs-iI-Sd0-Sd3-CS03 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS23⁻ ∷ ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ []) (CS23⁻ ∷ ι ∷ Sw01 ∷ S1⁻ ∷ S3⁻ ∷ CS13 ∷ Sw01 ∷ [])
  b0 = at 5 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 5 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 4 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 5 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw01 ∷ S3⁻ ∷ []) (sym (low-comm (Swap) (((S • S • S) ↑)))) ▸
       at 2 2 (Sw01 ∷ S1⁻ ∷ []) (win 3 0 complete₃ ((S • S • S) • Swap) (Swap • ((S • S • S) ↑)) tt tt Eq.refl) ▸ done

  b1 : Chain (CS23⁻ ∷ ι ∷ Sw01 ∷ S1⁻ ∷ S3⁻ ∷ CS13 ∷ Sw01 ∷ []) (ι ∷ S0⁻ ∷ S3⁻ ∷ Sw01 ∷ CS13 ∷ CS23⁻ ∷ Sw01 ∷ [])
  b1 = at 1 2 (Sw01 ∷ ι ∷ []) (win 3 0 complete₃ (iI • Swap) (Swap • iI) tt tt Eq.refl) ▸
       at 0 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 2 1 (ι3 ∷ []) (trans (can-≈ (iI)) (sym (can-≈ ((iI ↑ ↑ ↑))))) ▸
       at 1 5 (ι3 ∷ S1⁻ ∷ S3⁻ ∷ CS13 ∷ CS23⁻ ∷ []) (win 0 3 complete₃ (((CS • CS • CS) ↑) • (iI ↑ ↑) • (S • S • S) • ((S • S • S) ↑ ↑) • (Swap ↑ • CS • Swap ↑)) ((iI ↑ ↑) • (S • S • S) • ((S • S • S) ↑ ↑) • (Swap ↑ • CS • Swap ↑) • ((CS • CS • CS) ↑)) tt tt Eq.refl) ▸
       at 1 1 (ι ∷ []) (trans (can-≈ ((iI ↑ ↑ ↑))) (sym (can-≈ (iI)))) ▸
       at 0 2 (ι ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • iI) (iI • Swap) tt tt Eq.refl) ▸
       at 1 2 (S0⁻ ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • ((S • S • S) ↑)) ((S • S • S) • Swap) tt tt Eq.refl) ▸
       at 2 2 (S3⁻ ∷ Sw01 ∷ []) (low-comm (Swap) (((S • S • S) ↑))) ▸ done

  b2 : Chain (ι ∷ S0⁻ ∷ S3⁻ ∷ Sw01 ∷ CS13 ∷ CS23⁻ ∷ Sw01 ∷ []) (ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ CS23⁻ ∷ [])
  b2 = at 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 4 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 3 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 5 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- pass [CS23 TOFF201 CSd23 TOFF201] [iI Sd0 Sd3 CS03]: 4 steps
lem-pass-CS23-TOFF201-CSd23-TOFF201-vs-iI-Sd0-Sd3-CS03 : ⟪ (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) ⟫ʷ
lem-pass-CS23-TOFF201-CSd23-TOFF201-vs-iI-Sd0-Sd3-CS03 = run b0
  where
  b0 : Chain (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ []) (ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ [])
  b0 = at 3 5 (ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ Toff201 ∷ []) (lem-pass-TOFF201-vs-iI-Sd0-Sd3-CS03) ▸
       at 2 5 (ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ CS23⁻ ∷ []) (lem-pass-CSd23-vs-iI-Sd0-Sd3-CS03) ▸
       at 1 5 (ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ Toff201 ∷ []) (lem-pass-TOFF201-vs-iI-Sd0-Sd3-CS03) ▸
       at 0 5 (ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ CS23 ∷ []) (lem-pass-CS23-vs-iI-Sd0-Sd3-CS03) ▸ done

