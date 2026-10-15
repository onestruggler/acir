{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D160 where

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
open import Examples.Groups.Clifford+CS.Four.D.D030 using (lem-pass-CCZ012-vs-CSd03)
open import Examples.Groups.Clifford+CS.Four.D.D124 using (lem-ca-split-Gad⟨t≡2-W≡⟨3⟩-d≡SdKdSS-e≡-1⟩-3)
open import Examples.Groups.Clifford+CS.Four.D.D125 using (lem-pass-CS23-vs-CSd03 ; lem-pass-CS23-vs-S0)
open import Examples.Groups.Clifford+CS.Four.D.D132 using (lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X3-CS23-TOFF201-CSd23-TOFF201-X3)
open import Examples.Groups.Clifford+CS.Four.D.D138 using (lem-pass-X3-CKd32-X3-vs-CS03-TOFF012-CSd03-TOFF012 ; lem-pass-X3-CS32-X3-vs-CS03-TOFF012-CSd03-TOFF012 ; lem-pass-X3-CSd32-X3-vs-CS03-TOFF012-CSd03-TOFF012)
open import Examples.Groups.Clifford+CS.Four.D.D143 using (lem-pass-X3-CK32-X3-vs-CS03-TOFF012-CSd03-TOFF012)
open import Examples.Groups.Clifford+CS.Four.D.D144 using (lem-pass-X3-CSd30-X3-vs-CS23-TOFF201-CSd23-TOFF201)
open import Examples.Groups.Clifford+CS.Four.D.D145 using (lem-pass-X3-CKd30-X3-vs-CS23-TOFF201-CSd23-TOFF201)
open import Examples.Groups.Clifford+CS.Four.D.D159 using (lem-pass-S0-vs-CSd23)
-- pass [S0] [CS23 TOFF201 CSd23 TOFF201]: 4 steps
lem-pass-S0-vs-CS23-TOFF201-CSd23-TOFF201 : ⟪ (S0 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S0 ∷ []) ⟫ʷ
lem-pass-S0-vs-CS23-TOFF201-CSd23-TOFF201 = run b0
  where
  b0 : Chain (S0 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S0 ∷ [])
  b0 = at 0 2 (CS23 ∷ S0 ∷ []) (sym lem-pass-CS23-vs-S0) ▸
       at 1 2 (Toff201 ∷ S0 ∷ []) (win 3 0 complete₃ (S • Toffᵗ) (Toffᵗ • S) tt tt Eq.refl) ▸
       at 2 2 (CS23⁻ ∷ S0 ∷ []) (lem-pass-S0-vs-CSd23) ▸
       at 3 2 (Toff201 ∷ S0 ∷ []) (win 3 0 complete₃ (S • Toffᵗ) (Toffᵗ • S) tt tt Eq.refl) ▸ done


-- pass [CS23 TOFF201 CSd23 TOFF201] [S0]: 1 steps
lem-pass-CS23-TOFF201-CSd23-TOFF201-vs-S0 : ⟪ (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) ⟫ʷ
lem-pass-CS23-TOFF201-CSd23-TOFF201-vs-S0 = run b0
  where
  b0 : Chain (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S0 ∷ []) (S0 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ [])
  b0 = at 0 5 (S0 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) (sym lem-pass-S0-vs-CS23-TOFF201-CSd23-TOFF201) ▸ done


-- pass [TOFF201] [CSd03]: 33 steps
lem-pass-TOFF201-vs-CSd03 : ⟪ (Toff201 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ Toff201 ∷ []) ⟫ʷ
lem-pass-TOFF201-vs-CSd03 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (run b4))))
  where
  b0 : Chain (Toff201 ∷ CS03⁻ ∷ []) (K2 ∷ CCZ012 ∷ Sw01 ∷ K2⁻ ∷ CS13⁻ ∷ Sw01 ∷ [])
  b0 = at 0 1 (K2 ∷ CCZ012 ∷ K2⁻ ∷ []) (win 3 0 complete₃ (Toffᵗ) ((K ↑ ↑) • CCZ • ((K • iI) ↑ ↑)) tt tt Eq.refl) ▸
       at 4 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 3 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 4 2 (Sw01 ∷ CS12⁻ ∷ []) (win 3 0 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) (Swap • ((CS • CS • CS) ↑)) tt tt Eq.refl) ▸
       at 3 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 4 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw01 ∷ K2⁻ ∷ []) (sym (low-comm (Swap) ((K • iI)))) ▸ done

  b1 : Chain (K2 ∷ CCZ012 ∷ Sw01 ∷ K2⁻ ∷ CS13⁻ ∷ Sw01 ∷ []) (K2 ∷ CCZ012 ∷ CS03⁻ ∷ K2⁻ ∷ [])
  b1 = at 3 2 (CS13⁻ ∷ K2⁻ ∷ []) (win 0 3 complete₃ (((K • iI) ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • ((K • iI) ↑)) tt tt Eq.refl) ▸
       at 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 3 2 (CS02⁻ ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • ((CS • CS • CS) ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 4 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 2 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (K2⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((K • iI))) ▸
       at 4 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done

  b2 : Chain (K2 ∷ CCZ012 ∷ CS03⁻ ∷ K2⁻ ∷ []) (Sw01 ∷ K2 ∷ CS13⁻ ∷ Sw01 ∷ CCZ012 ∷ K2⁻ ∷ [])
  b2 = at 1 2 (CS03⁻ ∷ CCZ012 ∷ []) (lem-pass-CCZ012-vs-CSd03) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 1 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 2 2 (Sw01 ∷ CS12⁻ ∷ []) (win 3 0 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) (Swap • ((CS • CS • CS) ↑)) tt tt Eq.refl) ▸
       at 1 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 2 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw01 ∷ K2 ∷ []) (sym (low-comm (Swap) (K))) ▸ done

  b3 : Chain (Sw01 ∷ K2 ∷ CS13⁻ ∷ Sw01 ∷ CCZ012 ∷ K2⁻ ∷ []) (CS03⁻ ∷ K2 ∷ CCZ012 ∷ K2⁻ ∷ [])
  b3 = at 1 2 (CS13⁻ ∷ K2 ∷ []) (win 0 3 complete₃ ((K ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (K ↑)) tt tt Eq.refl) ▸
       at 1 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 1 2 (CS02⁻ ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • ((CS • CS • CS) ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 2 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 0 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 2 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done

  b4 : Chain (CS03⁻ ∷ K2 ∷ CCZ012 ∷ K2⁻ ∷ []) (CS03⁻ ∷ Toff201 ∷ [])
  b4 = at 1 3 (Toff201 ∷ []) (win 3 0 complete₃ ((K ↑ ↑) • CCZ • ((K • iI) ↑ ↑)) (Toffᵗ) tt tt Eq.refl) ▸ done


-- pass [CSd03] [TOFF201]: 1 steps
lem-pass-CSd03-vs-TOFF201 : ⟪ (CS03⁻ ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-pass-CSd03-vs-TOFF201 = run b0
  where
  b0 : Chain (CS03⁻ ∷ Toff201 ∷ []) (Toff201 ∷ CS03⁻ ∷ [])
  b0 = at 0 2 (Toff201 ∷ CS03⁻ ∷ []) (sym lem-pass-TOFF201-vs-CSd03) ▸ done


-- pass [CSd03] [CSd23]: 15 steps
lem-pass-CSd03-vs-CSd23 : ⟪ (CS03⁻ ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ CS03⁻ ∷ []) ⟫ʷ
lem-pass-CSd03-vs-CSd23 = trans (run b0) (run b1)
  where
  b0 : Chain (CS03⁻ ∷ CS23⁻ ∷ []) (Sw01 ∷ CS23⁻ ∷ CS13⁻ ∷ Sw01 ∷ [])
  b0 = at 2 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 1 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 0 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 1 2 (Sw01 ∷ CS12⁻ ∷ []) (win 3 0 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) (Swap • ((CS • CS • CS) ↑)) tt tt Eq.refl) ▸
       at 0 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 1 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (CS23⁻ ∷ CS13⁻ ∷ []) (win 0 3 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) tt tt Eq.refl) ▸ done

  b1 : Chain (Sw01 ∷ CS23⁻ ∷ CS13⁻ ∷ Sw01 ∷ []) (CS23⁻ ∷ CS03⁻ ∷ [])
  b1 = at 0 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 2 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 2 2 (CS02⁻ ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • ((CS • CS • CS) ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 3 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 1 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- pass [CSd03] [CS23 TOFF201 CSd23 TOFF201]: 4 steps
lem-pass-CSd03-vs-CS23-TOFF201-CSd23-TOFF201 : ⟪ (CS03⁻ ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-pass-CSd03-vs-CS23-TOFF201-CSd23-TOFF201 = run b0
  where
  b0 : Chain (CS03⁻ ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ CS03⁻ ∷ [])
  b0 = at 0 2 (CS23 ∷ CS03⁻ ∷ []) (sym lem-pass-CS23-vs-CSd03) ▸
       at 1 2 (Toff201 ∷ CS03⁻ ∷ []) (lem-pass-CSd03-vs-TOFF201) ▸
       at 2 2 (CS23⁻ ∷ CS03⁻ ∷ []) (lem-pass-CSd03-vs-CSd23) ▸
       at 3 2 (Toff201 ∷ CS03⁻ ∷ []) (lem-pass-CSd03-vs-TOFF201) ▸ done


-- pass [CS23 TOFF201 CSd23 TOFF201] [CSd03]: 1 steps
lem-pass-CS23-TOFF201-CSd23-TOFF201-vs-CSd03 : ⟪ (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) ⟫ʷ
lem-pass-CS23-TOFF201-CSd23-TOFF201-vs-CSd03 = run b0
  where
  b0 : Chain (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ [])
  b0 = at 0 5 (CS03⁻ ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) (sym lem-pass-CSd03-vs-CS23-TOFF201-CSd23-TOFF201) ▸ done


-- pass [S0 CSd03] [CS23 TOFF201 CSd23 TOFF201]: 8 steps
lem-pass-S0-CSd03-vs-CS23-TOFF201-CSd23-TOFF201 : ⟪ (S0 ∷ CS03⁻ ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S0 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-pass-S0-CSd03-vs-CS23-TOFF201-CSd23-TOFF201 = run b0
  where
  b0 : Chain (S0 ∷ CS03⁻ ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S0 ∷ CS03⁻ ∷ [])
  b0 = at 1 2 (CS23 ∷ CS03⁻ ∷ []) (sym lem-pass-CS23-vs-CSd03) ▸
       at 0 2 (CS23 ∷ S0 ∷ []) (sym lem-pass-CS23-vs-S0) ▸
       at 2 2 (Toff201 ∷ CS03⁻ ∷ []) (lem-pass-CSd03-vs-TOFF201) ▸
       at 1 2 (Toff201 ∷ S0 ∷ []) (win 3 0 complete₃ (S • Toffᵗ) (Toffᵗ • S) tt tt Eq.refl) ▸
       at 3 2 (CS23⁻ ∷ CS03⁻ ∷ []) (lem-pass-CSd03-vs-CSd23) ▸
       at 2 2 (CS23⁻ ∷ S0 ∷ []) (lem-pass-S0-vs-CSd23) ▸
       at 4 2 (Toff201 ∷ CS03⁻ ∷ []) (lem-pass-CSd03-vs-TOFF201) ▸
       at 3 2 (Toff201 ∷ S0 ∷ []) (win 3 0 complete₃ (S • Toffᵗ) (Toffᵗ • S) tt tt Eq.refl) ▸ done


-- pass [CS23 TOFF201 CSd23 TOFF201] [S0 CSd03]: 1 steps
lem-pass-CS23-TOFF201-CSd23-TOFF201-vs-S0-CSd03 : ⟪ (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S0 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ CS03⁻ ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) ⟫ʷ
lem-pass-CS23-TOFF201-CSd23-TOFF201-vs-S0-CSd03 = run b0
  where
  b0 : Chain (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S0 ∷ CS03⁻ ∷ []) (S0 ∷ CS03⁻ ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ [])
  b0 = at 0 6 (S0 ∷ CS03⁻ ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) (sym lem-pass-S0-CSd03-vs-CS23-TOFF201-CSd23-TOFF201) ▸ done


-- pass [X3 CS23 TOFF201 CSd23 TOFF201 X3] [CS03]: 31 steps
lem-pass-X3-CS23-TOFF201-CSd23-TOFF201-X3-vs-CS03 : ⟪ (X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS23-TOFF201-CSd23-TOFF201-X3-vs-CS03 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CS03 ∷ []) (X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S0 ∷ CS03⁻ ∷ Sw23 ∷ X2 ∷ Sw23 ∷ [])
  b0 = at 7 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 5 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 6 2 (S0 ∷ CS02⁻ ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑)) (S • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 5 2 (S0 ∷ Sw23 ∷ []) (sym (low₁-comm (S) ((Swap ↑)))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 6 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S0 ∷ CS03⁻ ∷ Sw23 ∷ X2 ∷ Sw23 ∷ []) (S0 ∷ Sw23 ∷ X2 ∷ CS02⁻ ∷ Sw23 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ [])
  b1 = at 7 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 8 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 6 (S0 ∷ CS03⁻ ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) (lem-pass-CS23-TOFF201-CSd23-TOFF201-vs-S0-CSd03) ▸
       at 0 2 (S0 ∷ X3 ∷ []) (sym (low₁-comm (S) ((X ↑ ↑)))) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸ done

  b2 : Chain (S0 ∷ Sw23 ∷ X2 ∷ CS02⁻ ∷ Sw23 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ []) (S0 ∷ S0⁻ ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ [])
  b2 = at 2 2 (S0⁻ ∷ CS02 ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((S • S • S) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 1 2 (S0⁻ ∷ Sw23 ∷ []) (sym (low₁-comm ((S • S • S)) ((Swap ↑)))) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 4 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b3 : Chain (S0 ∷ S0⁻ ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ []) (CS03 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ [])
  b3 = at 4 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 2 (Sw23 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((Swap ↑))) ▸
       at 0 2 (Sw23 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑))) ▸
       at 1 3 (CS02 ∷ []) (win 3 0 complete₃ (S • (S • S • S) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 0 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- pass [CS03] [X3 CS23 TOFF201 CSd23 TOFF201 X3]: 1 steps
lem-pass-CS03-vs-X3-CS23-TOFF201-CSd23-TOFF201-X3 : ⟪ (CS03 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CS03-vs-X3-CS23-TOFF201-CSd23-TOFF201-X3 = run b0
  where
  b0 : Chain (CS03 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ []) (X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CS03 ∷ [])
  b0 = at 0 7 (X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CS03 ∷ []) (sym lem-pass-X3-CS23-TOFF201-CSd23-TOFF201-X3-vs-CS03) ▸ done


-- pass [CS03 TOFF012 CSd03 TOFF012] [X3 CS23 TOFF201 CSd23 TOFF201 X3]: 33 steps
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X3-CS23-TOFF201-CSd23-TOFF201-X3 : ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X3-CS23-TOFF201-CSd23-TOFF201-X3 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (run b4))))
  where
  b0 : Chain (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ Toff012 ∷ CS03 ∷ CS03⁻ ∷ Toff012 ∷ [])
  b0 = at 10 0 (Toff012 ∷ Toff012 ∷ []) (win 3 0 complete₃ (ε) (Toff • Toff) tt tt Eq.refl) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 12 0 (CS02 ∷ CS02⁻ ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) tt tt Eq.refl) ▸
       at 13 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 11 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 14 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 12 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b1 : Chain (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ Toff012 ∷ CS03 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ [])
  b1 = at 12 0 (Toff012 ∷ Toff012 ∷ []) (win 3 0 complete₃ (ε) (Toff • Toff) tt tt Eq.refl) ▸
       at 13 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 14 0 (CS02⁻ ∷ CS02 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 15 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 13 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 16 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 14 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 15 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b2 : Chain (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ Sw23 ∷ Sw23 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ [])
  b2 = at 4 10 (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ []) (sym lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X3-CS23-TOFF201-CSd23-TOFF201-X3) ▸
       at 3 2 [] (win 3 0 complete₃ (Toff • Toff) (ε) tt tt Eq.refl) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 2 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 3 2 [] (win 3 0 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CS • Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b3 : Chain (CS03 ∷ Toff012 ∷ Sw23 ∷ Sw23 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (Sw23 ∷ Sw23 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ [])
  b3 = at 2 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ (Toff • Toff) (ε) tt tt Eq.refl) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b4 : Chain (Sw23 ∷ Sw23 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ [])
  b4 = at 0 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- pass [CS03 TOFF012 CSd03 TOFF012] [X3 Sd2 Kd2 S2 S2 CS23 TOFF201 CSd23 TOFF201 Sd2 Sd2 K2 S2 X3]: 11 steps
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X3 : ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X3 = trans (run b0) (run b1)
  where
  b0 : Chain (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X3 ∷ []) (X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CK32 ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ [])
  b0 = at 4 14 (X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CK32 ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ []) (lem-ca-split-Gad⟨t≡2-W≡⟨3⟩-d≡SdKdSS-e≡-1⟩-3) ▸
       at 0 7 (X3 ∷ CS23⁻ ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (sym lem-pass-X3-CSd32-X3-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 3 7 (X3 ∷ CK32⁻ ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (sym lem-pass-X3-CKd32-X3-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 6 7 (X3 ∷ CS23 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (sym lem-pass-X3-CS32-X3-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 9 7 (X3 ∷ CS23 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (sym lem-pass-X3-CS32-X3-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 12 10 (X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X3-CS23-TOFF201-CSd23-TOFF201-X3) ▸
       at 18 7 (X3 ∷ CS23⁻ ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (sym lem-pass-X3-CSd32-X3-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 21 7 (X3 ∷ CS23⁻ ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (sym lem-pass-X3-CSd32-X3-vs-CS03-TOFF012-CSd03-TOFF012) ▸ done

  b1 : Chain (X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CK32 ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ []) (X3 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ [])
  b1 = at 24 7 (X3 ∷ CK32 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (sym lem-pass-X3-CK32-X3-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 27 7 (X3 ∷ CS23 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (sym lem-pass-X3-CS32-X3-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 0 30 (X3 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X3 ∷ []) (sym lem-ca-split-Gad⟨t≡2-W≡⟨3⟩-d≡SdKdSS-e≡-1⟩-3) ▸ done


-- pass [X3 CSd30 X3] [Sd2 Kd2 S2 S2 CS23 TOFF201 CSd23 TOFF201 Sd2 Sd2 K2 S2]: 73 steps
lem-pass-X3-CSd30-X3-vs-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2 : ⟪ (X3 ∷ CS03⁻ ∷ X3 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ []) ⟫ʷ ≈ ⟪ (S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CSd30-X3-vs-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (run b9)))))))))
  where
  b0 : Chain (X3 ∷ CS03⁻ ∷ X3 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ []) (X3 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ Sw23 ∷ X2 ∷ Sw23 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ [])
  b0 = at 3 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 1 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 0 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 1 3 (X2 ∷ CS02⁻ ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑)) ((X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 0 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b1 : Chain (X3 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ Sw23 ∷ X2 ∷ Sw23 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ []) (X3 ∷ CS03⁻ ∷ X3 ∷ Sw01 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ [])
  b1 = at 1 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 7 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 6 2 (Sw01 ∷ S2 ∷ []) (sym (low-comm (Swap) (S))) ▸
       at 5 2 (Sw01 ∷ S2 ∷ []) (sym (low-comm (Swap) (S))) ▸
       at 4 2 (Sw01 ∷ K2⁻ ∷ []) (sym (low-comm (Swap) ((K • iI)))) ▸
       at 3 2 (Sw01 ∷ S2⁻ ∷ []) (sym (low-comm (Swap) ((S • S • S)))) ▸ done

  b2 : Chain (X3 ∷ CS03⁻ ∷ X3 ∷ Sw01 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ []) (Sw01 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ [])
  b2 = at 2 2 (Sw01 ∷ X3 ∷ []) (sym (low-comm (Swap) ((X ↑)))) ▸
       at 1 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 2 2 (Sw01 ∷ CS12⁻ ∷ []) (win 3 0 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) (Swap • ((CS • CS • CS) ↑)) tt tt Eq.refl) ▸
       at 1 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 2 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw01 ∷ X3 ∷ []) (sym (low-comm (Swap) ((X ↑)))) ▸
       at 1 7 (S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • ((S • S • S) ↑) • ((K • iI) ↑) • (S ↑) • (S ↑)) (((S • S • S) ↑) • ((K • iI) ↑) • (S ↑) • (S ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸ done

  b3 : Chain (Sw01 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ []) (S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ X3 ∷ Sw23 ∷ CS02⁻ ∷ Sw01 ∷ Sw23 ∷ X3 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ [])
  b3 = at 0 2 (S2⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((S • S • S))) ▸
       at 1 2 (K2⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((K • iI))) ▸
       at 2 2 (S2 ∷ Sw01 ∷ []) (low-comm (Swap) (S)) ▸
       at 3 2 (S2 ∷ Sw01 ∷ []) (low-comm (Swap) (S)) ▸
       at 4 2 (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑))) ▸
       at 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 2 (CS02⁻ ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • ((CS • CS • CS) ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) tt tt Eq.refl) ▸ done

  b4 : Chain (S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ X3 ∷ Sw23 ∷ CS02⁻ ∷ Sw01 ∷ Sw23 ∷ X3 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ []) (S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ S2⁻ ∷ S2⁻ ∷ Sw01 ∷ K2 ∷ S2 ∷ Sw01 ∷ [])
  b4 = at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑))) ▸
       at 7 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 4 7 (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) (lem-pass-X3-CSd30-X3-vs-CS23-TOFF201-CSd23-TOFF201) ▸
       at 15 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 14 2 (Sw01 ∷ S2 ∷ []) (sym (low-comm (Swap) (S))) ▸
       at 13 2 (Sw01 ∷ K2 ∷ []) (sym (low-comm (Swap) (K))) ▸ done

  b5 : Chain (S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ S2⁻ ∷ S2⁻ ∷ Sw01 ∷ K2 ∷ S2 ∷ Sw01 ∷ []) (S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ Sw01 ∷ CS13⁻ ∷ X3 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ Sw01 ∷ [])
  b5 = at 12 2 (Sw01 ∷ S2⁻ ∷ []) (sym (low-comm (Swap) ((S • S • S)))) ▸
       at 11 2 (Sw01 ∷ S2⁻ ∷ []) (sym (low-comm (Swap) ((S • S • S)))) ▸
       at 10 2 (Sw01 ∷ X3 ∷ []) (sym (low-comm (Swap) ((X ↑)))) ▸
       at 9 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 10 2 (Sw01 ∷ CS12⁻ ∷ []) (win 3 0 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) (Swap • ((CS • CS • CS) ↑)) tt tt Eq.refl) ▸
       at 9 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 10 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b6 : Chain (S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ Sw01 ∷ CS13⁻ ∷ X3 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ Sw01 ∷ []) (S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X3 ∷ Sw01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ X3 ∷ Sw01 ∷ [])
  b6 = at 8 2 (Sw01 ∷ X3 ∷ []) (sym (low-comm (Swap) ((X ↑)))) ▸
       at 9 7 (S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • ((S • S • S) ↑) • ((S • S • S) ↑) • (K ↑) • (S ↑)) (((S • S • S) ↑) • ((S • S • S) ↑) • (K ↑) • (S ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 8 2 (S2⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((S • S • S))) ▸
       at 9 2 (S2⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((S • S • S))) ▸
       at 10 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 11 2 (S2 ∷ Sw01 ∷ []) (low-comm (Swap) (S)) ▸
       at 12 2 (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑))) ▸
       at 14 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b7 : Chain (S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X3 ∷ Sw01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ X3 ∷ Sw01 ∷ []) (S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X3 ∷ CS03⁻ ∷ Sw23 ∷ X2 ∷ Sw23 ∷ [])
  b7 = at 13 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 14 2 (CS02⁻ ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • ((CS • CS • CS) ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 15 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 13 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑))) ▸
       at 15 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 15 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 14 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸ done

  b8 : Chain (S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X3 ∷ CS03⁻ ∷ Sw23 ∷ X2 ∷ Sw23 ∷ []) (S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ Sw23 ∷ Sw23 ∷ [])
  b8 = at 13 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 15 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 12 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 13 3 (X2 ∷ CS02⁻ ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑)) ((X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 12 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 15 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 13 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b9 : Chain (S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ Sw23 ∷ Sw23 ∷ []) (S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ [])
  b9 = at 15 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- pass [CSd30] [X3 Sd2 Kd2 S2 S2 CS23 TOFF201 CSd23 TOFF201 Sd2 Sd2 K2 S2 X3]: 23 steps
lem-pass-CSd30-vs-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X3 : ⟪ (CS03⁻ ∷ X3 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X3 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-pass-CSd30-vs-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X3 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS03⁻ ∷ X3 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X3 ∷ []) (X3 ∷ X3 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ Sw23 ∷ X2 ∷ Sw23 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X3 ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 0 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 2 (X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) (win 3 0 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 0 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b1 : Chain (X3 ∷ X3 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ Sw23 ∷ X2 ∷ Sw23 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X3 ∷ []) (X3 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X3 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ Sw23 ∷ X2 ∷ X2 ∷ Sw23 ∷ [])
  b1 = at 2 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 4 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 15 (S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) (lem-pass-X3-CSd30-X3-vs-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2) ▸
       at 17 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 16 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 15 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 14 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (X3 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X3 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ Sw23 ∷ X2 ∷ X2 ∷ Sw23 ∷ []) (X3 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X3 ∷ CS03⁻ ∷ [])
  b2 = at 16 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 13 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 14 4 (X2 ∷ CS02⁻ ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑)) ((X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) tt tt Eq.refl) ▸
       at 13 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 16 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 14 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 15 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- pass [X3 CKd30 X3] [Sd2 Kd2 S2 S2 CS23 TOFF201 CSd23 TOFF201 Sd2 Sd2 K2 S2]: 73 steps
lem-pass-X3-CKd30-X3-vs-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2 : ⟪ (X3 ∷ CK30⁻ ∷ X3 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ []) ⟫ʷ ≈ ⟪ (S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CKd30-X3-vs-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (run b9)))))))))
  where
  b0 : Chain (X3 ∷ CK30⁻ ∷ X3 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ []) (X3 ∷ Sw23 ∷ CK20⁻ ∷ Sw23 ∷ Sw23 ∷ X2 ∷ Sw23 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ [])
  b0 = at 3 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 1 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 0 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 1 3 (X2 ∷ CK20⁻ ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑)) ((X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 0 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b1 : Chain (X3 ∷ Sw23 ∷ CK20⁻ ∷ Sw23 ∷ Sw23 ∷ X2 ∷ Sw23 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ []) (X3 ∷ CK30⁻ ∷ X3 ∷ Sw01 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ [])
  b1 = at 1 3 (CK30⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 7 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 6 2 (Sw01 ∷ S2 ∷ []) (sym (low-comm (Swap) (S))) ▸
       at 5 2 (Sw01 ∷ S2 ∷ []) (sym (low-comm (Swap) (S))) ▸
       at 4 2 (Sw01 ∷ K2⁻ ∷ []) (sym (low-comm (Swap) ((K • iI)))) ▸
       at 3 2 (Sw01 ∷ S2⁻ ∷ []) (sym (low-comm (Swap) ((S • S • S)))) ▸ done

  b2 : Chain (X3 ∷ CK30⁻ ∷ X3 ∷ Sw01 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ []) (Sw01 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ [])
  b2 = at 2 2 (Sw01 ∷ X3 ∷ []) (sym (low-comm (Swap) ((X ↑)))) ▸
       at 1 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 2 2 (Sw01 ∷ CK21⁻ ∷ []) (win 3 0 complete₃ ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • Swap) (Swap • ((S ↑ • CK₁₀) ↑)) tt tt Eq.refl) ▸
       at 1 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 2 3 (CK31⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw01 ∷ X3 ∷ []) (sym (low-comm (Swap) ((X ↑)))) ▸
       at 1 7 (S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • ((S • S • S) ↑) • ((K • iI) ↑) • (S ↑) • (S ↑)) (((S • S • S) ↑) • ((K • iI) ↑) • (S ↑) • (S ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸ done

  b3 : Chain (Sw01 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ []) (S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ X3 ∷ Sw23 ∷ CK20⁻ ∷ Sw01 ∷ Sw23 ∷ X3 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ [])
  b3 = at 0 2 (S2⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((S • S • S))) ▸
       at 1 2 (K2⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((K • iI))) ▸
       at 2 2 (S2 ∷ Sw01 ∷ []) (low-comm (Swap) (S)) ▸
       at 3 2 (S2 ∷ Sw01 ∷ []) (low-comm (Swap) (S)) ▸
       at 4 2 (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑))) ▸
       at 6 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 2 (CK20⁻ ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • ((S ↑ • CK₁₀) ↑)) ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • Swap) tt tt Eq.refl) ▸ done

  b4 : Chain (S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ X3 ∷ Sw23 ∷ CK20⁻ ∷ Sw01 ∷ Sw23 ∷ X3 ∷ Sw01 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ []) (S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ S2⁻ ∷ S2⁻ ∷ Sw01 ∷ K2 ∷ S2 ∷ Sw01 ∷ [])
  b4 = at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 3 (CK30⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑))) ▸
       at 7 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 4 7 (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) (lem-pass-X3-CKd30-X3-vs-CS23-TOFF201-CSd23-TOFF201) ▸
       at 15 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 14 2 (Sw01 ∷ S2 ∷ []) (sym (low-comm (Swap) (S))) ▸
       at 13 2 (Sw01 ∷ K2 ∷ []) (sym (low-comm (Swap) (K))) ▸ done

  b5 : Chain (S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ S2⁻ ∷ S2⁻ ∷ Sw01 ∷ K2 ∷ S2 ∷ Sw01 ∷ []) (S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ Sw01 ∷ CK31⁻ ∷ X3 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ Sw01 ∷ [])
  b5 = at 12 2 (Sw01 ∷ S2⁻ ∷ []) (sym (low-comm (Swap) ((S • S • S)))) ▸
       at 11 2 (Sw01 ∷ S2⁻ ∷ []) (sym (low-comm (Swap) ((S • S • S)))) ▸
       at 10 2 (Sw01 ∷ X3 ∷ []) (sym (low-comm (Swap) ((X ↑)))) ▸
       at 9 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 10 2 (Sw01 ∷ CK21⁻ ∷ []) (win 3 0 complete₃ ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • Swap) (Swap • ((S ↑ • CK₁₀) ↑)) tt tt Eq.refl) ▸
       at 9 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 10 3 (CK31⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b6 : Chain (S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ Sw01 ∷ CK31⁻ ∷ X3 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ Sw01 ∷ []) (S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X3 ∷ Sw01 ∷ Sw23 ∷ CK21⁻ ∷ Sw23 ∷ X3 ∷ Sw01 ∷ [])
  b6 = at 8 2 (Sw01 ∷ X3 ∷ []) (sym (low-comm (Swap) ((X ↑)))) ▸
       at 9 7 (S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • ((S • S • S) ↑) • ((S • S • S) ↑) • (K ↑) • (S ↑)) (((S • S • S) ↑) • ((S • S • S) ↑) • (K ↑) • (S ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 8 2 (S2⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((S • S • S))) ▸
       at 9 2 (S2⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((S • S • S))) ▸
       at 10 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 11 2 (S2 ∷ Sw01 ∷ []) (low-comm (Swap) (S)) ▸
       at 12 2 (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑))) ▸
       at 14 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b7 : Chain (S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X3 ∷ Sw01 ∷ Sw23 ∷ CK21⁻ ∷ Sw23 ∷ X3 ∷ Sw01 ∷ []) (S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X3 ∷ CK30⁻ ∷ Sw23 ∷ X2 ∷ Sw23 ∷ [])
  b7 = at 13 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 14 2 (CK20⁻ ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • ((S ↑ • CK₁₀) ↑)) ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 15 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 13 3 (CK30⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑))) ▸
       at 15 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 15 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 14 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸ done

  b8 : Chain (S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X3 ∷ CK30⁻ ∷ Sw23 ∷ X2 ∷ Sw23 ∷ []) (S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ Sw23 ∷ Sw23 ∷ [])
  b8 = at 13 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 15 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 12 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 13 3 (X2 ∷ CK20⁻ ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑)) ((X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 12 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 15 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 13 3 (CK30⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b9 : Chain (S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ Sw23 ∷ Sw23 ∷ []) (S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ [])
  b9 = at 15 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

