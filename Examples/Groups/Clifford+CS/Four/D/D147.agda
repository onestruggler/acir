{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D147 where

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
open import Examples.Groups.Clifford+CS.Four.D.D025 using (lem-pass-CS13-vs-CS02)
open import Examples.Groups.Clifford+CS.Four.D.D029 using (lem-pass-CSd02-vs-CS13)
open import Examples.Groups.Clifford+CS.Four.D.D030 using (lem-pass-CS13-vs-CSd03 ; lem-pass-CS13-vs-S0 ; lem-pass-CS13-vs-TOFF012 ; lem-pass-TOFF102-vs-CSd03)
open import Examples.Groups.Clifford+CS.Four.D.D031 using (lem-pass-CS13-vs-CS03 ; lem-pass-CS13-vs-Sd0 ; lem-pass-CSd13-vs-CSd03 ; lem-pass-CSd13-vs-S0)
open import Examples.Groups.Clifford+CS.Four.D.D133 using (lem-pass-X3-CK31-X3-vs-CS13-TOFF102-CSd13-TOFF102 ; lem-pass-X3-CS31-X3-vs-CS13-TOFF102-CSd13-TOFF102)
-- pass [CK31] [X3 CS13 TOFF102 CSd13 TOFF102 X3]: 3 steps
lem-pass-CK31-vs-X3-CS13-TOFF102-CSd13-TOFF102-X3 : ⟪ (CK31 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ CK31 ∷ []) ⟫ʷ
lem-pass-CK31-vs-X3-CS13-TOFF102-CSd13-TOFF102-X3 = run b0
  where
  b0 : Chain (CK31 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ []) (X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ CK31 ∷ [])
  b0 = at 0 2 (X3 ∷ X3 ∷ CK31 ∷ X3 ∷ []) (win 0 3 complete₃ ((Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 1 7 (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ CK31 ∷ X3 ∷ []) (lem-pass-X3-CK31-X3-vs-CS13-TOFF102-CSd13-TOFF102) ▸
       at 5 4 (X3 ∷ CK31 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑ ↑)) ((X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑)) tt tt Eq.refl) ▸ done


-- pass [CS31] [X3 CS13 TOFF102 CSd13 TOFF102 X3]: 3 steps
lem-pass-CS31-vs-X3-CS13-TOFF102-CSd13-TOFF102-X3 : ⟪ (CS13 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ CS13 ∷ []) ⟫ʷ
lem-pass-CS31-vs-X3-CS13-TOFF102-CSd13-TOFF102-X3 = run b0
  where
  b0 : Chain (CS13 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ []) (X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ CS13 ∷ [])
  b0 = at 0 2 (X3 ∷ X3 ∷ CS13 ∷ X3 ∷ []) (win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 1 7 (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ CS13 ∷ X3 ∷ []) (lem-pass-X3-CS31-X3-vs-CS13-TOFF102-CSd13-TOFF102) ▸
       at 5 4 (X3 ∷ CS13 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑)) ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸ done


-- ca-split Gad(t=1, W=(3,), d=SK, e=-1) 3: 9 steps
lem-ca-split-Gad⟨t≡1-W≡⟨3⟩-d≡SK-e≡-1⟩-3 : ⟪ (X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13 ∷ X3 ∷ X3 ∷ CK31 ∷ X3 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ
lem-ca-split-Gad⟨t≡1-W≡⟨3⟩-d≡SK-e≡-1⟩-3 = trans (run b0) (run b1)
  where
  b0 : Chain (X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ []) (X3 ∷ CS13 ∷ X3 ∷ X3 ∷ CK31 ∷ X3 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ CS13 ∷ CK31 ∷ CK31⁻ ∷ CS13⁻ ∷ X3 ∷ CK31⁻ ∷ X3 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ [])
  b0 = at 0 2 (S1 ∷ X3 ∷ []) (sym (low-comm ((S ↑)) ((X ↑)))) ▸
       at 1 2 (K1 ∷ X3 ∷ []) (sym (low-comm ((K ↑)) ((X ↑)))) ▸
       at 8 2 (X3 ∷ S1⁻ ∷ []) (low-comm (((S • S • S) ↑)) ((X ↑))) ▸
       at 7 2 (X3 ∷ K1⁻ ∷ []) (low-comm (((K • iI) ↑)) ((X ↑))) ▸
       at 0 2 (X3 ∷ CS13 ∷ X3 ∷ X3 ∷ CK31 ∷ X3 ∷ CS13 ∷ CK31 ∷ []) (win 0 3 complete₃ (S • K) ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑)) tt tt Eq.refl) ▸
       at 14 2 (CK31⁻ ∷ CS13⁻ ∷ X3 ∷ CK31⁻ ∷ X3 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) (win 0 3 complete₃ ((K • iI) • (S • S • S)) ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 7 7 (X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ CK31 ∷ []) (lem-pass-CK31-vs-X3-CS13-TOFF102-CSd13-TOFF102-X3) ▸
       at 6 7 (X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ CS13 ∷ []) (lem-pass-CS31-vs-X3-CS13-TOFF102-CSd13-TOFF102-X3) ▸ done

  b1 : Chain (X3 ∷ CS13 ∷ X3 ∷ X3 ∷ CK31 ∷ X3 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ CS13 ∷ CK31 ∷ CK31⁻ ∷ CS13⁻ ∷ X3 ∷ CK31⁻ ∷ X3 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) (X3 ∷ CS13 ∷ X3 ∷ X3 ∷ CK31 ∷ X3 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ [])
  b1 = at 12 4 [] (win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- pass [CS13] [S0 CSd03 TOFF012 Sd0 CS03 TOFF012]: 6 steps
lem-pass-CS13-vs-S0-CSd03-TOFF012-Sd0-CS03-TOFF012 : ⟪ (CS13 ∷ S0 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ CS13 ∷ []) ⟫ʷ
lem-pass-CS13-vs-S0-CSd03-TOFF012-Sd0-CS03-TOFF012 = run b0
  where
  b0 : Chain (CS13 ∷ S0 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ []) (S0 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ CS13 ∷ [])
  b0 = at 0 2 (S0 ∷ CS13 ∷ []) (lem-pass-CS13-vs-S0) ▸
       at 1 2 (CS03⁻ ∷ CS13 ∷ []) (lem-pass-CS13-vs-CSd03) ▸
       at 2 2 (Toff012 ∷ CS13 ∷ []) (lem-pass-CS13-vs-TOFF012) ▸
       at 3 2 (S0⁻ ∷ CS13 ∷ []) (lem-pass-CS13-vs-Sd0) ▸
       at 4 2 (CS03 ∷ CS13 ∷ []) (lem-pass-CS13-vs-CS03) ▸
       at 5 2 (Toff012 ∷ CS13 ∷ []) (lem-pass-CS13-vs-TOFF012) ▸ done


-- pass [S0] [CS13 TOFF102 CSd13 TOFF102]: 4 steps
lem-pass-S0-vs-CS13-TOFF102-CSd13-TOFF102 : ⟪ (S0 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S0 ∷ []) ⟫ʷ
lem-pass-S0-vs-CS13-TOFF102-CSd13-TOFF102 = run b0
  where
  b0 : Chain (S0 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S0 ∷ [])
  b0 = at 0 2 (CS13 ∷ S0 ∷ []) (sym lem-pass-CS13-vs-S0) ▸
       at 1 2 (Toff102 ∷ S0 ∷ []) (win 3 0 complete₃ (S • (K ↑ • CCZ • K ↑ • iI)) ((K ↑ • CCZ • K ↑ • iI) • S) tt tt Eq.refl) ▸
       at 2 2 (CS13⁻ ∷ S0 ∷ []) (sym lem-pass-CSd13-vs-S0) ▸
       at 3 2 (Toff102 ∷ S0 ∷ []) (win 3 0 complete₃ (S • (K ↑ • CCZ • K ↑ • iI)) ((K ↑ • CCZ • K ↑ • iI) • S) tt tt Eq.refl) ▸ done


-- pass [CS13 TOFF102 CSd13 TOFF102] [S0]: 1 steps
lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-S0 : ⟪ (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) ⟫ʷ
lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-S0 = run b0
  where
  b0 : Chain (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S0 ∷ []) (S0 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ [])
  b0 = at 0 5 (S0 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (sym lem-pass-S0-vs-CS13-TOFF102-CSd13-TOFF102) ▸ done


-- pass [CSd03] [CS13 TOFF102 CSd13 TOFF102]: 4 steps
lem-pass-CSd03-vs-CS13-TOFF102-CSd13-TOFF102 : ⟪ (CS03⁻ ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-pass-CSd03-vs-CS13-TOFF102-CSd13-TOFF102 = run b0
  where
  b0 : Chain (CS03⁻ ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ CS03⁻ ∷ [])
  b0 = at 0 2 (CS13 ∷ CS03⁻ ∷ []) (sym lem-pass-CS13-vs-CSd03) ▸
       at 1 2 (Toff102 ∷ CS03⁻ ∷ []) (sym lem-pass-TOFF102-vs-CSd03) ▸
       at 2 2 (CS13⁻ ∷ CS03⁻ ∷ []) (sym lem-pass-CSd13-vs-CSd03) ▸
       at 3 2 (Toff102 ∷ CS03⁻ ∷ []) (sym lem-pass-TOFF102-vs-CSd03) ▸ done


-- pass [CS13 TOFF102 CSd13 TOFF102] [CSd03]: 1 steps
lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-CSd03 : ⟪ (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) ⟫ʷ
lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-CSd03 = run b0
  where
  b0 : Chain (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ [])
  b0 = at 0 5 (CS03⁻ ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (sym lem-pass-CSd03-vs-CS13-TOFF102-CSd13-TOFF102) ▸ done


-- pass [S0 CSd03] [CS13 TOFF102 CSd13 TOFF102]: 8 steps
lem-pass-S0-CSd03-vs-CS13-TOFF102-CSd13-TOFF102 : ⟪ (S0 ∷ CS03⁻ ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S0 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-pass-S0-CSd03-vs-CS13-TOFF102-CSd13-TOFF102 = run b0
  where
  b0 : Chain (S0 ∷ CS03⁻ ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S0 ∷ CS03⁻ ∷ [])
  b0 = at 1 2 (CS13 ∷ CS03⁻ ∷ []) (sym lem-pass-CS13-vs-CSd03) ▸
       at 0 2 (CS13 ∷ S0 ∷ []) (sym lem-pass-CS13-vs-S0) ▸
       at 2 2 (Toff102 ∷ CS03⁻ ∷ []) (sym lem-pass-TOFF102-vs-CSd03) ▸
       at 1 2 (Toff102 ∷ S0 ∷ []) (win 3 0 complete₃ (S • (K ↑ • CCZ • K ↑ • iI)) ((K ↑ • CCZ • K ↑ • iI) • S) tt tt Eq.refl) ▸
       at 3 2 (CS13⁻ ∷ CS03⁻ ∷ []) (sym lem-pass-CSd13-vs-CSd03) ▸
       at 2 2 (CS13⁻ ∷ S0 ∷ []) (sym lem-pass-CSd13-vs-S0) ▸
       at 4 2 (Toff102 ∷ CS03⁻ ∷ []) (sym lem-pass-TOFF102-vs-CSd03) ▸
       at 3 2 (Toff102 ∷ S0 ∷ []) (win 3 0 complete₃ (S • (K ↑ • CCZ • K ↑ • iI)) ((K ↑ • CCZ • K ↑ • iI) • S) tt tt Eq.refl) ▸ done


-- pass [CS13 TOFF102 CSd13 TOFF102] [S0 CSd03]: 1 steps
lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-S0-CSd03 : ⟪ (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S0 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ CS03⁻ ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) ⟫ʷ
lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-S0-CSd03 = run b0
  where
  b0 : Chain (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S0 ∷ CS03⁻ ∷ []) (S0 ∷ CS03⁻ ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ [])
  b0 = at 0 6 (S0 ∷ CS03⁻ ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (sym lem-pass-S0-CSd03-vs-CS13-TOFF102-CSd13-TOFF102) ▸ done


-- pass [X3 CS13 TOFF102 CSd13 TOFF102 X3] [CS03]: 31 steps
lem-pass-X3-CS13-TOFF102-CSd13-TOFF102-X3-vs-CS03 : ⟪ (X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS13-TOFF102-CSd13-TOFF102-X3-vs-CS03 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ CS03 ∷ []) (X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S0 ∷ CS03⁻ ∷ Sw23 ∷ X2 ∷ Sw23 ∷ [])
  b0 = at 7 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 5 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 6 2 (S0 ∷ CS02⁻ ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑)) (S • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 5 2 (S0 ∷ Sw23 ∷ []) (sym (low₁-comm (S) ((Swap ↑)))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 6 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S0 ∷ CS03⁻ ∷ Sw23 ∷ X2 ∷ Sw23 ∷ []) (S0 ∷ Sw23 ∷ X2 ∷ CS02⁻ ∷ Sw23 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ [])
  b1 = at 7 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 8 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 6 (S0 ∷ CS03⁻ ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-S0-CSd03) ▸
       at 0 2 (S0 ∷ X3 ∷ []) (sym (low₁-comm (S) ((X ↑ ↑)))) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸ done

  b2 : Chain (S0 ∷ Sw23 ∷ X2 ∷ CS02⁻ ∷ Sw23 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ []) (S0 ∷ S0⁻ ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ [])
  b2 = at 2 2 (S0⁻ ∷ CS02 ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((S • S • S) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 1 2 (S0⁻ ∷ Sw23 ∷ []) (sym (low₁-comm ((S • S • S)) ((Swap ↑)))) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 4 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b3 : Chain (S0 ∷ S0⁻ ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ []) (CS03 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ [])
  b3 = at 4 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 2 (Sw23 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((Swap ↑))) ▸
       at 0 2 (Sw23 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑))) ▸
       at 1 3 (CS02 ∷ []) (win 3 0 complete₃ (S • (S • S • S) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 0 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- pass [CS03] [X3 CS13 TOFF102 CSd13 TOFF102 X3]: 1 steps
lem-pass-CS03-vs-X3-CS13-TOFF102-CSd13-TOFF102-X3 : ⟪ (CS03 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CS03-vs-X3-CS13-TOFF102-CSd13-TOFF102-X3 = run b0
  where
  b0 : Chain (CS03 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ []) (X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ CS03 ∷ [])
  b0 = at 0 7 (X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ CS03 ∷ []) (sym lem-pass-X3-CS13-TOFF102-CSd13-TOFF102-X3-vs-CS03) ▸ done


-- pass [CS13] [TOFF012 S0 CSd03 TOFF012 Sd0 CS03]: 6 steps
lem-pass-CS13-vs-TOFF012-S0-CSd03-TOFF012-Sd0-CS03 : ⟪ (CS13 ∷ Toff012 ∷ S0 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ S0 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ CS03 ∷ CS13 ∷ []) ⟫ʷ
lem-pass-CS13-vs-TOFF012-S0-CSd03-TOFF012-Sd0-CS03 = run b0
  where
  b0 : Chain (CS13 ∷ Toff012 ∷ S0 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ CS03 ∷ []) (Toff012 ∷ S0 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ CS03 ∷ CS13 ∷ [])
  b0 = at 0 2 (Toff012 ∷ CS13 ∷ []) (lem-pass-CS13-vs-TOFF012) ▸
       at 1 2 (S0 ∷ CS13 ∷ []) (lem-pass-CS13-vs-S0) ▸
       at 2 2 (CS03⁻ ∷ CS13 ∷ []) (lem-pass-CS13-vs-CSd03) ▸
       at 3 2 (Toff012 ∷ CS13 ∷ []) (lem-pass-CS13-vs-TOFF012) ▸
       at 4 2 (S0⁻ ∷ CS13 ∷ []) (lem-pass-CS13-vs-Sd0) ▸
       at 5 2 (CS03 ∷ CS13 ∷ []) (lem-pass-CS13-vs-CS03) ▸ done


-- pass [CS13] [X3 TOFF013 X3 CS02 X3 TOFF013 X3 CSd02]: 382 steps
lem-pass-CS13-vs-X3-TOFF013-X3-CS02-X3-TOFF013-X3-CSd02 : ⟪ (CS13 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ CS13 ∷ []) ⟫ʷ
lem-pass-CS13-vs-X3-TOFF013-X3-CS02-X3-TOFF013-X3-CSd02 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (trans (run b35) (trans (run b36) (trans (run b37) (trans (run b38) (trans (run b39) (trans (run b40) (trans (run b41) (trans (run b42) (trans (run b43) (trans (run b44) (trans (run b45) (trans (run b46) (run b47)))))))))))))))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (CS13 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ []) (CS13 ∷ X3 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ X2 ∷ Sw23 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ [])
  b0 = at 4 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 2 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b1 : Chain (CS13 ∷ X3 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ X2 ∷ Sw23 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ []) (CS13 ∷ X3 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ X2 ∷ Sw23 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ [])
  b1 = at 7 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 10 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b2 : Chain (CS13 ∷ X3 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ X2 ∷ Sw23 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ []) (CS13 ∷ X3 ∷ K0 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ X2 ∷ Sw23 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ [])
  b2 = at 9 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸
       at 8 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 6 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 4 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸ done

  b3 : Chain (CS13 ∷ X3 ∷ K0 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ X2 ∷ Sw23 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ []) (CS13 ∷ CX10 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ [])
  b3 = at 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 2 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 3 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (win 3 0 complete₃ (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) tt tt Eq.refl) ▸
       at 3 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 2 3 (CX10 ∷ Toff012 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • Toff • (X ↑ ↑)) (CX₁₀ • Toff) tt tt Eq.refl) ▸
       at 1 2 (CX10 ∷ Sw23 ∷ []) (sym (low-comm (CX₁₀) (Swap))) ▸ done

  b4 : Chain (CS13 ∷ CX10 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ []) (CS13 ∷ CX10 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ [])
  b4 = at 3 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b5 : Chain (CS13 ∷ CX10 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ []) (CS13 ∷ CX10 ∷ Sw23 ∷ K0 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ [])
  b5 = at 9 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b6 : Chain (CS13 ∷ CX10 ∷ Sw23 ∷ K0 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ []) (CS13 ∷ CX10 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ [])
  b6 = at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 9 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 10 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸ done

  b7 : Chain (CS13 ∷ CX10 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ []) (Sw23 ∷ CS12 ∷ CX10 ∷ Sw23 ∷ Toff013 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ [])
  b7 = at 3 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (win 3 0 complete₃ (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) tt tt Eq.refl) ▸
       at 3 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 2 (Sw23 ∷ CX10 ∷ []) (low-comm (CX₁₀) (Swap)) ▸
       at 0 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b8 : Chain (Sw23 ∷ CS12 ∷ CX10 ∷ Sw23 ∷ Toff013 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ []) (CX10 ∷ CS13 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ [])
  b8 = at 1 2 (CX10 ∷ CS12 ∷ []) (win 3 0 complete₃ ((CS ↑) • CX₁₀) (CX₁₀ • (CS ↑)) tt tt Eq.refl) ▸
       at 0 2 (CX10 ∷ Sw23 ∷ []) (sym (low-comm (CX₁₀) (Swap))) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸ done

  b9 : Chain (CX10 ∷ CS13 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ []) (CX10 ∷ CS13 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ [])
  b9 = at 2 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b10 : Chain (CX10 ∷ CS13 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ []) (CX10 ∷ CS13 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ [])
  b10 = at 7 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 10 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 9 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸
       at 8 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b11 : Chain (CX10 ∷ CS13 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ []) (CX10 ∷ CS13 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ [])
  b11 = at 6 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 4 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 2 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 3 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (win 3 0 complete₃ (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) tt tt Eq.refl) ▸ done

  b12 : Chain (CX10 ∷ CS13 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ []) (CX10 ∷ K0 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ CS12 ∷ Sw23 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ [])
  b12 = at 3 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 2 2 (Toff012 ∷ CS12 ∷ []) (win 3 0 complete₃ ((CS ↑) • Toff) (Toff • (CS ↑)) tt tt Eq.refl) ▸
       at 2 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b13 : Chain (CX10 ∷ K0 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ CS12 ∷ Sw23 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ []) (CX10 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ [])
  b13 = at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 4 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 6 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 8 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸ done

  b14 : Chain (CX10 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ []) (CX10 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw23 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ [])
  b14 = at 1 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b15 : Chain (CX10 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw23 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ []) (CX10 ∷ Toff013 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ [])
  b15 = at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 8 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 2 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (win 3 0 complete₃ (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) tt tt Eq.refl) ▸
       at 2 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b16 : Chain (CX10 ∷ Toff013 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ []) (CX10 ∷ K0 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS13 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ [])
  b16 = at 2 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b17 : Chain (CX10 ∷ K0 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS13 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ []) (CX10 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS13 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ [])
  b17 = at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 4 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 6 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 8 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸ done

  b18 : Chain (CX10 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS13 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ []) (CX10 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ CS13 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ [])
  b18 = at 9 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 8 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸
       at 7 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 5 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 4 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b19 : Chain (CX10 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ CS13 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ []) (Sw23 ∷ X2 ∷ Toff012 ∷ X2 ∷ Sw23 ∷ CS13 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ [])
  b19 = at 3 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 2 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (win 3 0 complete₃ (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) tt tt Eq.refl) ▸
       at 2 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw23 ∷ CX10 ∷ []) (low-comm (CX₁₀) (Swap)) ▸
       at 1 2 (X2 ∷ Toff012 ∷ X2 ∷ []) (win 3 0 complete₃ (CX₁₀ • Toff) ((X ↑ ↑) • Toff • (X ↑ ↑)) tt tt Eq.refl) ▸ done

  b20 : Chain (Sw23 ∷ X2 ∷ Toff012 ∷ X2 ∷ Sw23 ∷ CS13 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ []) (X3 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ X2 ∷ Sw23 ∷ CS13 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ [])
  b20 = at 0 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 4 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b21 : Chain (X3 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ X2 ∷ Sw23 ∷ CS13 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ []) (X3 ∷ Sw23 ∷ K0 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ X2 ∷ Sw23 ∷ CS13 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ [])
  b21 = at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 6 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 8 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b22 : Chain (X3 ∷ Sw23 ∷ K0 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ X2 ∷ Sw23 ∷ CS13 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ []) (X3 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ Sw23 ∷ ι ∷ Sw23 ∷ X2 ∷ Sw23 ∷ CS13 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ [])
  b22 = at 3 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 8 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸ done

  b23 : Chain (X3 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ Sw23 ∷ ι ∷ Sw23 ∷ X2 ∷ Sw23 ∷ CS13 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ []) (X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ CS13 ∷ X3 ∷ Toff013 ∷ X3 ∷ Sw23 ∷ Sw23 ∷ CS02⁻ ∷ [])
  b23 = at 9 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 2 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (win 3 0 complete₃ (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) tt tt Eq.refl) ▸
       at 2 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 3 2 (CS02 ∷ CS13 ∷ []) (lem-pass-CS13-vs-CS02) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b24 : Chain (X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ CS13 ∷ X3 ∷ Toff013 ∷ X3 ∷ Sw23 ∷ Sw23 ∷ CS02⁻ ∷ []) (X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ CS13 ∷ X3 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ X2 ∷ Sw23 ∷ CS02⁻ ∷ [])
  b24 = at 7 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 6 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b25 : Chain (X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ CS13 ∷ X3 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ X2 ∷ Sw23 ∷ CS02⁻ ∷ []) (X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ CS13 ∷ X3 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ Sw23 ∷ ι ∷ X2 ∷ Sw23 ∷ CS02⁻ ∷ [])
  b25 = at 9 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 13 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 11 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 13 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 14 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 13 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸ done

  b26 : Chain (X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ CS13 ∷ X3 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ Sw23 ∷ ι ∷ X2 ∷ Sw23 ∷ CS02⁻ ∷ []) (X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ CS13 ∷ X3 ∷ K0 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ X2 ∷ Sw23 ∷ CS02⁻ ∷ [])
  b26 = at 12 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 10 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 9 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 8 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b27 : Chain (X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ CS13 ∷ X3 ∷ K0 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ X2 ∷ Sw23 ∷ CS02⁻ ∷ []) (X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ CS13 ∷ CX10 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ CS02⁻ ∷ [])
  b27 = at 9 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 6 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 7 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (win 3 0 complete₃ (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) tt tt Eq.refl) ▸
       at 7 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 6 3 (CX10 ∷ Toff012 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • Toff • (X ↑ ↑)) (CX₁₀ • Toff) tt tt Eq.refl) ▸
       at 5 2 (CX10 ∷ Sw23 ∷ []) (sym (low-comm (CX₁₀) (Swap))) ▸
       at 7 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸ done

  b28 : Chain (X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ CS13 ∷ CX10 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ CS02⁻ ∷ []) (X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ CS13 ∷ CX10 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw23 ∷ CS02⁻ ∷ [])
  b28 = at 6 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 9 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 13 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b29 : Chain (X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ CS13 ∷ CX10 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw23 ∷ CS02⁻ ∷ []) (X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ CS13 ∷ CX10 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ Sw23 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ CS02⁻ ∷ [])
  b29 = at 11 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 13 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 9 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b30 : Chain (X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ CS13 ∷ CX10 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ Sw23 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ CS02⁻ ∷ []) (X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ CS13 ∷ CX10 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS02⁻ ∷ [])
  b30 = at 11 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 11 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 13 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 14 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 7 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (win 3 0 complete₃ (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) tt tt Eq.refl) ▸ done

  b31 : Chain (X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ CS13 ∷ CX10 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS02⁻ ∷ []) (X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ Sw23 ∷ CX10 ∷ CS12 ∷ Sw23 ∷ Toff013 ∷ CS02⁻ ∷ [])
  b31 = at 7 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 6 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 2 (Sw23 ∷ CX10 ∷ []) (low-comm (CX₁₀) (Swap)) ▸
       at 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 5 2 (CX10 ∷ CS12 ∷ []) (win 3 0 complete₃ ((CS ↑) • CX₁₀) (CX₁₀ • (CS ↑)) tt tt Eq.refl) ▸ done

  b32 : Chain (X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ Sw23 ∷ CX10 ∷ CS12 ∷ Sw23 ∷ Toff013 ∷ CS02⁻ ∷ []) (X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ CX10 ∷ CS13 ∷ K0 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS02⁻ ∷ [])
  b32 = at 4 2 (CX10 ∷ Sw23 ∷ []) (sym (low-comm (CX₁₀) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 6 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸ done

  b33 : Chain (X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ CX10 ∷ CS13 ∷ K0 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS02⁻ ∷ []) (X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ CX10 ∷ CS13 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS02⁻ ∷ [])
  b33 = at 9 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 9 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 13 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 11 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸ done

  b34 : Chain (X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ CX10 ∷ CS13 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS02⁻ ∷ []) (X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ CX10 ∷ CS13 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ CS02⁻ ∷ [])
  b34 = at 12 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 13 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 14 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 13 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸
       at 12 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 10 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸ done

  b35 : Chain (X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ CX10 ∷ CS13 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ CS02⁻ ∷ []) (X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ CX10 ∷ CS13 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ CS02⁻ ∷ [])
  b35 = at 9 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 8 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 6 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 7 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (win 3 0 complete₃ (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) tt tt Eq.refl) ▸
       at 7 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸ done

  b36 : Chain (X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ CX10 ∷ CS13 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ CS02⁻ ∷ []) (X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ CX10 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ CS12 ∷ Sw23 ∷ CS02⁻ ∷ [])
  b36 = at 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 6 2 (Toff012 ∷ CS12 ∷ []) (win 3 0 complete₃ ((CS ↑) • Toff) (Toff • (CS ↑)) tt tt Eq.refl) ▸
       at 6 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 6 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b37 : Chain (X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ CX10 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ CS12 ∷ Sw23 ∷ CS02⁻ ∷ []) (X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ CX10 ∷ Sw23 ∷ Sw23 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CS02⁻ ∷ [])
  b37 = at 10 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 8 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 10 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 12 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b38 : Chain (X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ CX10 ∷ Sw23 ∷ Sw23 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CS02⁻ ∷ []) (X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ CX10 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw23 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CS02⁻ ∷ [])
  b38 = at 6 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 10 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 10 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b39 : Chain (X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ CX10 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw23 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CS02⁻ ∷ []) (X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ CX10 ∷ Toff013 ∷ CS13 ∷ Sw23 ∷ Sw23 ∷ CS02⁻ ∷ [])
  b39 = at 11 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 12 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 13 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 6 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (win 3 0 complete₃ (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) tt tt Eq.refl) ▸
       at 6 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 5 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 6 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b40 : Chain (X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ CX10 ∷ Toff013 ∷ CS13 ∷ Sw23 ∷ Sw23 ∷ CS02⁻ ∷ []) (X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ CX10 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS13 ∷ CS02⁻ ∷ [])
  b40 = at 7 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 6 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b41 : Chain (X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ CX10 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS13 ∷ CS02⁻ ∷ []) (X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ CX10 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ CS13 ∷ CS02⁻ ∷ [])
  b41 = at 10 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 8 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 10 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 12 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 13 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b42 : Chain (X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ CX10 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ CS13 ∷ CS02⁻ ∷ []) (X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ CX10 ∷ K0 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ CS13 ∷ CS02⁻ ∷ [])
  b42 = at 12 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸
       at 11 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 9 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 7 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸ done

  b43 : Chain (X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ CX10 ∷ K0 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ CS13 ∷ CS02⁻ ∷ []) (X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ X3 ∷ Sw23 ∷ Toff012 ∷ X2 ∷ Sw23 ∷ CS13 ∷ CS02⁻ ∷ [])
  b43 = at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 5 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 6 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (win 3 0 complete₃ (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) tt tt Eq.refl) ▸
       at 6 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw23 ∷ CX10 ∷ []) (low-comm (CX₁₀) (Swap)) ▸
       at 5 2 (X2 ∷ Toff012 ∷ X2 ∷ []) (win 3 0 complete₃ (CX₁₀ • Toff) ((X ↑ ↑) • Toff • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 4 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b44 : Chain (X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ X3 ∷ Sw23 ∷ Toff012 ∷ X2 ∷ Sw23 ∷ CS13 ∷ CS02⁻ ∷ []) (X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ X3 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ K0 ∷ ι ∷ X2 ∷ Sw23 ∷ CS13 ∷ CS02⁻ ∷ [])
  b44 = at 6 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 6 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 8 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b45 : Chain (X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ X3 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ K0 ∷ ι ∷ X2 ∷ Sw23 ∷ CS13 ∷ CS02⁻ ∷ []) (X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ X3 ∷ Sw23 ∷ K0 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ X2 ∷ Sw23 ∷ CS13 ∷ CS02⁻ ∷ [])
  b45 = at 12 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 10 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 12 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 6 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b46 : Chain (X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ X3 ∷ Sw23 ∷ K0 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ X2 ∷ Sw23 ∷ CS13 ∷ CS02⁻ ∷ []) (X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ X3 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ X2 ∷ Sw23 ∷ CS13 ∷ CS02⁻ ∷ [])
  b46 = at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 10 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 10 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 12 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 13 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸ done

  b47 : Chain (X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ X3 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ X2 ∷ Sw23 ∷ CS13 ∷ CS02⁻ ∷ []) (X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ CS13 ∷ [])
  b47 = at 6 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (win 3 0 complete₃ (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) tt tt Eq.refl) ▸
       at 6 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 5 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 7 2 (CS02⁻ ∷ CS13 ∷ []) (sym lem-pass-CSd02-vs-CS13) ▸ done

