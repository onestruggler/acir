{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D689 where

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
open import Examples.Groups.Clifford+CS.Four.D.D030 using (lem-pass-CS13-vs-CSd03 ; lem-pass-TOFF012-vs-CS13 ; lem-pass-TOFF102-vs-CS03 ; lem-pass-TOFF102-vs-CSd03)
open import Examples.Groups.Clifford+CS.Four.D.D031 using (lem-pass-CS13-vs-CS03 ; lem-pass-CSd13-vs-CS03 ; lem-pass-CSd13-vs-CSd03 ; lem-pass-CSd13-vs-TOFF012 ; lem-pass-TOFF012-vs-CSd13)
open import Examples.Groups.Clifford+CS.Four.D.D046 using (lem-ca-split-Gad⟨t≡0-W≡⟨3⟩-d≡SK-e≡-1⟩-3)
open import Examples.Groups.Clifford+CS.Four.D.D048 using (lem-pass-CS03-vs-S1 ; lem-pass-CS03-vs-Sd1)
open import Examples.Groups.Clifford+CS.Four.D.D074 using (lem-pass-TOFF012-vs-X2-TOFF102-X2)
open import Examples.Groups.Clifford+CS.Four.D.D076 using (lem-pass-CSd03-vs-S1)
open import Examples.Groups.Clifford+CS.Four.D.D082 using (lem-pass-CK31-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 ; lem-pass-CKd31-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 ; lem-pass-CS31-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 ; lem-pass-CSd31-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 ; lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3)
open import Examples.Groups.Clifford+CS.Four.D.D148 using (lem-pass-X3-CSd30-X3-vs-CS13-TOFF102-CSd13-TOFF102)
open import Examples.Groups.Clifford+CS.Four.D.D149 using (lem-pass-X3-CK30-X3-vs-CS13-TOFF102-CSd13-TOFF102 ; lem-pass-X3-CKd30-X3-vs-CS13-TOFF102-CSd13-TOFF102 ; lem-pass-X3-CS30-X3-vs-CS13-TOFF102-CSd13-TOFF102)
open import Examples.Groups.Clifford+CS.Four.D.D150 using (lem-pass-X2-CKd21-X2-vs-CS13-TOFF102-CSd13-TOFF102 ; lem-pass-X2-CS21-X2-vs-CS13-TOFF102-CSd13-TOFF102 ; lem-pass-X2-CSd21-X2-vs-CS13-TOFF102-CSd13-TOFF102)
open import Examples.Groups.Clifford+CS.Four.D.D688 using (lem-ca-split-Gad⟨t≡1-W≡⟨⟩-d≡SdKdSS-e≡-1⟩-3)
-- pass [CS03] [S1 CSd13 TOFF102 Sd1 CS13 TOFF102]: 6 steps
lem-pass-CS03-vs-S1-CSd13-TOFF102-Sd1-CS13-TOFF102 : ⟪ (CS03 ∷ S1 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ CS13 ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ CS13 ∷ Toff102 ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CS03-vs-S1-CSd13-TOFF102-Sd1-CS13-TOFF102 = run b0
  where
  b0 : Chain (CS03 ∷ S1 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ CS13 ∷ Toff102 ∷ []) (S1 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ CS13 ∷ Toff102 ∷ CS03 ∷ [])
  b0 = at 0 2 (S1 ∷ CS03 ∷ []) (lem-pass-CS03-vs-S1) ▸
       at 1 2 (CS13⁻ ∷ CS03 ∷ []) (sym lem-pass-CSd13-vs-CS03) ▸
       at 2 2 (Toff102 ∷ CS03 ∷ []) (sym lem-pass-TOFF102-vs-CS03) ▸
       at 3 2 (S1⁻ ∷ CS03 ∷ []) (lem-pass-CS03-vs-Sd1) ▸
       at 4 2 (CS13 ∷ CS03 ∷ []) (sym lem-pass-CS13-vs-CS03) ▸
       at 5 2 (Toff102 ∷ CS03 ∷ []) (sym lem-pass-TOFF102-vs-CS03) ▸ done


-- pass [S1] [CS03 TOFF012 CSd03 TOFF012]: 4 steps
lem-pass-S1-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (S1 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S1 ∷ []) ⟫ʷ
lem-pass-S1-vs-CS03-TOFF012-CSd03-TOFF012 = run b0
  where
  b0 : Chain (S1 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S1 ∷ [])
  b0 = at 0 2 (CS03 ∷ S1 ∷ []) (sym lem-pass-CS03-vs-S1) ▸
       at 1 2 (Toff012 ∷ S1 ∷ []) (win 3 0 complete₃ ((S ↑) • Toff) (Toff • (S ↑)) tt tt Eq.refl) ▸
       at 2 2 (CS03⁻ ∷ S1 ∷ []) (sym lem-pass-CSd03-vs-S1) ▸
       at 3 2 (Toff012 ∷ S1 ∷ []) (win 3 0 complete₃ ((S ↑) • Toff) (Toff • (S ↑)) tt tt Eq.refl) ▸ done


-- pass [CS03 TOFF012 CSd03 TOFF012] [S1]: 1 steps
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-S1 : ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-S1 = run b0
  where
  b0 : Chain (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S1 ∷ []) (S1 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ [])
  b0 = at 0 5 (S1 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (sym lem-pass-S1-vs-CS03-TOFF012-CSd03-TOFF012) ▸ done


-- pass [CSd13] [CS03 TOFF012 CSd03 TOFF012]: 4 steps
lem-pass-CSd13-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (CS13⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-pass-CSd13-vs-CS03-TOFF012-CSd03-TOFF012 = run b0
  where
  b0 : Chain (CS13⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ CS13⁻ ∷ [])
  b0 = at 0 2 (CS03 ∷ CS13⁻ ∷ []) (lem-pass-CSd13-vs-CS03) ▸
       at 1 2 (Toff012 ∷ CS13⁻ ∷ []) (lem-pass-CSd13-vs-TOFF012) ▸
       at 2 2 (CS03⁻ ∷ CS13⁻ ∷ []) (lem-pass-CSd13-vs-CSd03) ▸
       at 3 2 (Toff012 ∷ CS13⁻ ∷ []) (lem-pass-CSd13-vs-TOFF012) ▸ done


-- pass [CS03 TOFF012 CSd03 TOFF012] [CSd13]: 1 steps
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-CSd13 : ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-CSd13 = run b0
  where
  b0 : Chain (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ [])
  b0 = at 0 5 (CS13⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (sym lem-pass-CSd13-vs-CS03-TOFF012-CSd03-TOFF012) ▸ done


-- pass [S1 CSd13] [CS03 TOFF012 CSd03 TOFF012]: 8 steps
lem-pass-S1-CSd13-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (S1 ∷ CS13⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S1 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-pass-S1-CSd13-vs-CS03-TOFF012-CSd03-TOFF012 = run b0
  where
  b0 : Chain (S1 ∷ CS13⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S1 ∷ CS13⁻ ∷ [])
  b0 = at 1 2 (CS03 ∷ CS13⁻ ∷ []) (lem-pass-CSd13-vs-CS03) ▸
       at 0 2 (CS03 ∷ S1 ∷ []) (sym lem-pass-CS03-vs-S1) ▸
       at 2 2 (Toff012 ∷ CS13⁻ ∷ []) (lem-pass-CSd13-vs-TOFF012) ▸
       at 1 2 (Toff012 ∷ S1 ∷ []) (win 3 0 complete₃ ((S ↑) • Toff) (Toff • (S ↑)) tt tt Eq.refl) ▸
       at 3 2 (CS03⁻ ∷ CS13⁻ ∷ []) (lem-pass-CSd13-vs-CSd03) ▸
       at 2 2 (CS03⁻ ∷ S1 ∷ []) (sym lem-pass-CSd03-vs-S1) ▸
       at 4 2 (Toff012 ∷ CS13⁻ ∷ []) (lem-pass-CSd13-vs-TOFF012) ▸
       at 3 2 (Toff012 ∷ S1 ∷ []) (win 3 0 complete₃ ((S ↑) • Toff) (Toff • (S ↑)) tt tt Eq.refl) ▸ done


-- pass [CS03 TOFF012 CSd03 TOFF012] [S1 CSd13]: 1 steps
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-S1-CSd13 : ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S1 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ CS13⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-S1-CSd13 = run b0
  where
  b0 : Chain (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S1 ∷ CS13⁻ ∷ []) (S1 ∷ CS13⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ [])
  b0 = at 0 6 (S1 ∷ CS13⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (sym lem-pass-S1-CSd13-vs-CS03-TOFF012-CSd03-TOFF012) ▸ done


-- pass [X3 CS03 TOFF012 CSd03 TOFF012 X3] [CS13]: 5 steps
lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-CS13 : ⟪ (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-CS13 = run b0
  where
  b0 : Chain (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS13 ∷ []) (CS13 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ [])
  b0 = at 5 2 (S1 ∷ CS13⁻ ∷ X3 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑)) (S • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 1 6 (S1 ∷ CS13⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-S1-CSd13) ▸
       at 0 2 (S1 ∷ X3 ∷ []) (sym (low-comm ((S ↑)) ((X ↑)))) ▸
       at 1 2 (S1⁻ ∷ CS13 ∷ X3 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((S • S • S) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 0 3 (CS13 ∷ []) (win 0 3 complete₃ (S • (S • S • S) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸ done


-- pass [CS13] [X3 CS03 TOFF012 CSd03 TOFF012 X3]: 1 steps
lem-pass-CS13-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 : ⟪ (CS13 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS13 ∷ []) ⟫ʷ
lem-pass-CS13-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 = run b0
  where
  b0 : Chain (CS13 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS13 ∷ [])
  b0 = at 0 7 (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS13 ∷ []) (sym lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-CS13) ▸ done


-- pass [CS13 TOFF102 CSd13 TOFF102] [X3 CS03 TOFF012 CSd03 TOFF012 X3]: 9 steps
lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 : ⟪ (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) ⟫ʷ
lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 = trans (run b0) (run b1)
  where
  b0 : Chain (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) (CS13 ∷ CS13⁻ ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ [])
  b0 = at 10 0 (Toff102 ∷ Toff102 ∷ []) (win 3 0 complete₃ (ε) ((K ↑ • CCZ • K ↑ • iI) • (K ↑ • CCZ • K ↑ • iI)) tt tt Eq.refl) ▸
       at 11 0 (CS13 ∷ CS13⁻ ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) tt tt Eq.refl) ▸
       at 12 0 (Toff102 ∷ Toff102 ∷ []) (win 3 0 complete₃ (ε) ((K ↑ • CCZ • K ↑ • iI) • (K ↑ • CCZ • K ↑ • iI)) tt tt Eq.refl) ▸
       at 13 0 (CS13⁻ ∷ CS13 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 4 10 (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) (sym lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3) ▸
       at 3 2 [] (win 3 0 complete₃ ((K ↑ • CCZ • K ↑ • iI) • (K ↑ • CCZ • K ↑ • iI)) (ε) tt tt Eq.refl) ▸
       at 2 2 [] (win 0 3 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CS • Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ ((K ↑ • CCZ • K ↑ • iI) • (K ↑ • CCZ • K ↑ • iI)) (ε) tt tt Eq.refl) ▸ done

  b1 : Chain (CS13 ∷ CS13⁻ ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ [])
  b1 = at 0 2 [] (win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- pass [CS13 TOFF102 CSd13 TOFF102] [X3 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X3]: 7 steps
lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 : ⟪ (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) ⟫ʷ
lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 = run b0
  where
  b0 : Chain (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ []) (X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ [])
  b0 = at 4 10 (X3 ∷ CS03 ∷ X3 ∷ X3 ∷ CK30 ∷ X3 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) (lem-ca-split-Gad⟨t≡0-W≡⟨3⟩-d≡SK-e≡-1⟩-3) ▸
       at 0 7 (X3 ∷ CS03 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (sym lem-pass-X3-CS30-X3-vs-CS13-TOFF102-CSd13-TOFF102) ▸
       at 3 7 (X3 ∷ CK30 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (sym lem-pass-X3-CK30-X3-vs-CS13-TOFF102-CSd13-TOFF102) ▸
       at 6 10 (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3) ▸
       at 12 7 (X3 ∷ CK30⁻ ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (sym lem-pass-X3-CKd30-X3-vs-CS13-TOFF102-CSd13-TOFF102) ▸
       at 15 7 (X3 ∷ CS03⁻ ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (sym lem-pass-X3-CSd30-X3-vs-CS13-TOFF102-CSd13-TOFF102) ▸
       at 0 18 (X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ []) (sym lem-ca-split-Gad⟨t≡0-W≡⟨3⟩-d≡SK-e≡-1⟩-3) ▸ done


-- pass [Sd1 Kd1 S1 S1 CS13 TOFF102 CSd13 TOFF102 Sd1 Sd1 K1 S1] [X3 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X3]: 11 steps
lem-pass-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 : ⟪ (S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ []) ⟫ʷ
lem-pass-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 = trans (run b0) (run b1)
  where
  b0 : Chain (S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ []) (CS13⁻ ∷ CK31⁻ ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ CS13⁻ ∷ CS13⁻ ∷ CK31 ∷ CS13 ∷ [])
  b0 = at 0 12 (CS13⁻ ∷ CK31⁻ ∷ CS13 ∷ CS13 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ CS13⁻ ∷ CS13⁻ ∷ CK31 ∷ CS13 ∷ []) (lem-ca-split-Gad⟨t≡1-W≡⟨⟩-d≡SdKdSS-e≡-1⟩-3) ▸
       at 11 11 (X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ CS13 ∷ []) (lem-pass-CS31-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3) ▸
       at 10 11 (X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ CK31 ∷ []) (lem-pass-CK31-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3) ▸
       at 9 11 (X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ CS13⁻ ∷ []) (lem-pass-CSd31-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3) ▸
       at 8 11 (X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ CS13⁻ ∷ []) (lem-pass-CSd31-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3) ▸
       at 4 14 (X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3) ▸
       at 3 11 (X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ CS13 ∷ []) (lem-pass-CS31-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3) ▸
       at 2 11 (X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ CS13 ∷ []) (lem-pass-CS31-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3) ▸ done

  b1 : Chain (CS13⁻ ∷ CK31⁻ ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ CS13⁻ ∷ CS13⁻ ∷ CK31 ∷ CS13 ∷ []) (X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ [])
  b1 = at 1 11 (X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ CK31⁻ ∷ []) (lem-pass-CKd31-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3) ▸
       at 0 11 (X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ CS13⁻ ∷ []) (lem-pass-CSd31-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3) ▸
       at 10 12 (S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ []) (sym lem-ca-split-Gad⟨t≡1-W≡⟨⟩-d≡SdKdSS-e≡-1⟩-3) ▸ done


-- ca-split Gad(t=1, W=(), d=SdKdSS, e=-1) 2: 7 steps
lem-ca-split-Gad⟨t≡1-W≡⟨⟩-d≡SdKdSS-e≡-1⟩-2 : ⟪ (S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ CK21⁻ ∷ CS12 ∷ CS12 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ CS12⁻ ∷ CS12⁻ ∷ CK21 ∷ CS12 ∷ []) ⟫ʷ
lem-ca-split-Gad⟨t≡1-W≡⟨⟩-d≡SdKdSS-e≡-1⟩-2 = run b0
  where
  b0 : Chain (S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ []) (CS12⁻ ∷ CK21⁻ ∷ CS12 ∷ CS12 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ CS12⁻ ∷ CS12⁻ ∷ CK21 ∷ CS12 ∷ [])
  b0 = at 0 4 (CS12⁻ ∷ CK21⁻ ∷ CS12 ∷ CS12 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ []) (win 3 0 complete₃ (((S • S • S) ↑) • ((K • iI) ↑) • (S ↑) • (S ↑)) (((CS • CS • CS) ↑) • ((S ↑ • CK₁₀) ↑) • (CS ↑) • (CS ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 20 4 (X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ CS12⁻ ∷ CS12⁻ ∷ CK21 ∷ CS12 ∷ []) (win 3 0 complete₃ (((S • S • S) ↑) • ((S • S • S) ↑) • (K ↑) • (S ↑)) ((X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • ((CS • CS • CS) ↑) • (CK₁₀ ↑) • (CS ↑)) tt tt Eq.refl) ▸
       at 13 7 (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CS12 ∷ X2 ∷ []) (lem-pass-X2-CS21-X2-vs-CS13-TOFF102-CSd13-TOFF102) ▸
       at 10 7 (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CS12 ∷ X2 ∷ []) (lem-pass-X2-CS21-X2-vs-CS13-TOFF102-CSd13-TOFF102) ▸
       at 7 7 (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (lem-pass-X2-CKd21-X2-vs-CS13-TOFF102-CSd13-TOFF102) ▸
       at 4 7 (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) (lem-pass-X2-CSd21-X2-vs-CS13-TOFF102-CSd13-TOFF102) ▸
       at 8 24 [] (win 3 0 complete₃ ((X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑)) (ε) tt tt Eq.refl) ▸ done


-- pass [CS03] [CS13 X2 TOFF102 X2 CSd13 X2 TOFF102 X2]: 26 steps
lem-pass-CS03-vs-CS13-X2-TOFF102-X2-CSd13-X2-TOFF102-X2 : ⟪ (CS03 ∷ CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CS03-vs-CS13-X2-TOFF102-X2-CSd13-X2-TOFF102-X2 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (CS03 ∷ CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ []) (CS13 ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ [])
  b0 = at 0 2 (CS13 ∷ CS03 ∷ []) (sym lem-pass-CS13-vs-CS03) ▸
       at 2 3 (CX01 ∷ Toff102 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑)) (CX₀₁ • (K ↑ • CCZ • K ↑ • iI)) tt tt Eq.refl) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 2 2 (CX01 ∷ CS02 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • CX₀₁) (CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 1 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b1 : Chain (CS13 ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ []) (CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13⁻ ∷ CS03 ∷ CX01 ∷ Sw23 ∷ Sw23 ∷ Toff102 ∷ [])
  b1 = at 4 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 2 2 (Toff102 ∷ CS03 ∷ []) (sym lem-pass-TOFF102-vs-CS03) ▸
       at 1 2 (X2 ∷ Toff102 ∷ X2 ∷ []) (win 3 0 complete₃ (CX₀₁ • (K ↑ • CCZ • K ↑ • iI)) ((X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 4 2 (CS13⁻ ∷ CS03 ∷ []) (sym lem-pass-CSd13-vs-CS03) ▸
       at 6 3 (CX01 ∷ Toff102 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑)) (CX₀₁ • (K ↑ • CCZ • K ↑ • iI)) tt tt Eq.refl) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b2 : Chain (CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13⁻ ∷ CS03 ∷ CX01 ∷ Sw23 ∷ Sw23 ∷ Toff102 ∷ []) (CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Toff102 ∷ [])
  b2 = at 6 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 6 2 (CX01 ∷ CS02 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • CX₀₁) (CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 6 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b3 : Chain (CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Toff102 ∷ []) (CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ CS03 ∷ [])
  b3 = at 6 2 (Toff102 ∷ CS03 ∷ []) (sym lem-pass-TOFF102-vs-CS03) ▸
       at 5 2 (X2 ∷ Toff102 ∷ X2 ∷ []) (win 3 0 complete₃ (CX₀₁ • (K ↑ • CCZ • K ↑ • iI)) ((X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑)) tt tt Eq.refl) ▸ done


-- pass [TOFF012] [CS13 X2 TOFF102 X2 CSd13 X2 TOFF102 X2]: 4 steps
lem-pass-TOFF012-vs-CS13-X2-TOFF102-X2-CSd13-X2-TOFF102-X2 : ⟪ (Toff012 ∷ CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ Toff012 ∷ []) ⟫ʷ
lem-pass-TOFF012-vs-CS13-X2-TOFF102-X2-CSd13-X2-TOFF102-X2 = run b0
  where
  b0 : Chain (Toff012 ∷ CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ []) (CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ Toff012 ∷ [])
  b0 = at 0 2 (CS13 ∷ Toff012 ∷ []) (lem-pass-TOFF012-vs-CS13) ▸
       at 1 4 (X2 ∷ Toff102 ∷ X2 ∷ Toff012 ∷ []) (lem-pass-TOFF012-vs-X2-TOFF102-X2) ▸
       at 4 2 (CS13⁻ ∷ Toff012 ∷ []) (lem-pass-TOFF012-vs-CSd13) ▸
       at 5 4 (X2 ∷ Toff102 ∷ X2 ∷ Toff012 ∷ []) (lem-pass-TOFF012-vs-X2-TOFF102-X2) ▸ done


-- pass [CSd03] [CS13 X2 TOFF102 X2 CSd13 X2 TOFF102 X2]: 26 steps
lem-pass-CSd03-vs-CS13-X2-TOFF102-X2-CSd13-X2-TOFF102-X2 : ⟪ (CS03⁻ ∷ CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-pass-CSd03-vs-CS13-X2-TOFF102-X2-CSd13-X2-TOFF102-X2 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (CS03⁻ ∷ CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ []) (CS13 ∷ CX01 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ [])
  b0 = at 0 2 (CS13 ∷ CS03⁻ ∷ []) (sym lem-pass-CS13-vs-CSd03) ▸
       at 2 3 (CX01 ∷ Toff102 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑)) (CX₀₁ • (K ↑ • CCZ • K ↑ • iI)) tt tt Eq.refl) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 1 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 2 2 (CX01 ∷ CS02⁻ ∷ []) (win 3 0 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • CX₀₁) (CX₀₁ • (Swap ↑ • (CS • CS • CS) • Swap ↑)) tt tt Eq.refl) ▸
       at 1 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b1 : Chain (CS13 ∷ CX01 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ []) (CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13⁻ ∷ CS03⁻ ∷ CX01 ∷ Sw23 ∷ Sw23 ∷ Toff102 ∷ [])
  b1 = at 4 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 2 2 (Toff102 ∷ CS03⁻ ∷ []) (sym lem-pass-TOFF102-vs-CSd03) ▸
       at 1 2 (X2 ∷ Toff102 ∷ X2 ∷ []) (win 3 0 complete₃ (CX₀₁ • (K ↑ • CCZ • K ↑ • iI)) ((X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 4 2 (CS13⁻ ∷ CS03⁻ ∷ []) (sym lem-pass-CSd13-vs-CSd03) ▸
       at 6 3 (CX01 ∷ Toff102 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑)) (CX₀₁ • (K ↑ • CCZ • K ↑ • iI)) tt tt Eq.refl) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b2 : Chain (CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13⁻ ∷ CS03⁻ ∷ CX01 ∷ Sw23 ∷ Sw23 ∷ Toff102 ∷ []) (CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13⁻ ∷ CX01 ∷ CS03⁻ ∷ Toff102 ∷ [])
  b2 = at 6 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 5 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 6 2 (CX01 ∷ CS02⁻ ∷ []) (win 3 0 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • CX₀₁) (CX₀₁ • (Swap ↑ • (CS • CS • CS) • Swap ↑)) tt tt Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 6 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b3 : Chain (CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13⁻ ∷ CX01 ∷ CS03⁻ ∷ Toff102 ∷ []) (CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ CS03⁻ ∷ [])
  b3 = at 6 2 (Toff102 ∷ CS03⁻ ∷ []) (sym lem-pass-TOFF102-vs-CSd03) ▸
       at 5 2 (X2 ∷ Toff102 ∷ X2 ∷ []) (win 3 0 complete₃ (CX₀₁ • (K ↑ • CCZ • K ↑ • iI)) ((X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑)) tt tt Eq.refl) ▸ done

