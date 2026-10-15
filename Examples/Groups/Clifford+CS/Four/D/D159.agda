{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D159 where

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
open import Examples.Groups.Clifford+CS.Four.D.D008 using (lem-S2)
open import Examples.Groups.Clifford+CS.Four.D.D081 using (lem-pass-X1-CK10-X1-vs-CS03-TOFF012-CSd03-TOFF012 ; lem-pass-X1-CS10-X1-vs-CS03-TOFF012-CSd03-TOFF012)
open import Examples.Groups.Clifford+CS.Four.D.D125 using (lem-pass-CS23-vs-CSd03 ; lem-pass-CS23-vs-S0 ; lem-pass-CS23-vs-TOFF012)
open import Examples.Groups.Clifford+CS.Four.D.D126 using (lem-pass-CS23-vs-CS03 ; lem-pass-CS23-vs-Sd0)
open import Examples.Groups.Clifford+CS.Four.D.D151 using (lem-b2g-1111R0 ; lem-ca-split-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩-1)
open import Examples.Groups.Clifford+CS.Four.D.D152 using (lem-ca-split-Gad⟨t≡0-W≡⟨1-2-3⟩-d≡SdKdSS-e≡-1⟩-1 ; lem-pass-X1-CKd10-X1-vs-CS03-TOFF012-CSd03-TOFF012 ; lem-pass-X1-CSd10-X1-vs-CS03-TOFF012-CSd03-TOFF012)
open import Examples.Groups.Clifford+CS.Four.D.D158 using (lem-pass-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3-vs-TOFF013-CS02-TOFF013-CSd02)
-- pass [TOFF013 CS02 TOFF013 CSd02] [X1 X2 X3 CS03 TOFF012 CSd03 TOFF012 X1 X2 X3]: 1 steps
lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 : ⟪ (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) ⟫ʷ
lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 = run b0
  where
  b0 : Chain (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ []) (X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ [])
  b0 = at 0 14 (X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (sym lem-pass-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3-vs-TOFF013-CS02-TOFF013-CSd02) ▸ done


-- pass [TOFF012 CS03 TOFF012 CSd03] [X1 X2 X3 CS03 TOFF012 CSd03 TOFF012 X1 X2 X3]: 3 steps
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 : ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 = run b0
  where
  b0 : Chain (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ []) (X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ [])
  b0 = at 0 4 (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (lem-S2) ▸
       at 0 14 (X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3) ▸
       at 10 4 (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (sym lem-S2) ▸ done


-- pass [CS03 TOFF012 CSd03 TOFF012] [X1 X2 X3 CS03 TOFF012 CSd03 TOFF012 X1 X2 X3]: 33 steps
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 : ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (run b4))))
  where
  b0 : Chain (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ CS03⁻ ∷ Toff012 ∷ [])
  b0 = at 14 0 (Toff012 ∷ Toff012 ∷ []) (win 3 0 complete₃ (ε) (Toff • Toff) tt tt Eq.refl) ▸
       at 15 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 16 0 (CS02 ∷ CS02⁻ ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) tt tt Eq.refl) ▸
       at 17 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 15 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 18 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 16 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 17 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b1 : Chain (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ [])
  b1 = at 16 0 (Toff012 ∷ Toff012 ∷ []) (win 3 0 complete₃ (ε) (Toff • Toff) tt tt Eq.refl) ▸
       at 17 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 18 0 (CS02⁻ ∷ CS02 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 19 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 17 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 20 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 18 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 19 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b2 : Chain (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ Sw23 ∷ Sw23 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ [])
  b2 = at 4 14 (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ []) (sym lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3) ▸
       at 3 2 [] (win 3 0 complete₃ (Toff • Toff) (ε) tt tt Eq.refl) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 2 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 3 2 [] (win 3 0 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CS • Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b3 : Chain (CS03 ∷ Toff012 ∷ Sw23 ∷ Sw23 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (Sw23 ∷ Sw23 ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ [])
  b3 = at 2 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ (Toff • Toff) (ε) tt tt Eq.refl) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b4 : Chain (Sw23 ∷ Sw23 ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ [])
  b4 = at 0 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- pass [CS03 TOFF012 CSd03 TOFF012] [X1 X2 X3 Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0 X1 X2 X3]: 11 steps
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X1-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X1-X2-X3 : ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X1-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X1-X2-X3 = trans (run b0) (run b1)
  where
  b0 : Chain (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X1 ∷ X2 ∷ X3 ∷ []) (X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ [])
  b0 = at 4 18 (X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ []) (lem-ca-split-Gad⟨t≡0-W≡⟨1-2-3⟩-d≡SdKdSS-e≡-1⟩-1) ▸
       at 0 7 (X1 ∷ CS01⁻ ∷ X1 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (sym lem-pass-X1-CSd10-X1-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 3 7 (X1 ∷ CK10⁻ ∷ X1 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (sym lem-pass-X1-CKd10-X1-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 6 7 (X1 ∷ CS01 ∷ X1 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (sym lem-pass-X1-CS10-X1-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 9 7 (X1 ∷ CS01 ∷ X1 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (sym lem-pass-X1-CS10-X1-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 12 14 (X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3) ▸
       at 22 7 (X1 ∷ CS01⁻ ∷ X1 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (sym lem-pass-X1-CSd10-X1-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 25 7 (X1 ∷ CS01⁻ ∷ X1 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (sym lem-pass-X1-CSd10-X1-vs-CS03-TOFF012-CSd03-TOFF012) ▸ done

  b1 : Chain (X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ []) (X1 ∷ X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ [])
  b1 = at 28 7 (X1 ∷ CK10 ∷ X1 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (sym lem-pass-X1-CK10-X1-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 31 7 (X1 ∷ CS01 ∷ X1 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (sym lem-pass-X1-CS10-X1-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 0 34 (X1 ∷ X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X1 ∷ X2 ∷ X3 ∷ []) (sym lem-ca-split-Gad⟨t≡0-W≡⟨1-2-3⟩-d≡SdKdSS-e≡-1⟩-1) ▸ done


-- pass [X1 CSd10 X1] [X2 X3 Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0 X2 X3]: 9 steps
lem-pass-X1-CSd10-X1-vs-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2-X3 : ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ X3 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CSd10-X1-vs-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2-X3 = trans (run b0) (run b1)
  where
  b0 : Chain (X1 ∷ CS01⁻ ∷ X1 ∷ X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ X3 ∷ [])
  b0 = at 0 4 (X2 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑) • (CS • CS • CS) • (X ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑) • (CS • CS • CS) • (X ↑)) tt tt Eq.refl) ▸
       at 1 4 (X3 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (win 2 1 complete₃ ((X ↑) • (CS • CS • CS) • (X ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑) • (CS • CS • CS) • (X ↑)) tt tt Eq.refl) ▸
       at 2 7 (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑) • (CS • CS • CS) • (X ↑) • (S • S • S) • (K • iI) • S • S) ((S • S • S) • (K • iI) • S • S • (X ↑) • (CS • CS • CS) • (X ↑) • (X ↑) • CK₁₀ • (X ↑) • (X ↑) • (CS • CS • CS) • (X ↑)) tt tt Eq.refl) ▸
       at 12 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (lem-pass-X1-CSd10-X1-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 9 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CK10 ∷ X1 ∷ []) (lem-pass-X1-CK10-X1-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 6 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (lem-pass-X1-CSd10-X1-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 10 13 (S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑) • (CS • CS • CS) • (X ↑) • (X ↑) • CK₁₀ • (X ↑) • (X ↑) • (CS • CS • CS) • (X ↑) • (S • S • S) • (S • S • S) • K • S) ((S • S • S) • (S • S • S) • K • S • (X ↑) • (CS • CS • CS) • (X ↑)) tt tt Eq.refl) ▸
       at 14 4 (X2 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑) • (CS • CS • CS) • (X ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑) • (CS • CS • CS) • (X ↑)) tt tt Eq.refl) ▸ done

  b1 : Chain (X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ X3 ∷ []) (X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ X3 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ [])
  b1 = at 15 4 (X3 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (win 2 1 complete₃ ((X ↑) • (CS • CS • CS) • (X ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑) • (CS • CS • CS) • (X ↑)) tt tt Eq.refl) ▸ done


-- pass [CSd10] [X1 X2 X3 Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0 X1 X2 X3]: 7 steps
lem-pass-CSd10-vs-X1-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X1-X2-X3 : ⟪ (CS01⁻ ∷ X1 ∷ X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X1 ∷ X2 ∷ X3 ∷ CS01⁻ ∷ []) ⟫ʷ
lem-pass-CSd10-vs-X1-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X1-X2-X3 = run b0
  where
  b0 : Chain (CS01⁻ ∷ X1 ∷ X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X1 ∷ X2 ∷ X3 ∷ []) (X1 ∷ X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X1 ∷ X2 ∷ X3 ∷ CS01⁻ ∷ [])
  b0 = at 0 2 (X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (win 3 0 complete₃ ((CS • CS • CS) • (X ↑)) ((X ↑) • (X ↑) • (CS • CS • CS) • (X ↑)) tt tt Eq.refl) ▸
       at 18 2 (X2 ∷ X1 ∷ []) (low-comm ((X ↑)) (X)) ▸
       at 19 2 (X3 ∷ X1 ∷ []) (low-comm ((X ↑)) ((X ↑))) ▸
       at 1 19 (X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ X3 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (lem-pass-X1-CSd10-X1-vs-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2-X3) ▸
       at 17 4 (X1 ∷ CS01⁻ ∷ []) (win 3 0 complete₃ ((X ↑) • (CS • CS • CS) • (X ↑) • (X ↑)) ((X ↑) • (CS • CS • CS)) tt tt Eq.refl) ▸
       at 16 2 (X1 ∷ X3 ∷ []) (sym (low-comm ((X ↑)) ((X ↑)))) ▸
       at 15 2 (X1 ∷ X2 ∷ []) (sym (low-comm ((X ↑)) (X))) ▸ done


-- pass [X1 CKd10 X1] [X2 X3 Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0 X2 X3]: 11 steps
lem-pass-X1-CKd10-X1-vs-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2-X3 : ⟪ (X1 ∷ CK10⁻ ∷ X1 ∷ X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ X3 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CKd10-X1-vs-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2-X3 = trans (run b0) (run b1)
  where
  b0 : Chain (X1 ∷ CK10⁻ ∷ X1 ∷ X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ X3 ∷ [])
  b0 = at 0 4 (X2 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑)) tt tt Eq.refl) ▸
       at 1 4 (X3 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) (win 2 1 complete₃ ((X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑)) tt tt Eq.refl) ▸
       at 2 7 (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑) • (S ↑ • CK₁₀) • (X ↑) • (S • S • S) • (K • iI) • S • S) ((S • S • S) • (K • iI) • S • S • (X ↑) • (CS • CS • CS) • (X ↑) • (X ↑) • CK₁₀ • (X ↑) • (X ↑) • CS • (X ↑) • (X ↑) • CS • (X ↑) • (X ↑) • CK₁₀ • (X ↑)) tt tt Eq.refl) ▸
       at 18 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CK10 ∷ X1 ∷ []) (lem-pass-X1-CK10-X1-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 15 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CS01 ∷ X1 ∷ []) (lem-pass-X1-CS10-X1-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 12 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CS01 ∷ X1 ∷ []) (lem-pass-X1-CS10-X1-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 9 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CK10 ∷ X1 ∷ []) (lem-pass-X1-CK10-X1-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 6 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (lem-pass-X1-CSd10-X1-vs-CS03-TOFF012-CSd03-TOFF012) ▸ done

  b1 : Chain (X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ X3 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ [])
  b1 = at 10 19 (S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑) • (CS • CS • CS) • (X ↑) • (X ↑) • CK₁₀ • (X ↑) • (X ↑) • CS • (X ↑) • (X ↑) • CS • (X ↑) • (X ↑) • CK₁₀ • (X ↑) • (S • S • S) • (S • S • S) • K • S) ((S • S • S) • (S • S • S) • K • S • (X ↑) • (S ↑ • CK₁₀) • (X ↑)) tt tt Eq.refl) ▸
       at 14 4 (X2 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑)) tt tt Eq.refl) ▸
       at 15 4 (X3 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) (win 2 1 complete₃ ((X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑)) tt tt Eq.refl) ▸ done


-- pass [CKd10] [X1 X2 X3 Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0 X1 X2 X3]: 7 steps
lem-pass-CKd10-vs-X1-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X1-X2-X3 : ⟪ (CK10⁻ ∷ X1 ∷ X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X1 ∷ X2 ∷ X3 ∷ CK10⁻ ∷ []) ⟫ʷ
lem-pass-CKd10-vs-X1-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X1-X2-X3 = run b0
  where
  b0 : Chain (CK10⁻ ∷ X1 ∷ X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X1 ∷ X2 ∷ X3 ∷ []) (X1 ∷ X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X1 ∷ X2 ∷ X3 ∷ CK10⁻ ∷ [])
  b0 = at 0 2 (X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) (win 3 0 complete₃ ((S ↑ • CK₁₀) • (X ↑)) ((X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑)) tt tt Eq.refl) ▸
       at 18 2 (X2 ∷ X1 ∷ []) (low-comm ((X ↑)) (X)) ▸
       at 19 2 (X3 ∷ X1 ∷ []) (low-comm ((X ↑)) ((X ↑))) ▸
       at 1 19 (X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ X3 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) (lem-pass-X1-CKd10-X1-vs-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2-X3) ▸
       at 17 4 (X1 ∷ CK10⁻ ∷ []) (win 3 0 complete₃ ((X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑)) ((X ↑) • (S ↑ • CK₁₀)) tt tt Eq.refl) ▸
       at 16 2 (X1 ∷ X3 ∷ []) (sym (low-comm ((X ↑)) ((X ↑)))) ▸
       at 15 2 (X1 ∷ X2 ∷ []) (sym (low-comm ((X ↑)) (X))) ▸ done


-- pass [X1 CK10 X1] [X2 X3 Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0 X2 X3]: 11 steps
lem-pass-X1-CK10-X1-vs-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2-X3 : ⟪ (X1 ∷ CK10 ∷ X1 ∷ X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ X3 ∷ X1 ∷ CK10 ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CK10-X1-vs-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2-X3 = trans (run b0) (run b1)
  where
  b0 : Chain (X1 ∷ CK10 ∷ X1 ∷ X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ X3 ∷ [])
  b0 = at 0 4 (X2 ∷ X1 ∷ CK10 ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑) • CK₁₀ • (X ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑) • CK₁₀ • (X ↑)) tt tt Eq.refl) ▸
       at 1 4 (X3 ∷ X1 ∷ CK10 ∷ X1 ∷ []) (win 2 1 complete₃ ((X ↑) • CK₁₀ • (X ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑) • CK₁₀ • (X ↑)) tt tt Eq.refl) ▸
       at 2 7 (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑) • CK₁₀ • (X ↑) • (S • S • S) • (K • iI) • S • S) ((S • S • S) • (K • iI) • S • S • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • CS • (X ↑) • (X ↑) • CS • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • CS • (X ↑)) tt tt Eq.refl) ▸
       at 18 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CS01 ∷ X1 ∷ []) (lem-pass-X1-CS10-X1-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 15 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) (lem-pass-X1-CKd10-X1-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 12 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CS01 ∷ X1 ∷ []) (lem-pass-X1-CS10-X1-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 9 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CS01 ∷ X1 ∷ []) (lem-pass-X1-CS10-X1-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 6 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) (lem-pass-X1-CKd10-X1-vs-CS03-TOFF012-CSd03-TOFF012) ▸ done

  b1 : Chain (X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ X3 ∷ X1 ∷ CK10 ∷ X1 ∷ [])
  b1 = at 10 19 (S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X1 ∷ CK10 ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • CS • (X ↑) • (X ↑) • CS • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • CS • (X ↑) • (S • S • S) • (S • S • S) • K • S) ((S • S • S) • (S • S • S) • K • S • (X ↑) • CK₁₀ • (X ↑)) tt tt Eq.refl) ▸
       at 14 4 (X2 ∷ X1 ∷ CK10 ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑) • CK₁₀ • (X ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑) • CK₁₀ • (X ↑)) tt tt Eq.refl) ▸
       at 15 4 (X3 ∷ X1 ∷ CK10 ∷ X1 ∷ []) (win 2 1 complete₃ ((X ↑) • CK₁₀ • (X ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑) • CK₁₀ • (X ↑)) tt tt Eq.refl) ▸ done


-- pass [CK10] [X1 X2 X3 Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0 X1 X2 X3]: 7 steps
lem-pass-CK10-vs-X1-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X1-X2-X3 : ⟪ (CK10 ∷ X1 ∷ X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X1 ∷ X2 ∷ X3 ∷ CK10 ∷ []) ⟫ʷ
lem-pass-CK10-vs-X1-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X1-X2-X3 = run b0
  where
  b0 : Chain (CK10 ∷ X1 ∷ X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X1 ∷ X2 ∷ X3 ∷ []) (X1 ∷ X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X1 ∷ X2 ∷ X3 ∷ CK10 ∷ [])
  b0 = at 0 2 (X1 ∷ X1 ∷ CK10 ∷ X1 ∷ []) (win 3 0 complete₃ (CK₁₀ • (X ↑)) ((X ↑) • (X ↑) • CK₁₀ • (X ↑)) tt tt Eq.refl) ▸
       at 18 2 (X2 ∷ X1 ∷ []) (low-comm ((X ↑)) (X)) ▸
       at 19 2 (X3 ∷ X1 ∷ []) (low-comm ((X ↑)) ((X ↑))) ▸
       at 1 19 (X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ X3 ∷ X1 ∷ CK10 ∷ X1 ∷ []) (lem-pass-X1-CK10-X1-vs-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2-X3) ▸
       at 17 4 (X1 ∷ CK10 ∷ []) (win 3 0 complete₃ ((X ↑) • CK₁₀ • (X ↑) • (X ↑)) ((X ↑) • CK₁₀) tt tt Eq.refl) ▸
       at 16 2 (X1 ∷ X3 ∷ []) (sym (low-comm ((X ↑)) ((X ↑)))) ▸
       at 15 2 (X1 ∷ X2 ∷ []) (sym (low-comm ((X ↑)) (X))) ▸ done


-- pass [X1 CS10 X1] [X2 X3 Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0 X2 X3]: 9 steps
lem-pass-X1-CS10-X1-vs-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2-X3 : ⟪ (X1 ∷ CS01 ∷ X1 ∷ X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ X3 ∷ X1 ∷ CS01 ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CS10-X1-vs-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2-X3 = trans (run b0) (run b1)
  where
  b0 : Chain (X1 ∷ CS01 ∷ X1 ∷ X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ X1 ∷ CS01 ∷ X1 ∷ X3 ∷ [])
  b0 = at 0 4 (X2 ∷ X1 ∷ CS01 ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑) • CS • (X ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑) • CS • (X ↑)) tt tt Eq.refl) ▸
       at 1 4 (X3 ∷ X1 ∷ CS01 ∷ X1 ∷ []) (win 2 1 complete₃ ((X ↑) • CS • (X ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑) • CS • (X ↑)) tt tt Eq.refl) ▸
       at 2 7 (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑) • CS • (X ↑) • (S • S • S) • (K • iI) • S • S) ((S • S • S) • (K • iI) • S • S • (X ↑) • CS • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • CS • (X ↑)) tt tt Eq.refl) ▸
       at 12 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CS01 ∷ X1 ∷ []) (lem-pass-X1-CS10-X1-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 9 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) (lem-pass-X1-CKd10-X1-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 6 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CS01 ∷ X1 ∷ []) (lem-pass-X1-CS10-X1-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 10 13 (S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X1 ∷ CS01 ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑) • CS • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • CS • (X ↑) • (S • S • S) • (S • S • S) • K • S) ((S • S • S) • (S • S • S) • K • S • (X ↑) • CS • (X ↑)) tt tt Eq.refl) ▸
       at 14 4 (X2 ∷ X1 ∷ CS01 ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑) • CS • (X ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑) • CS • (X ↑)) tt tt Eq.refl) ▸ done

  b1 : Chain (X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ X1 ∷ CS01 ∷ X1 ∷ X3 ∷ []) (X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ X3 ∷ X1 ∷ CS01 ∷ X1 ∷ [])
  b1 = at 15 4 (X3 ∷ X1 ∷ CS01 ∷ X1 ∷ []) (win 2 1 complete₃ ((X ↑) • CS • (X ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑) • CS • (X ↑)) tt tt Eq.refl) ▸ done


-- pass [CS10] [X1 X2 X3 Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0 X1 X2 X3]: 7 steps
lem-pass-CS10-vs-X1-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X1-X2-X3 : ⟪ (CS01 ∷ X1 ∷ X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X1 ∷ X2 ∷ X3 ∷ CS01 ∷ []) ⟫ʷ
lem-pass-CS10-vs-X1-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X1-X2-X3 = run b0
  where
  b0 : Chain (CS01 ∷ X1 ∷ X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X1 ∷ X2 ∷ X3 ∷ []) (X1 ∷ X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X1 ∷ X2 ∷ X3 ∷ CS01 ∷ [])
  b0 = at 0 2 (X1 ∷ X1 ∷ CS01 ∷ X1 ∷ []) (win 3 0 complete₃ (CS • (X ↑)) ((X ↑) • (X ↑) • CS • (X ↑)) tt tt Eq.refl) ▸
       at 18 2 (X2 ∷ X1 ∷ []) (low-comm ((X ↑)) (X)) ▸
       at 19 2 (X3 ∷ X1 ∷ []) (low-comm ((X ↑)) ((X ↑))) ▸
       at 1 19 (X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ X3 ∷ X1 ∷ CS01 ∷ X1 ∷ []) (lem-pass-X1-CS10-X1-vs-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2-X3) ▸
       at 17 4 (X1 ∷ CS01 ∷ []) (win 3 0 complete₃ ((X ↑) • CS • (X ↑) • (X ↑)) ((X ↑) • CS) tt tt Eq.refl) ▸
       at 16 2 (X1 ∷ X3 ∷ []) (sym (low-comm ((X ↑)) ((X ↑)))) ▸
       at 15 2 (X1 ∷ X2 ∷ []) (sym (low-comm ((X ↑)) (X))) ▸ done


-- pass [S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0] [X1 X2 X3 Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0 X1 X2 X3]: 7 steps
lem-pass-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-vs-X1-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X1-X2-X3 : ⟪ (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X1 ∷ X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X1 ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ
lem-pass-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-vs-X1-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X1-X2-X3 = run b0
  where
  b0 : Chain (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X1 ∷ X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X1 ∷ X2 ∷ X3 ∷ []) (X1 ∷ X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X1 ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ [])
  b0 = at 0 8 (CS01 ∷ CK10 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ CK10⁻ ∷ CS01⁻ ∷ []) (lem-ca-split-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩-1) ▸
       at 7 19 (X1 ∷ X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X1 ∷ X2 ∷ X3 ∷ CS01⁻ ∷ []) (lem-pass-CSd10-vs-X1-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X1-X2-X3) ▸
       at 6 19 (X1 ∷ X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X1 ∷ X2 ∷ X3 ∷ CK10⁻ ∷ []) (lem-pass-CKd10-vs-X1-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X1-X2-X3) ▸
       at 2 22 (X1 ∷ X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X1-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X1-X2-X3) ▸
       at 1 19 (X1 ∷ X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X1 ∷ X2 ∷ X3 ∷ CK10 ∷ []) (lem-pass-CK10-vs-X1-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X1-X2-X3) ▸
       at 0 19 (X1 ∷ X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X1 ∷ X2 ∷ X3 ∷ CS01 ∷ []) (lem-pass-CS10-vs-X1-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X1-X2-X3) ▸
       at 18 8 (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (sym lem-ca-split-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩-1) ▸ done


-- cls 0000R0 1111R0 = 1111R0 0000R0: 3 steps
lem-cls-0000R0-1111R0-≡-1111R0-0000R0 : ⟪ (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X0 ∷ X1 ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X0 ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X0 ∷ X1 ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ
lem-cls-0000R0-1111R0-≡-1111R0-0000R0 = run b0
  where
  b0 : Chain (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X0 ∷ X1 ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X0 ∷ X1 ∷ X2 ∷ X3 ∷ []) (X0 ∷ X1 ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X0 ∷ X1 ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ [])
  b0 = at 8 16 (X1 ∷ X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X1 ∷ X2 ∷ X3 ∷ []) (lem-b2g-1111R0) ▸
       at 0 26 (X1 ∷ X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X1 ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (lem-pass-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-vs-X1-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X1-X2-X3) ▸
       at 0 18 (X0 ∷ X1 ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X0 ∷ X1 ∷ X2 ∷ X3 ∷ []) (sym lem-b2g-1111R0) ▸ done


-- pass [CS23] [S0 CSd03 TOFF012 Sd0 CS03 TOFF012]: 6 steps
lem-pass-CS23-vs-S0-CSd03-TOFF012-Sd0-CS03-TOFF012 : ⟪ (CS23 ∷ S0 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ CS23 ∷ []) ⟫ʷ
lem-pass-CS23-vs-S0-CSd03-TOFF012-Sd0-CS03-TOFF012 = run b0
  where
  b0 : Chain (CS23 ∷ S0 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ []) (S0 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ CS23 ∷ [])
  b0 = at 0 2 (S0 ∷ CS23 ∷ []) (lem-pass-CS23-vs-S0) ▸
       at 1 2 (CS03⁻ ∷ CS23 ∷ []) (lem-pass-CS23-vs-CSd03) ▸
       at 2 2 (Toff012 ∷ CS23 ∷ []) (lem-pass-CS23-vs-TOFF012) ▸
       at 3 2 (S0⁻ ∷ CS23 ∷ []) (lem-pass-CS23-vs-Sd0) ▸
       at 4 2 (CS03 ∷ CS23 ∷ []) (lem-pass-CS23-vs-CS03) ▸
       at 5 2 (Toff012 ∷ CS23 ∷ []) (lem-pass-CS23-vs-TOFF012) ▸ done


-- pass [S0] [CSd23]: 1 steps
lem-pass-S0-vs-CSd23 : ⟪ (S0 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ S0 ∷ []) ⟫ʷ
lem-pass-S0-vs-CSd23 = run b0
  where
  b0 : Chain (S0 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ S0 ∷ [])
  b0 = at 0 2 (CS23⁻ ∷ S0 ∷ []) (win 1 2 complete₃ (S • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • S) tt tt Eq.refl) ▸ done

