{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D043 where

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
open import Examples.Groups.Clifford+CS.Four.D.D015 using (lem-PP-flip)
open import Examples.Groups.Clifford+CS.Four.D.D023 using (lem-pass-CCZ012-vs-CS12 ; lem-pass-CCZ012-vs-CZ12)
open import Examples.Groups.Clifford+CS.Four.D.D024 using (lem-pass-S0-vs-CS03 ; lem-pass-S0-vs-CSd03 ; lem-pass-S0-vs-TOFF012-CS03-TOFF012-CSd03)
open import Examples.Groups.Clifford+CS.Four.D.D030 using (lem-pass-CCZ012-vs-CSd03)
open import Examples.Groups.Clifford+CS.Four.D.D040 using (lem-pass-CS12-vs-CSd03)
open import Examples.Groups.Clifford+CS.Four.D.D041 using (lem-C⟨U'⟩≡eps ; lem-ROT-gad)
open import Examples.Groups.Clifford+CS.Four.D.D042 using (lem-C⟨SU'S⟩ ; lem-CAw-KdSK-Gad⟨t≡0-W≡⟨⟩-d≡1-e≡1⟩ ; lem-cocycle-KdSK∣SKdSK ; lem-cocycle-S∣KdSK)
-- C(U'SU'): 12 steps
lem-C⟨U'SU'⟩ : ⟪ (Toff012 ∷ CK30⁻ ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30⁻ ∷ CS03 ∷ CK30 ∷ Toff012 ∷ CK30⁻ ∷ CS03⁻ ∷ CK30 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CK30 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ S0 ∷ []) ⟫ʷ
lem-C⟨U'SU'⟩ = trans (run b0) (run b1)
  where
  b0 : Chain (Toff012 ∷ CK30⁻ ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30⁻ ∷ CS03 ∷ CK30 ∷ Toff012 ∷ CK30⁻ ∷ CS03⁻ ∷ CK30 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CK30 ∷ []) (CK30⁻ ∷ CS03 ∷ CK30 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ CK30⁻ ∷ CS03⁻ ∷ CK30 ∷ [])
  b0 = at 0 16 (Toff012 ∷ CK30⁻ ∷ CS03 ∷ CK30 ∷ Toff012 ∷ CK30⁻ ∷ CS03⁻ ∷ CK30 ∷ CK30⁻ ∷ CS03 ∷ CK30 ∷ Toff012 ∷ CS03 ∷ CK30⁻ ∷ CS03 ∷ CK30 ∷ Toff012 ∷ CK30⁻ ∷ CS03⁻ ∷ CK30 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CK30 ∷ []) (lem-cocycle-KdSK∣SKdSK) ▸
       at 0 8 [] (lem-C⟨U'⟩≡eps) ▸
       at 3 10 (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CS03 ∷ Toff012 ∷ CK30⁻ ∷ CS03 ∷ CK30 ∷ Toff012 ∷ CK30⁻ ∷ CS03⁻ ∷ CK30 ∷ CS03⁻ ∷ []) (lem-cocycle-S∣KdSK) ▸
       at 8 8 [] (lem-C⟨U'⟩≡eps) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 8 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (CK30⁻ ∷ CS03 ∷ CK30 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ CK30⁻ ∷ CS03⁻ ∷ CK30 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ S0 ∷ [])
  b1 = at 9 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 8 2 [] (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 7 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 0 10 (S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ S0 ∷ []) (lem-CAw-KdSK-Gad⟨t≡0-W≡⟨⟩-d≡1-e≡1⟩) ▸ done


-- REL0: 56 steps
lem-REL0 : ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ S0 ∷ []) ⟫ʷ
lem-REL0 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (run b6))))))
  where
  b0 : Chain (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ []) (Toff012 ∷ CS03 ∷ CK30⁻ ∷ Sw23 ∷ CS02 ∷ CK20 ∷ CS02 ∷ Sw23 ∷ Toff012 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CK30 ∷ CS03⁻ ∷ [])
  b0 = at 0 12 (Toff012 ∷ CS03 ∷ CK30⁻ ∷ CS03 ∷ CK30 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CK30 ∷ CS03⁻ ∷ []) (sym lem-C⟨SU'S⟩) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 4 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b1 : Chain (Toff012 ∷ CS03 ∷ CK30⁻ ∷ Sw23 ∷ CS02 ∷ CK20 ∷ CS02 ∷ Sw23 ∷ Toff012 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CK30 ∷ CS03⁻ ∷ []) (Toff012 ∷ CK30⁻ ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ CK20 ∷ CS02 ∷ CK20⁻ ∷ CS02 ∷ CK20 ∷ Sw23 ∷ Toff012 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CK30 ∷ CS03⁻ ∷ [])
  b1 = at 2 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 2 5 (CK20⁻ ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20⁻ ∷ CS02 ∷ CK20 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑)) tt tt Eq.refl) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 3 (CK30⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b2 : Chain (Toff012 ∷ CK30⁻ ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ CK20 ∷ CS02 ∷ CK20⁻ ∷ CS02 ∷ CK20 ∷ Sw23 ∷ Toff012 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CK30 ∷ CS03⁻ ∷ []) (Toff012 ∷ CK30⁻ ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30⁻ ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Toff012 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CK30 ∷ CS03⁻ ∷ [])
  b2 = at 2 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 3 (CK30 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 4 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 3 (CK30⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b3 : Chain (Toff012 ∷ CK30⁻ ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30⁻ ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Toff012 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CK30 ∷ CS03⁻ ∷ []) (Toff012 ∷ CK30⁻ ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30⁻ ∷ CS03 ∷ CK30 ∷ Toff012 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ [])
  b3 = at 6 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 3 (CK30 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 14 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 13 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 15 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 12 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b4 : Chain (Toff012 ∷ CK30⁻ ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30⁻ ∷ CS03 ∷ CK30 ∷ Toff012 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (Toff012 ∷ CK30⁻ ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30⁻ ∷ CS03 ∷ CK30 ∷ Toff012 ∷ Sw23 ∷ CK20⁻ ∷ CS02⁻ ∷ CK20 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CK20 ∷ Sw23 ∷ [])
  b4 = at 14 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 11 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 10 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 9 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 10 5 (CK20⁻ ∷ CS02⁻ ∷ CK20 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CK20 ∷ []) (win 3 0 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑)) tt tt Eq.refl) ▸ done

  b5 : Chain (Toff012 ∷ CK30⁻ ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30⁻ ∷ CS03 ∷ CK30 ∷ Toff012 ∷ Sw23 ∷ CK20⁻ ∷ CS02⁻ ∷ CK20 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CK20 ∷ Sw23 ∷ []) (Toff012 ∷ CK30⁻ ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30⁻ ∷ CS03 ∷ CK30 ∷ Toff012 ∷ CK30⁻ ∷ CS03⁻ ∷ CK30 ∷ CS03⁻ ∷ Sw23 ∷ CK20⁻ ∷ CS02⁻ ∷ CK20 ∷ Sw23 ∷ [])
  b5 = at 11 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 9 3 (CK30⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 10 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 13 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 11 3 (CK30 ∷ []) (by-assoc Eq.refl) ▸
       at 14 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 12 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b6 : Chain (Toff012 ∷ CK30⁻ ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30⁻ ∷ CS03 ∷ CK30 ∷ Toff012 ∷ CK30⁻ ∷ CS03⁻ ∷ CK30 ∷ CS03⁻ ∷ Sw23 ∷ CK20⁻ ∷ CS02⁻ ∷ CK20 ∷ Sw23 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ S0 ∷ [])
  b6 = at 15 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 13 3 (CK30⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 16 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 14 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 17 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 15 3 (CK30 ∷ []) (by-assoc Eq.refl) ▸
       at 16 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 0 16 (S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ S0 ∷ []) (lem-C⟨U'SU'⟩) ▸ done


-- REL Sd: 5 steps
lem-REL-Sd : ⟪ (S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ
lem-REL-Sd = run b0
  where
  b0 : Chain (S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ S0 ∷ []) (S0 ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ [])
  b0 = at 5 4 (K0⁻ ∷ S0⁻ ∷ []) (win 3 0 complete₃ (S • (S • S • S) • (K • iI) • (S • S • S)) ((K • iI) • (S • S • S)) tt tt Eq.refl) ▸
       at 11 3 (S0 ∷ K0 ∷ S0 ∷ []) (win 3 0 complete₃ (S • K • S) (S • K • S) tt tt Eq.refl) ▸
       at 1 12 (S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ S0 ∷ []) (lem-REL0) ▸
       at 0 4 (S0 ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ []) (win 3 0 complete₃ ((S • S • S) • (S • S • S) • (K • iI) • (S • S • S)) (S • S • (K • iI) • (S • S • S)) tt tt Eq.refl) ▸
       at 8 4 (S0 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) (win 3 0 complete₃ (S • K • S • S) (S • K • (S • S • S) • (S • S • S)) tt tt Eq.refl) ▸ done


-- spell Gad(t=0, W=(), d=1, e=1) -> Gad(t=0, W=(), d=Sd, e=1): 5 steps
lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡1-e≡1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡Sd-e≡1⟩ : ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ []) ⟫ʷ
lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡1-e≡1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡Sd-e≡1⟩ = run b0
  where
  b0 : Chain (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ [])
  b0 = at 0 0 (S0⁻ ∷ S0 ∷ []) (win 3 0 complete₃ (ε) ((S • S • S) • S) tt tt Eq.refl) ▸
       at 6 0 (S0⁻ ∷ S0 ∷ []) (win 3 0 complete₃ (ε) ((S • S • S) • S) tt tt Eq.refl) ▸
       at 1 1 (S0 ∷ []) (win 3 0 complete₃ (S) (S) tt tt Eq.refl) ▸
       at 1 5 (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ []) (lem-pass-S0-vs-TOFF012-CS03-TOFF012-CSd03) ▸
       at 5 2 [] (win 3 0 complete₃ (S • (S • S • S)) (ε) tt tt Eq.refl) ▸ done


-- pass [S0] [CS03 TOFF012 CSd03 TOFF012]: 12 steps
lem-pass-S0-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0 ∷ []) ⟫ʷ
lem-pass-S0-vs-CS03-TOFF012-CSd03-TOFF012 = trans (run b0) (run b1)
  where
  b0 : Chain (S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0 ∷ CS12 ∷ CCZ012 ∷ CS12 ∷ CZ12 ∷ CCZ012 ∷ [])
  b0 = at 0 2 (CS03 ∷ S0 ∷ []) (lem-pass-S0-vs-CS03) ▸
       at 1 2 (Toff012 ∷ S0 ∷ CS12 ∷ CCZ012 ∷ []) (win 3 0 complete₃ (S • Toff) (Toff • S • (CS ↑) • CCZ) tt tt Eq.refl) ▸
       at 4 2 (CS03⁻ ∷ CCZ012 ∷ []) (lem-pass-CCZ012-vs-CSd03) ▸
       at 3 2 (CS03⁻ ∷ CS12 ∷ []) (lem-pass-CS12-vs-CSd03) ▸
       at 2 2 (CS03⁻ ∷ S0 ∷ []) (lem-pass-S0-vs-CSd03) ▸
       at 5 2 (Toff012 ∷ CZ12 ∷ CCZ012 ∷ []) (win 3 0 complete₃ (CCZ • Toff) (Toff • (CZ ↑) • CCZ) tt tt Eq.refl) ▸
       at 4 2 (Toff012 ∷ CS12 ∷ []) (win 3 0 complete₃ ((CS ↑) • Toff) (Toff • (CS ↑)) tt tt Eq.refl) ▸
       at 3 2 (Toff012 ∷ S0 ∷ CS12 ∷ CCZ012 ∷ []) (win 3 0 complete₃ (S • Toff) (Toff • S • (CS ↑) • CCZ) tt tt Eq.refl) ▸ done

  b1 : Chain (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0 ∷ CS12 ∷ CCZ012 ∷ CS12 ∷ CZ12 ∷ CCZ012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0 ∷ [])
  b1 = at 6 2 (CS12 ∷ CCZ012 ∷ []) (lem-pass-CCZ012-vs-CS12) ▸
       at 7 2 (CZ12 ∷ CCZ012 ∷ []) (lem-pass-CCZ012-vs-CZ12) ▸
       at 5 3 [] (win 3 0 complete₃ ((CS ↑) • (CS ↑) • (CZ ↑)) (ε) tt tt Eq.refl) ▸
       at 5 2 [] (win 3 0 complete₃ (CCZ • CCZ) (ε) tt tt Eq.refl) ▸ done


-- PP-flip ^-1: 35 steps
lem-PP-flip-ᵖ-1 : ⟪ (X0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-PP-flip-ᵖ-1 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (run b4))))
  where
  b0 : Chain (X0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X0 ∷ []) (X0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X0 ∷ CS03 ∷ Toff012 ∷ Toff012 ∷ CS03⁻ ∷ [])
  b0 = at 6 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 0 (CS02 ∷ CS02⁻ ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) tt tt Eq.refl) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 6 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 7 0 (Toff012 ∷ Toff012 ∷ []) (win 3 0 complete₃ (ε) (Toff • Toff) tt tt Eq.refl) ▸ done

  b1 : Chain (X0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X0 ∷ CS03 ∷ Toff012 ∷ Toff012 ∷ CS03⁻ ∷ []) (X0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ [])
  b1 = at 8 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 9 0 (CS02⁻ ∷ CS02 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 8 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 9 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 9 0 (Toff012 ∷ Toff012 ∷ []) (win 3 0 complete₃ (ε) (Toff • Toff) tt tt Eq.refl) ▸ done

  b2 : Chain (X0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (X0 ∷ CS03 ∷ Toff012 ∷ Sw23 ∷ CS02⁻ ∷ CS02 ∷ Sw23 ∷ Toff012 ∷ CS03⁻ ∷ X0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ [])
  b2 = at 6 4 (X0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X0 ∷ []) (sym lem-PP-flip) ▸
       at 5 2 [] (win 3 0 complete₃ (X • X) (ε) tt tt Eq.refl) ▸
       at 4 2 [] (win 3 0 complete₃ (Toff • Toff) (ε) tt tt Eq.refl) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 3 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b3 : Chain (X0 ∷ CS03 ∷ Toff012 ∷ Sw23 ∷ CS02⁻ ∷ CS02 ∷ Sw23 ∷ Toff012 ∷ CS03⁻ ∷ X0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (X0 ∷ Sw23 ∷ CS02 ∷ CS02⁻ ∷ Sw23 ∷ X0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ [])
  b3 = at 4 2 [] (win 3 0 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CS • Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 3 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 2 2 [] (win 3 0 complete₃ (Toff • Toff) (ε) tt tt Eq.refl) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b4 : Chain (X0 ∷ Sw23 ∷ CS02 ∷ CS02⁻ ∷ Sw23 ∷ X0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ [])
  b4 = at 2 2 [] (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 0 2 [] (win 3 0 complete₃ (X • X) (ε) tt tt Eq.refl) ▸ done


-- spell Gad(t=0, W=(), d=SK, e=-1) -> Gad(t=0, W=(), d=SdKdSd, e=1): 8 steps
lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡SdKdSd-e≡1⟩ : ⟪ (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ S0 ∷ []) ⟫ʷ
lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡SdKdSd-e≡1⟩ = run b0
  where
  b0 : Chain (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ S0 ∷ [])
  b0 = at 0 2 (S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0 ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ []) (win 3 0 complete₃ (S • K) ((S • S • S) • (K • iI) • (S • S • S) • S • K • S • S • K) tt tt Eq.refl) ▸
       at 12 2 (K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0 ∷ K0 ∷ S0 ∷ []) (win 3 0 complete₃ ((K • iI) • (S • S • S)) ((K • iI) • (S • S • S) • (S • S • S) • (K • iI) • (S • S • S) • S • K • S) tt tt Eq.refl) ▸
       at 3 5 (X0 ∷ S0 ∷ S0 ∷ S0 ∷ []) (win 3 0 complete₃ (S • K • S • S • K) (X • S • S • S) tt tt Eq.refl) ▸
       at 6 5 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0 ∷ []) (lem-pass-S0-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 5 5 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0 ∷ []) (lem-pass-S0-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 4 5 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0 ∷ []) (lem-pass-S0-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 8 8 (X0 ∷ []) (win 3 0 complete₃ (S • S • S • (K • iI) • (S • S • S) • (S • S • S) • (K • iI) • (S • S • S)) (X) tt tt Eq.refl) ▸
       at 3 6 (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (lem-PP-flip-ᵖ-1) ▸ done


-- prod Gad(t=0, W=(), d=1, e=1) Gad(t=0, W=(), d=SK, e=-1): 3 steps
lem-prod-Gad⟨t≡0-W≡⟨⟩-d≡1-e≡1⟩-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩ : ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ
lem-prod-Gad⟨t≡0-W≡⟨⟩-d≡1-e≡1⟩-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩ = run b0
  where
  b0 : Chain (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ [])
  b0 = at 0 4 (S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ []) (lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡1-e≡1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡Sd-e≡1⟩) ▸
       at 6 8 (S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ S0 ∷ []) (lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡SdKdSd-e≡1⟩) ▸
       at 0 16 (S0 ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) (lem-REL-Sd) ▸ done


-- REL SdKSS: 5 steps
lem-REL-SdKSS : ⟪ (S0⁻ ∷ K0 ∷ S0 ∷ S0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ
lem-REL-SdKSS = run b0
  where
  b0 : Chain (S0⁻ ∷ K0 ∷ S0 ∷ S0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ []) (S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ [])
  b0 = at 8 8 (K0⁻ ∷ S0⁻ ∷ []) (win 3 0 complete₃ ((S • S • S) • (S • S • S) • (K • iI) • S • K • S • S • K) ((K • iI) • (S • S • S)) tt tt Eq.refl) ▸
       at 14 4 (S0 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ []) (win 3 0 complete₃ ((K • iI) • (S • S • S) • (S • S • S) • (K • iI)) (S • K • (S • S • S) • (S • S • S) • (K • iI) • S) tt tt Eq.refl) ▸
       at 4 12 (S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ S0 ∷ []) (lem-REL0) ▸
       at 0 7 (S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ []) (win 3 0 complete₃ ((S • S • S) • K • S • S • (S • S • S) • (K • iI) • (S • S • S)) (S • S • (K • iI) • S • S) tt tt Eq.refl) ▸
       at 9 7 (S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) (win 3 0 complete₃ (S • K • S • (S • S • S) • (S • S • S) • (K • iI) • S) ((S • S • S) • (S • S • S) • K • (S • S • S) • (S • S • S)) tt tt Eq.refl) ▸ done


-- spell Gad(t=0, W=(), d=SK, e=-1) -> Gad(t=0, W=(), d=SdKSS, e=1): 47 steps
lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡SdKSS-e≡1⟩ : ⟪ (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0 ∷ S0 ∷ S0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ []) ⟫ʷ
lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡SdKSS-e≡1⟩ = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (run b5)))))
  where
  b0 : Chain (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (S0⁻ ∷ K0 ∷ S0 ∷ S0 ∷ X0 ∷ S0 ∷ S0 ∷ ι ∷ Sw23 ∷ CS02 ∷ ι ∷ Sw23 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ [])
  b0 = at 0 2 (S0⁻ ∷ K0 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ []) (win 3 0 complete₃ (S • K) ((S • S • S) • K • S • S • S • S • K • S • S • (K • iI)) tt tt Eq.refl) ▸
       at 14 2 (K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ []) (win 3 0 complete₃ ((K • iI) • (S • S • S)) (K • (S • S • S) • (S • S • S) • (K • iI) • (S • S • S) • (S • S • S) • (S • S • S) • (S • S • S) • (K • iI) • S) tt tt Eq.refl) ▸
       at 4 6 (X0 ∷ S0 ∷ S0 ∷ ι ∷ ι ∷ []) (win 3 0 complete₃ (S • S • K • S • S • (K • iI)) (X • S • S • iI • iI) tt tt Eq.refl) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 8 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸
       at 9 2 (CS02 ∷ ι ∷ []) (win 3 0 complete₃ (iI • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • iI) tt tt Eq.refl) ▸ done

  b1 : Chain (S0⁻ ∷ K0 ∷ S0 ∷ S0 ∷ X0 ∷ S0 ∷ S0 ∷ ι ∷ Sw23 ∷ CS02 ∷ ι ∷ Sw23 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ []) (S0⁻ ∷ K0 ∷ S0 ∷ S0 ∷ X0 ∷ S0 ∷ S0 ∷ ι ∷ CS03 ∷ Toff012 ∷ ι ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ Toff012 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ [])
  b1 = at 10 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 10 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 9 2 (Toff012 ∷ ι ∷ []) (win 3 0 complete₃ (iI • Toff) (Toff • iI) tt tt Eq.refl) ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 11 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b2 : Chain (S0⁻ ∷ K0 ∷ S0 ∷ S0 ∷ X0 ∷ S0 ∷ S0 ∷ ι ∷ CS03 ∷ Toff012 ∷ ι ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ Toff012 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ []) (S0⁻ ∷ K0 ∷ S0 ∷ S0 ∷ X0 ∷ S0 ∷ S0 ∷ ι ∷ CS03 ∷ Sw23 ∷ Sw23 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ ι ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ [])
  b2 = at 10 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸
       at 11 2 (CS02⁻ ∷ ι ∷ []) (win 3 0 complete₃ (iI • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • iI) tt tt Eq.refl) ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 10 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 12 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 11 2 (Toff012 ∷ ι ∷ []) (win 3 0 complete₃ (iI • Toff) (Toff • iI) tt tt Eq.refl) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b3 : Chain (S0⁻ ∷ K0 ∷ S0 ∷ S0 ∷ X0 ∷ S0 ∷ S0 ∷ ι ∷ CS03 ∷ Sw23 ∷ Sw23 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ ι ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ []) (S0⁻ ∷ K0 ∷ S0 ∷ S0 ∷ X0 ∷ S0 ∷ S0 ∷ CS03 ∷ ι ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ ι ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ [])
  b3 = at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 7 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸
       at 8 2 (CS02 ∷ ι ∷ []) (win 3 0 complete₃ (iI • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • iI) tt tt Eq.refl) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 9 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b4 : Chain (S0⁻ ∷ K0 ∷ S0 ∷ S0 ∷ X0 ∷ S0 ∷ S0 ∷ CS03 ∷ ι ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ ι ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ []) (S0⁻ ∷ K0 ∷ S0 ∷ S0 ∷ X0 ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Sw23 ∷ ι ∷ Sw23 ∷ Toff012 ∷ ι ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ [])
  b4 = at 8 2 (Toff012 ∷ ι ∷ []) (win 3 0 complete₃ (iI • Toff) (Toff • iI) tt tt Eq.refl) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 10 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 9 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸
       at 10 2 (CS02⁻ ∷ ι ∷ []) (win 3 0 complete₃ (iI • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • iI) tt tt Eq.refl) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 9 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b5 : Chain (S0⁻ ∷ K0 ∷ S0 ∷ S0 ∷ X0 ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Sw23 ∷ ι ∷ Sw23 ∷ Toff012 ∷ ι ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ []) (S0⁻ ∷ K0 ∷ S0 ∷ S0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ [])
  b5 = at 10 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 11 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 10 2 (Toff012 ∷ ι ∷ []) (win 3 0 complete₃ (iI • Toff) (Toff • iI) tt tt Eq.refl) ▸
       at 6 5 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0 ∷ []) (lem-pass-S0-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 5 5 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0 ∷ []) (lem-pass-S0-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 9 10 (X0 ∷ []) (win 3 0 complete₃ (S • S • iI • iI • K • (S • S • S) • (S • S • S) • (K • iI) • (S • S • S) • (S • S • S)) (X) tt tt Eq.refl) ▸
       at 4 6 (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (lem-PP-flip-ᵖ-1) ▸ done


-- spell Gad(t=0, W=(), d=1, e=-1) -> Gad(t=0, W=(), d=KSSK, e=1): 25 steps
lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡1-e≡-1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡KSSK-e≡1⟩ : ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ S0 ∷ S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ []) ⟫ʷ
lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡1-e≡-1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡KSSK-e≡1⟩ = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (K0 ∷ S0 ∷ S0 ∷ K0 ∷ X0 ∷ Sw23 ∷ CS02 ∷ ι ∷ Sw23 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ [])
  b0 = at 0 0 (K0 ∷ S0 ∷ S0 ∷ K0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ []) (win 3 0 complete₃ (ε) (K • S • S • K • (K • iI) • S • S • (K • iI)) tt tt Eq.refl) ▸
       at 12 0 (K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ []) (win 3 0 complete₃ (ε) (K • (S • S • S) • (S • S • S) • K • (K • iI) • (S • S • S) • (S • S • S) • (K • iI)) tt tt Eq.refl) ▸
       at 4 4 (X0 ∷ ι ∷ []) (win 3 0 complete₃ ((K • iI) • S • S • (K • iI)) (X • iI) tt tt Eq.refl) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 5 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸
       at 6 2 (CS02 ∷ ι ∷ []) (win 3 0 complete₃ (iI • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • iI) tt tt Eq.refl) ▸ done

  b1 : Chain (K0 ∷ S0 ∷ S0 ∷ K0 ∷ X0 ∷ Sw23 ∷ CS02 ∷ ι ∷ Sw23 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ []) (K0 ∷ S0 ∷ S0 ∷ K0 ∷ X0 ∷ CS03 ∷ Toff012 ∷ ι ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ Toff012 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ [])
  b1 = at 7 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 7 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 6 2 (Toff012 ∷ ι ∷ []) (win 3 0 complete₃ (iI • Toff) (Toff • iI) tt tt Eq.refl) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 8 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b2 : Chain (K0 ∷ S0 ∷ S0 ∷ K0 ∷ X0 ∷ CS03 ∷ Toff012 ∷ ι ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ Toff012 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ []) (K0 ∷ S0 ∷ S0 ∷ K0 ∷ X0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X0 ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ [])
  b2 = at 7 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸
       at 8 2 (CS02⁻ ∷ ι ∷ []) (win 3 0 complete₃ (iI • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • iI) tt tt Eq.refl) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 9 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 8 2 (Toff012 ∷ ι ∷ []) (win 3 0 complete₃ (iI • Toff) (Toff • iI) tt tt Eq.refl) ▸
       at 9 5 (X0 ∷ []) (win 3 0 complete₃ (iI • K • (S • S • S) • (S • S • S) • K) (X) tt tt Eq.refl) ▸ done

  b3 : Chain (K0 ∷ S0 ∷ S0 ∷ K0 ∷ X0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X0 ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ []) (K0 ∷ S0 ∷ S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ [])
  b3 = at 4 6 (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (lem-PP-flip-ᵖ-1) ▸ done


-- prod Gad(t=0, W=(), d=SK, e=-1) Gad(t=0, W=(), d=1, e=-1): 3 steps
lem-prod-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩-Gad⟨t≡0-W≡⟨⟩-d≡1-e≡-1⟩ : ⟪ (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ
lem-prod-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩-Gad⟨t≡0-W≡⟨⟩-d≡1-e≡-1⟩ = run b0
  where
  b0 : Chain (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ [])
  b0 = at 0 8 (S0⁻ ∷ K0 ∷ S0 ∷ S0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ []) (lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡SdKSS-e≡1⟩) ▸
       at 12 4 (K0 ∷ S0 ∷ S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ []) (lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡1-e≡-1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡KSSK-e≡1⟩) ▸
       at 0 24 (S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) (lem-REL-SdKSS) ▸ done


-- spell Gad(t=0, W=(), d=SSKdSd, e=1) -> Gad(t=0, W=(), d=SSKdSS, e=1): 5 steps
lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡SSKdSd-e≡1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡SSKdSS-e≡1⟩ : ⟪ (S0 ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ
lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡SSKdSd-e≡1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡SSKdSS-e≡1⟩ = run b0
  where
  b0 : Chain (S0 ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) (S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ [])
  b0 = at 0 4 (S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ S0 ∷ []) (win 3 0 complete₃ (S • S • (K • iI) • (S • S • S)) (S • S • (K • iI) • S • S • S) tt tt Eq.refl) ▸
       at 10 4 (S0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) (win 3 0 complete₃ (S • K • (S • S • S) • (S • S • S)) ((S • S • S) • (S • S • S) • (S • S • S) • K • (S • S • S) • (S • S • S)) tt tt Eq.refl) ▸
       at 5 1 (S0 ∷ []) (win 3 0 complete₃ (S) (S) tt tt Eq.refl) ▸
       at 5 5 (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ []) (lem-pass-S0-vs-TOFF012-CS03-TOFF012-CSd03) ▸
       at 9 2 [] (win 3 0 complete₃ (S • (S • S • S)) (ε) tt tt Eq.refl) ▸ done


-- F6 p l = l p': 6 steps
lem-F6-p-l-≡-l-p' : ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ S1 ∷ CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ []) ⟫ʷ ≈ ⟪ (CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ S1 ∷ CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ X0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X0 ∷ []) ⟫ʷ
lem-F6-p-l-≡-l-p' = run b0
  where
  b0 : Chain (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ S1 ∷ CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ []) (CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ S1 ∷ CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ X0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X0 ∷ [])
  b0 = at 4 15 (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (lem-ROT-gad) ▸
       at 0 12 (S0 ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) (lem-prod-Gad⟨t≡0-W≡⟨⟩-d≡1-e≡1⟩-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩) ▸
       at 0 12 (S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) (lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡SSKdSd-e≡1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡SSKdSS-e≡1⟩) ▸
       at 0 14 (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (sym lem-prod-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩-Gad⟨t≡0-W≡⟨⟩-d≡1-e≡-1⟩) ▸
       at 8 4 (X0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X0 ∷ []) (sym lem-PP-flip) ▸
       at 0 8 (CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ S1 ∷ CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ []) (sym lem-ROT-gad) ▸ done


-- PP-flip @1023: 69 steps
lem-PP-flip-at1023 : ⟪ (X1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) ⟫ʷ
lem-PP-flip-at1023 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (run b8))))))))
  where
  b0 : Chain (X1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X1 ∷ []) (X1 ∷ Toff102 ∷ CS13 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw01 ∷ CS03⁻ ∷ X0 ∷ Sw01 ∷ [])
  b0 = at 6 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 5 2 (Sw01 ∷ X0 ∷ []) (win 3 0 complete₃ ((X ↑) • Swap) (Swap • X) tt tt Eq.refl) ▸
       at 4 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 5 2 (Sw01 ∷ CS02⁻ ∷ []) (win 3 0 complete₃ (((CS • CS • CS) ↑) • Swap) (Swap • (Swap ↑ • (CS • CS • CS) • Swap ↑)) tt tt Eq.refl) ▸
       at 4 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 5 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (X1 ∷ Toff102 ∷ CS13 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw01 ∷ CS03⁻ ∷ X0 ∷ Sw01 ∷ []) (X1 ∷ Toff102 ∷ CS13 ∷ Sw01 ∷ K0 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K0 ∷ ι1 ∷ CS03⁻ ∷ X0 ∷ Sw01 ∷ [])
  b1 = at 10 2 (Sw01 ∷ ι1 ∷ []) (win 3 0 complete₃ (iI • Swap) (Swap • (iI ↑)) tt tt Eq.refl) ▸
       at 9 2 (Sw01 ∷ K0 ∷ []) (win 3 0 complete₃ ((K ↑) • Swap) (Swap • K) tt tt Eq.refl) ▸
       at 8 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 7 2 (Sw01 ∷ CX10 ∷ []) (win 3 0 complete₃ (CX₀₁ • Swap) (Swap • CX₁₀) tt tt Eq.refl) ▸
       at 6 2 (Sw01 ∷ CS02⁻ ∷ []) (win 3 0 complete₃ (((CS • CS • CS) ↑) • Swap) (Swap • (Swap ↑ • (CS • CS • CS) • Swap ↑)) tt tt Eq.refl) ▸
       at 5 2 (Sw01 ∷ CX10 ∷ []) (win 3 0 complete₃ (CX₀₁ • Swap) (Swap • CX₁₀) tt tt Eq.refl) ▸
       at 4 2 (Sw01 ∷ CS02 ∷ []) (win 3 0 complete₃ ((CS ↑) • Swap) (Swap • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 3 2 (Sw01 ∷ K0 ∷ []) (win 3 0 complete₃ ((K ↑) • Swap) (Swap • K) tt tt Eq.refl) ▸ done

  b2 : Chain (X1 ∷ Toff102 ∷ CS13 ∷ Sw01 ∷ K0 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K0 ∷ ι1 ∷ CS03⁻ ∷ X0 ∷ Sw01 ∷ []) (X1 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw01 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X0 ∷ Sw01 ∷ [])
  b2 = at 4 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (win 3 0 complete₃ (K • (Swap ↑ • CS • Swap ↑) • CX₁₀ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • CX₁₀ • (CS ↑) • K • (iI ↑)) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) tt tt Eq.refl) ▸
       at 4 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 3 2 (Sw01 ∷ CS02 ∷ []) (win 3 0 complete₃ ((CS ↑) • Swap) (Swap • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 2 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 3 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸ done

  b3 : Chain (X1 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw01 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X0 ∷ Sw01 ∷ []) (X1 ∷ Sw01 ∷ K0 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K0 ∷ ι1 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X0 ∷ Sw01 ∷ [])
  b3 = at 8 2 (Sw01 ∷ ι1 ∷ []) (win 3 0 complete₃ (iI • Swap) (Swap • (iI ↑)) tt tt Eq.refl) ▸
       at 7 2 (Sw01 ∷ K0 ∷ []) (win 3 0 complete₃ ((K ↑) • Swap) (Swap • K) tt tt Eq.refl) ▸
       at 6 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 5 2 (Sw01 ∷ CX10 ∷ []) (win 3 0 complete₃ (CX₀₁ • Swap) (Swap • CX₁₀) tt tt Eq.refl) ▸
       at 4 2 (Sw01 ∷ CS02⁻ ∷ []) (win 3 0 complete₃ (((CS • CS • CS) ↑) • Swap) (Swap • (Swap ↑ • (CS • CS • CS) • Swap ↑)) tt tt Eq.refl) ▸
       at 3 2 (Sw01 ∷ CX10 ∷ []) (win 3 0 complete₃ (CX₀₁ • Swap) (Swap • CX₁₀) tt tt Eq.refl) ▸
       at 2 2 (Sw01 ∷ CS02 ∷ []) (win 3 0 complete₃ ((CS ↑) • Swap) (Swap • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 1 2 (Sw01 ∷ K0 ∷ []) (win 3 0 complete₃ ((K ↑) • Swap) (Swap • K) tt tt Eq.refl) ▸ done

  b4 : Chain (X1 ∷ Sw01 ∷ K0 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K0 ∷ ι1 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X0 ∷ Sw01 ∷ []) (Sw23 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ Sw01 ∷ [])
  b4 = at 2 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (win 3 0 complete₃ (K • (Swap ↑ • CS • Swap ↑) • CX₁₀ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • CX₁₀ • (CS ↑) • K • (iI ↑)) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) tt tt Eq.refl) ▸
       at 2 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw01 ∷ X0 ∷ []) (win 3 0 complete₃ ((X ↑) • Swap) (Swap • X) tt tt Eq.refl) ▸
       at 1 6 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (lem-PP-flip) ▸
       at 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 1 2 (CS12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • Swap) tt tt Eq.refl) ▸
       at 2 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b5 : Chain (Sw23 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ Sw01 ∷ []) (CS13 ∷ K1 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ Sw01 ∷ K0 ∷ ι ∷ CS03⁻ ∷ Toff012 ∷ Sw01 ∷ [])
  b5 = at 0 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (K1 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • K) ((K ↑) • Swap) tt tt Eq.refl) ▸
       at 2 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 3 2 (CX10 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • CX₀₁) (CX₁₀ • Swap) tt tt Eq.refl) ▸
       at 4 2 (CS02⁻ ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • ((CS • CS • CS) ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 5 2 (CX10 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • CX₀₁) (CX₁₀ • Swap) tt tt Eq.refl) ▸
       at 6 2 (CS12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • Swap) tt tt Eq.refl) ▸ done

  b6 : Chain (CS13 ∷ K1 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ Sw01 ∷ K0 ∷ ι ∷ CS03⁻ ∷ Toff012 ∷ Sw01 ∷ []) (CS13 ∷ Toff102 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw01 ∷ Toff012 ∷ Sw01 ∷ [])
  b6 = at 7 2 (K1 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • K) ((K ↑) • Swap) tt tt Eq.refl) ▸
       at 8 2 (ι1 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • iI) ((iI ↑) • Swap) tt tt Eq.refl) ▸
       at 1 8 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (win 3 0 complete₃ ((K ↑) • (Swap ↑ • CS • Swap ↑) • CX₁₀ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • CX₁₀ • (CS ↑) • (K ↑) • (iI ↑)) ((K ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑) • iI) tt tt Eq.refl) ▸
       at 1 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 3 2 (CS12⁻ ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • (CS • CS • CS) • Swap ↑)) (((CS • CS • CS) ↑) • Swap) tt tt Eq.refl) ▸
       at 4 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b7 : Chain (CS13 ∷ Toff102 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw01 ∷ Toff012 ∷ Sw01 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ Sw01 ∷ K0 ∷ ι ∷ Sw01 ∷ [])
  b7 = at 2 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (K1 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • K) ((K ↑) • Swap) tt tt Eq.refl) ▸
       at 4 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 5 2 (CX10 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • CX₀₁) (CX₁₀ • Swap) tt tt Eq.refl) ▸
       at 6 2 (CS02⁻ ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • ((CS • CS • CS) ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 7 2 (CX10 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • CX₀₁) (CX₁₀ • Swap) tt tt Eq.refl) ▸
       at 8 2 (CS12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • Swap) tt tt Eq.refl) ▸ done

  b8 : Chain (CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ Sw01 ∷ K0 ∷ ι ∷ Sw01 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ [])
  b8 = at 9 2 (K1 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • K) ((K ↑) • Swap) tt tt Eq.refl) ▸
       at 10 2 (ι1 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • iI) ((iI ↑) • Swap) tt tt Eq.refl) ▸
       at 3 8 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (win 3 0 complete₃ ((K ↑) • (Swap ↑ • CS • Swap ↑) • CX₁₀ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • CX₁₀ • (CS ↑) • (K ↑) • (iI ↑)) ((K ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑) • iI) tt tt Eq.refl) ▸
       at 3 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done

