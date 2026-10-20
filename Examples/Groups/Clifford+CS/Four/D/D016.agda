{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D016 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Tools using (ax)
open import Examples.Groups.Clifford+CS.TopWeakening using (low-comm)
open import Examples.Groups.Clifford+CS.Idle using (low₁-comm)
open import Examples.Groups.Clifford+CS.Four.Chain
open import Examples.Groups.Clifford+CS.Four.Wins.W01 using (wn00001 ; wn00003 ; wn00005 ; wn00011 ; wn00024 ; wn00025 ; wn00026 ; wn00027 ; wn00028 ; wn00029 ; wn00030 ; wn00031 ; wn00039 ; wn00043 ; wn00086 ; wn00093 ; wn00121 ; wn00123 ; wn00124 ; wn00129 ; wn00139 ; wn00142 ; wn00173 ; wn00175 ; wn00179 ; wn00181 ; wn00191 ; wn00196)
open import Examples.Groups.Clifford+CS.Four.Wins.W02 using (wn00219 ; wn00220 ; wn00221 ; wn00249 ; wn00250 ; wn00251 ; wn00254 ; wn00274 ; wn00275 ; wn00287 ; wn00288 ; wn00297 ; wn00298 ; wn00299 ; wn00300 ; wn00301 ; wn00302 ; wn00303 ; wn00304 ; wn00305 ; wn00306 ; wn00307 ; wn00308 ; wn00309 ; wn00310 ; wn00311 ; wn00312 ; wn00313 ; wn00314 ; wn00315 ; wn00316 ; wn00317 ; wn00318 ; wn00319 ; wn00320 ; wn00321 ; wn00322 ; wn00323 ; wn00324 ; wn00325 ; wn00326 ; wn00327 ; wn00328 ; wn00329 ; wn00330 ; wn00331 ; wn00332)

-- pass [X1 CS10 X1] [CS03]: 13 steps
lem-pass-X1-CS10-X1-vs-CS03 : ⟪ (X1 ∷ CS01 ∷ X1 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ X1 ∷ CS01 ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CS10-X1-vs-CS03 = trans (run b0) (run b1)
  where
  b0 : Chain (X1 ∷ CS01 ∷ X1 ∷ CS03 ∷ []) (Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ X1 ∷ CS01 ∷ X1 ∷ Sw23 ∷ [])
  b0 = at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00003 ▸
       at 2 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 1 2 (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap)) ▸
       at 0 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 1 4 (CS02 ∷ X1 ∷ CS01 ∷ X1 ∷ []) wn00297 ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b1 : Chain (Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ X1 ∷ CS01 ∷ X1 ∷ Sw23 ∷ []) (CS03 ∷ X1 ∷ CS01 ∷ X1 ∷ [])
  b1 = at 0 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 2 2 (CS01 ∷ Sw23 ∷ []) (sym (low-comm (CS) (Swap))) ▸
       at 3 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 4 2 [] wn00003 ▸ done

-- pass [X1 CS10 X1] [CSd03]: 13 steps
lem-pass-X1-CS10-X1-vs-CSd03 : ⟪ (X1 ∷ CS01 ∷ X1 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ X1 ∷ CS01 ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CS10-X1-vs-CSd03 = trans (run b0) (run b1)
  where
  b0 : Chain (X1 ∷ CS01 ∷ X1 ∷ CS03⁻ ∷ []) (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ Sw23 ∷ X1 ∷ CS01 ∷ X1 ∷ Sw23 ∷ [])
  b0 = at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00003 ▸
       at 2 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 1 2 (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap)) ▸
       at 0 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 1 4 (CS02⁻ ∷ X1 ∷ CS01 ∷ X1 ∷ []) wn00298 ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b1 : Chain (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ Sw23 ∷ X1 ∷ CS01 ∷ X1 ∷ Sw23 ∷ []) (CS03⁻ ∷ X1 ∷ CS01 ∷ X1 ∷ [])
  b1 = at 0 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 2 2 (CS01 ∷ Sw23 ∷ []) (sym (low-comm (CS) (Swap))) ▸
       at 3 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 4 2 [] wn00003 ▸ done

-- pass [CS13] [X3 TOFF103 X3]: 65 steps
lem-pass-CS13-vs-X3-TOFF103-X3 : ⟪ (CS13 ∷ X3 ∷ Toff103 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff103 ∷ X3 ∷ CS13 ∷ []) ⟫ʷ
lem-pass-CS13-vs-X3-TOFF103-X3 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (run b8))))))))
  where
  b0 : Chain (CS13 ∷ X3 ∷ Toff103 ∷ X3 ∷ []) (CS13 ∷ X3 ∷ K1 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw23 ∷ X2 ∷ Sw23 ∷ [])
  b0 = at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 2 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b1 : Chain (CS13 ∷ X3 ∷ K1 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw23 ∷ X2 ∷ Sw23 ∷ []) (CS13 ∷ X3 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw23 ∷ X2 ∷ Sw23 ∷ [])
  b1 = at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 5 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 7 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 10 2 [] wn00003 ▸ done

  b2 : Chain (CS13 ∷ X3 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw23 ∷ X2 ∷ Sw23 ∷ []) (CS13 ∷ X3 ∷ K1 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ X2 ∷ Sw23 ∷ [])
  b2 = at 9 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸
       at 8 2 (Sw23 ∷ K1 ∷ []) (low-comm ((K ↑)) (Swap)) ▸
       at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] wn00003 ▸
       at 6 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] wn00003 ▸
       at 4 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸ done

  b3 : Chain (CS13 ∷ X3 ∷ K1 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ X2 ∷ Sw23 ∷ []) (Sw23 ∷ CS12 ∷ X2 ∷ Toff102 ∷ X2 ∷ Sw23 ∷ [])
  b3 = at 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00003 ▸
       at 2 2 (Sw23 ∷ K1 ∷ []) (low-comm ((K ↑)) (Swap)) ▸
       at 3 8 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) wn00196 ▸
       at 3 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 0 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00003 ▸ done

  b4 : Chain (Sw23 ∷ CS12 ∷ X2 ∷ Toff102 ∷ X2 ∷ Sw23 ∷ []) (X3 ∷ K1 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ X2 ∷ CS12 ∷ Sw23 ∷ [])
  b4 = at 1 4 (X2 ∷ Toff102 ∷ X2 ∷ CS12 ∷ []) wn00299 ▸
       at 0 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 2 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b5 : Chain (X3 ∷ K1 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ X2 ∷ CS12 ∷ Sw23 ∷ []) (X3 ∷ Sw23 ∷ K1 ∷ Sw23 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw23 ∷ X2 ∷ CS12 ∷ Sw23 ∷ [])
  b5 = at 4 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 8 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸ done

  b6 : Chain (X3 ∷ Sw23 ∷ K1 ∷ Sw23 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw23 ∷ X2 ∷ CS12 ∷ Sw23 ∷ []) (X3 ∷ Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ K1 ∷ ι ∷ Sw23 ∷ X2 ∷ CS12 ∷ Sw23 ∷ [])
  b6 = at 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] wn00003 ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00003 ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] wn00003 ▸ done

  b7 : Chain (X3 ∷ Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ K1 ∷ ι ∷ Sw23 ∷ X2 ∷ CS12 ∷ Sw23 ∷ []) (X3 ∷ Toff103 ∷ X3 ∷ CS13 ∷ Sw23 ∷ Sw23 ∷ [])
  b7 = at 8 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 2 8 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) wn00196 ▸
       at 2 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff103 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b8 : Chain (X3 ∷ Toff103 ∷ X3 ∷ CS13 ∷ Sw23 ∷ Sw23 ∷ []) (X3 ∷ Toff103 ∷ X3 ∷ CS13 ∷ [])
  b8 = at 4 2 [] wn00003 ▸ done

-- pass [CSd13] [X3 TOFF103 X3]: 65 steps
lem-pass-CSd13-vs-X3-TOFF103-X3 : ⟪ (CS13⁻ ∷ X3 ∷ Toff103 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff103 ∷ X3 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-pass-CSd13-vs-X3-TOFF103-X3 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (run b8))))))))
  where
  b0 : Chain (CS13⁻ ∷ X3 ∷ Toff103 ∷ X3 ∷ []) (CS13⁻ ∷ X3 ∷ K1 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw23 ∷ X2 ∷ Sw23 ∷ [])
  b0 = at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 2 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b1 : Chain (CS13⁻ ∷ X3 ∷ K1 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw23 ∷ X2 ∷ Sw23 ∷ []) (CS13⁻ ∷ X3 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw23 ∷ X2 ∷ Sw23 ∷ [])
  b1 = at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 5 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 7 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 10 2 [] wn00003 ▸ done

  b2 : Chain (CS13⁻ ∷ X3 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw23 ∷ X2 ∷ Sw23 ∷ []) (CS13⁻ ∷ X3 ∷ K1 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ X2 ∷ Sw23 ∷ [])
  b2 = at 9 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸
       at 8 2 (Sw23 ∷ K1 ∷ []) (low-comm ((K ↑)) (Swap)) ▸
       at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] wn00003 ▸
       at 6 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] wn00003 ▸
       at 4 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸ done

  b3 : Chain (CS13⁻ ∷ X3 ∷ K1 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ X2 ∷ Sw23 ∷ []) (Sw23 ∷ CS12⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ Sw23 ∷ [])
  b3 = at 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00003 ▸
       at 2 2 (Sw23 ∷ K1 ∷ []) (low-comm ((K ↑)) (Swap)) ▸
       at 3 8 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) wn00196 ▸
       at 3 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 0 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00003 ▸ done

  b4 : Chain (Sw23 ∷ CS12⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ Sw23 ∷ []) (X3 ∷ K1 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ X2 ∷ CS12⁻ ∷ Sw23 ∷ [])
  b4 = at 1 4 (X2 ∷ Toff102 ∷ X2 ∷ CS12⁻ ∷ []) wn00300 ▸
       at 0 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 2 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b5 : Chain (X3 ∷ K1 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ X2 ∷ CS12⁻ ∷ Sw23 ∷ []) (X3 ∷ Sw23 ∷ K1 ∷ Sw23 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw23 ∷ X2 ∷ CS12⁻ ∷ Sw23 ∷ [])
  b5 = at 4 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 8 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸ done

  b6 : Chain (X3 ∷ Sw23 ∷ K1 ∷ Sw23 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw23 ∷ X2 ∷ CS12⁻ ∷ Sw23 ∷ []) (X3 ∷ Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ K1 ∷ ι ∷ Sw23 ∷ X2 ∷ CS12⁻ ∷ Sw23 ∷ [])
  b6 = at 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] wn00003 ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00003 ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] wn00003 ▸ done

  b7 : Chain (X3 ∷ Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ K1 ∷ ι ∷ Sw23 ∷ X2 ∷ CS12⁻ ∷ Sw23 ∷ []) (X3 ∷ Toff103 ∷ X3 ∷ CS13⁻ ∷ Sw23 ∷ Sw23 ∷ [])
  b7 = at 8 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 2 8 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) wn00196 ▸
       at 2 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff103 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b8 : Chain (X3 ∷ Toff103 ∷ X3 ∷ CS13⁻ ∷ Sw23 ∷ Sw23 ∷ []) (X3 ∷ Toff103 ∷ X3 ∷ CS13⁻ ∷ [])
  b8 = at 4 2 [] wn00003 ▸ done

-- pass [CS12] [CS13]: 1 steps
lem-pass-CS12-vs-CS13 : ⟪ (CS12 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ CS12 ∷ []) ⟫ʷ
lem-pass-CS12-vs-CS13 = run b0
  where
  b0 : Chain (CS12 ∷ CS13 ∷ []) (CS13 ∷ CS12 ∷ [])
  b0 = at 0 2 (CS13 ∷ CS12 ∷ []) wn00093 ▸ done

-- pass [CCZ012] [CZ02]: 1 steps
lem-pass-CCZ012-vs-CZ02 : ⟪ (CCZ012 ∷ CZ02 ∷ []) ⟫ʷ ≈ ⟪ (CZ02 ∷ CCZ012 ∷ []) ⟫ʷ
lem-pass-CCZ012-vs-CZ02 = run b0
  where
  b0 : Chain (CCZ012 ∷ CZ02 ∷ []) (CZ02 ∷ CCZ012 ∷ [])
  b0 = at 0 2 (CZ02 ∷ CCZ012 ∷ []) wn00301 ▸ done

-- pass [CS12] [CZ02]: 1 steps
lem-pass-CS12-vs-CZ02 : ⟪ (CS12 ∷ CZ02 ∷ []) ⟫ʷ ≈ ⟪ (CZ02 ∷ CS12 ∷ []) ⟫ʷ
lem-pass-CS12-vs-CZ02 = run b0
  where
  b0 : Chain (CS12 ∷ CZ02 ∷ []) (CZ02 ∷ CS12 ∷ [])
  b0 = at 0 2 (CZ02 ∷ CS12 ∷ []) wn00302 ▸ done

-- pass [CS12] [CSd13]: 1 steps
lem-pass-CS12-vs-CSd13 : ⟪ (CS12 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ CS12 ∷ []) ⟫ʷ
lem-pass-CS12-vs-CSd13 = run b0
  where
  b0 : Chain (CS12 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CS12 ∷ [])
  b0 = at 0 2 (CS13⁻ ∷ CS12 ∷ []) wn00086 ▸ done

-- pass [CSd12] [CS13]: 1 steps
lem-pass-CSd12-vs-CS13 : ⟪ (CS12⁻ ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ CS12⁻ ∷ []) ⟫ʷ
lem-pass-CSd12-vs-CS13 = run b0
  where
  b0 : Chain (CS12⁻ ∷ CS13 ∷ []) (CS13 ∷ CS12⁻ ∷ [])
  b0 = at 0 2 (CS13 ∷ CS12⁻ ∷ []) wn00179 ▸ done

-- pass [CSd12] [CZ02]: 1 steps
lem-pass-CSd12-vs-CZ02 : ⟪ (CS12⁻ ∷ CZ02 ∷ []) ⟫ʷ ≈ ⟪ (CZ02 ∷ CS12⁻ ∷ []) ⟫ʷ
lem-pass-CSd12-vs-CZ02 = run b0
  where
  b0 : Chain (CS12⁻ ∷ CZ02 ∷ []) (CZ02 ∷ CS12⁻ ∷ [])
  b0 = at 0 2 (CZ02 ∷ CS12⁻ ∷ []) wn00303 ▸ done

-- pass [CSd12] [CSd13]: 1 steps
lem-pass-CSd12-vs-CSd13 : ⟪ (CS12⁻ ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ CS12⁻ ∷ []) ⟫ʷ
lem-pass-CSd12-vs-CSd13 = run b0
  where
  b0 : Chain (CS12⁻ ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CS12⁻ ∷ [])
  b0 = at 0 2 (CS13⁻ ∷ CS12⁻ ∷ []) wn00181 ▸ done

-- pass [X3 CSd31 X3] [TOFF103]: 65 steps
lem-pass-X3-CSd31-X3-vs-TOFF103 : ⟪ (X3 ∷ CS13⁻ ∷ X3 ∷ Toff103 ∷ []) ⟫ʷ ≈ ⟪ (Toff103 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CSd31-X3-vs-TOFF103 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (run b8))))))))
  where
  b0 : Chain (X3 ∷ CS13⁻ ∷ X3 ∷ Toff103 ∷ []) (X3 ∷ CS13⁻ ∷ X3 ∷ K1 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ [])
  b0 = at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b1 : Chain (X3 ∷ CS13⁻ ∷ X3 ∷ K1 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ []) (X3 ∷ CS13⁻ ∷ X3 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ Sw23 ∷ ι ∷ Sw23 ∷ [])
  b1 = at 6 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 10 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 11 2 [] wn00003 ▸
       at 10 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸ done

  b2 : Chain (X3 ∷ CS13⁻ ∷ X3 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ Sw23 ∷ ι ∷ Sw23 ∷ []) (X3 ∷ CS13⁻ ∷ X3 ∷ K1 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ [])
  b2 = at 9 2 (Sw23 ∷ K1 ∷ []) (low-comm ((K ↑)) (Swap)) ▸
       at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] wn00003 ▸
       at 7 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] wn00003 ▸
       at 5 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b3 : Chain (X3 ∷ CS13⁻ ∷ X3 ∷ K1 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ []) (Sw23 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ Toff102 ∷ Sw23 ∷ [])
  b3 = at 6 2 [] wn00003 ▸
       at 3 2 (Sw23 ∷ K1 ∷ []) (low-comm ((K ↑)) (Swap)) ▸
       at 4 8 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) wn00196 ▸
       at 4 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 1 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] wn00003 ▸
       at 0 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸ done

  b4 : Chain (Sw23 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ Toff102 ∷ Sw23 ∷ []) (K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ X2 ∷ CS12⁻ ∷ X2 ∷ Sw23 ∷ [])
  b4 = at 1 4 (Toff102 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) wn00304 ▸
       at 1 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b5 : Chain (K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ X2 ∷ CS12⁻ ∷ X2 ∷ Sw23 ∷ []) (Sw23 ∷ K1 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw23 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ Sw23 ∷ [])
  b5 = at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 5 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 7 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b6 : Chain (Sw23 ∷ K1 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw23 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ Sw23 ∷ []) (Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ Sw23 ∷ ι ∷ Sw23 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ Sw23 ∷ [])
  b6 = at 2 2 [] wn00003 ▸
       at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00003 ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00003 ▸
       at 7 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸ done

  b7 : Chain (Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ Sw23 ∷ ι ∷ Sw23 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ Sw23 ∷ []) (Toff103 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ Sw23 ∷ Sw23 ∷ [])
  b7 = at 8 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 1 8 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) wn00196 ▸
       at 1 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Toff103 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸ done

  b8 : Chain (Toff103 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ Sw23 ∷ Sw23 ∷ []) (Toff103 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ [])
  b8 = at 4 2 [] wn00003 ▸ done

-- pass [X3 CSd31 X3] [CS12]: 1 steps
lem-pass-X3-CSd31-X3-vs-CS12 : ⟪ (X3 ∷ CS13⁻ ∷ X3 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CSd31-X3-vs-CS12 = run b0
  where
  b0 : Chain (X3 ∷ CS13⁻ ∷ X3 ∷ CS12 ∷ []) (CS12 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ [])
  b0 = at 0 4 (CS12 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) wn00249 ▸ done

-- pass [X3 CSd31 X3] [CSd12]: 1 steps
lem-pass-X3-CSd31-X3-vs-CSd12 : ⟪ (X3 ∷ CS13⁻ ∷ X3 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CSd31-X3-vs-CSd12 = run b0
  where
  b0 : Chain (X3 ∷ CS13⁻ ∷ X3 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ X3 ∷ CS13⁻ ∷ X3 ∷ [])
  b0 = at 0 4 (CS12⁻ ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) wn00250 ▸ done

-- pass [TOFF102] [X2 TOFF102 X2]: 1 steps
lem-pass-TOFF102-vs-X2-TOFF102-X2 : ⟪ (Toff102 ∷ X2 ∷ Toff102 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff102 ∷ X2 ∷ Toff102 ∷ []) ⟫ʷ
lem-pass-TOFF102-vs-X2-TOFF102-X2 = run b0
  where
  b0 : Chain (Toff102 ∷ X2 ∷ Toff102 ∷ X2 ∷ []) (X2 ∷ Toff102 ∷ X2 ∷ Toff102 ∷ [])
  b0 = at 0 4 (X2 ∷ Toff102 ∷ X2 ∷ Toff102 ∷ []) wn00305 ▸ done

-- pass [CS12] [X2 TOFF102 X2]: 1 steps
lem-pass-CS12-vs-X2-TOFF102-X2 : ⟪ (CS12 ∷ X2 ∷ Toff102 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff102 ∷ X2 ∷ CS12 ∷ []) ⟫ʷ
lem-pass-CS12-vs-X2-TOFF102-X2 = run b0
  where
  b0 : Chain (CS12 ∷ X2 ∷ Toff102 ∷ X2 ∷ []) (X2 ∷ Toff102 ∷ X2 ∷ CS12 ∷ [])
  b0 = at 0 4 (X2 ∷ Toff102 ∷ X2 ∷ CS12 ∷ []) wn00299 ▸ done

-- pass [CSd12] [X2 TOFF102 X2]: 1 steps
lem-pass-CSd12-vs-X2-TOFF102-X2 : ⟪ (CS12⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff102 ∷ X2 ∷ CS12⁻ ∷ []) ⟫ʷ
lem-pass-CSd12-vs-X2-TOFF102-X2 = run b0
  where
  b0 : Chain (CS12⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ []) (X2 ∷ Toff102 ∷ X2 ∷ CS12⁻ ∷ [])
  b0 = at 0 4 (X2 ∷ Toff102 ∷ X2 ∷ CS12⁻ ∷ []) wn00300 ▸ done

-- pass [CCZ013] [CZ03]: 49 steps
lem-pass-CCZ013-vs-CZ03 : ⟪ (CCZ013 ∷ CZ03 ∷ []) ⟫ʷ ≈ ⟪ (CZ03 ∷ CCZ013 ∷ []) ⟫ʷ
lem-pass-CCZ013-vs-CZ03 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (run b6))))))
  where
  b0 : Chain (CCZ013 ∷ CZ03 ∷ []) (CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ CZ02 ∷ Sw23 ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 1 (Sw23 ∷ CZ02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] wn00003 ▸
       at 0 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 0 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b1 : Chain (CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ CZ02 ∷ Sw23 ∷ []) (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ CZ02 ∷ Sw23 ∷ [])
  b1 = at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 4 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00003 ▸
       at 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00003 ▸ done

  b2 : Chain (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ CZ02 ∷ Sw23 ∷ []) (Sw23 ∷ CCZ012 ∷ CZ02 ∷ Sw23 ∷ [])
  b2 = at 3 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 2 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00003 ▸
       at 1 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 0 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00003 ▸
       at 1 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) wn00043 ▸
       at 1 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸ done

  b3 : Chain (Sw23 ∷ CCZ012 ∷ CZ02 ∷ Sw23 ∷ []) (CZ03 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ Sw23 ∷ [])
  b3 = at 1 2 (CZ02 ∷ CCZ012 ∷ []) wn00301 ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 0 3 (CZ03 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b4 : Chain (CZ03 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ Sw23 ∷ []) (CZ03 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ Sw23 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw23 ∷ Sw23 ∷ [])
  b4 = at 3 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 5 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00003 ▸
       at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b5 : Chain (CZ03 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ Sw23 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw23 ∷ Sw23 ∷ []) (CZ03 ∷ CCZ013 ∷ Sw23 ∷ Sw23 ∷ [])
  b5 = at 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00003 ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00003 ▸
       at 2 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) wn00043 ▸
       at 2 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸ done

  b6 : Chain (CZ03 ∷ CCZ013 ∷ Sw23 ∷ Sw23 ∷ []) (CZ03 ∷ CCZ013 ∷ [])
  b6 = at 2 2 [] wn00003 ▸ done

-- pass [CS13] [CZ03]: 11 steps
lem-pass-CS13-vs-CZ03 : ⟪ (CS13 ∷ CZ03 ∷ []) ⟫ʷ ≈ ⟪ (CZ03 ∷ CS13 ∷ []) ⟫ʷ
lem-pass-CS13-vs-CZ03 = trans (run b0) (run b1)
  where
  b0 : Chain (CS13 ∷ CZ03 ∷ []) (CZ03 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 1 (Sw23 ∷ CZ02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] wn00003 ▸
       at 0 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00003 ▸
       at 1 2 (CZ02 ∷ CS12 ∷ []) wn00302 ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 0 3 (CZ03 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (CZ03 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ []) (CZ03 ∷ CS13 ∷ [])
  b1 = at 3 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00003 ▸ done

-- pass [CSd13] [CZ03]: 11 steps
lem-pass-CSd13-vs-CZ03 : ⟪ (CS13⁻ ∷ CZ03 ∷ []) ⟫ʷ ≈ ⟪ (CZ03 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-pass-CSd13-vs-CZ03 = trans (run b0) (run b1)
  where
  b0 : Chain (CS13⁻ ∷ CZ03 ∷ []) (CZ03 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 1 (Sw23 ∷ CZ02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] wn00003 ▸
       at 0 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00003 ▸
       at 1 2 (CZ02 ∷ CS12⁻ ∷ []) wn00303 ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 0 3 (CZ03 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (CZ03 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (CZ03 ∷ CS13⁻ ∷ [])
  b1 = at 3 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00003 ▸ done

-- pass [X2 CSd21 X2] [TOFF102]: 1 steps
lem-pass-X2-CSd21-X2-vs-TOFF102 : ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CSd21-X2-vs-TOFF102 = run b0
  where
  b0 : Chain (X2 ∷ CS12⁻ ∷ X2 ∷ Toff102 ∷ []) (Toff102 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ [])
  b0 = at 0 4 (Toff102 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) wn00304 ▸ done

-- pass [X2 CSd21 X2] [CS13]: 1 steps
lem-pass-X2-CSd21-X2-vs-CS13 : ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CSd21-X2-vs-CS13 = run b0
  where
  b0 : Chain (X2 ∷ CS12⁻ ∷ X2 ∷ CS13 ∷ []) (CS13 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ [])
  b0 = at 0 4 (CS13 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) wn00287 ▸ done

-- pass [X2 CSd21 X2] [CSd13]: 1 steps
lem-pass-X2-CSd21-X2-vs-CSd13 : ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CSd21-X2-vs-CSd13 = run b0
  where
  b0 : Chain (X2 ∷ CS12⁻ ∷ X2 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ X2 ∷ CS12⁻ ∷ X2 ∷ [])
  b0 = at 0 4 (CS13⁻ ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) wn00288 ▸ done

-- pass [S1] [CS13]: 1 steps
lem-pass-S1-vs-CS13 : ⟪ (S1 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ S1 ∷ []) ⟫ʷ
lem-pass-S1-vs-CS13 = run b0
  where
  b0 : Chain (S1 ∷ CS13 ∷ []) (CS13 ∷ S1 ∷ [])
  b0 = at 0 2 (CS13 ∷ S1 ∷ []) wn00306 ▸ done

-- pass [CCZ012] [CS02]: 1 steps
lem-pass-CCZ012-vs-CS02 : ⟪ (CCZ012 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CCZ012 ∷ []) ⟫ʷ
lem-pass-CCZ012-vs-CS02 = run b0
  where
  b0 : Chain (CCZ012 ∷ CS02 ∷ []) (CS02 ∷ CCZ012 ∷ [])
  b0 = at 0 2 (CS02 ∷ CCZ012 ∷ []) wn00251 ▸ done

-- pass [S1] [CSd13]: 1 steps
lem-pass-S1-vs-CSd13 : ⟪ (S1 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ S1 ∷ []) ⟫ʷ
lem-pass-S1-vs-CSd13 = run b0
  where
  b0 : Chain (S1 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ S1 ∷ [])
  b0 = at 0 2 (CS13⁻ ∷ S1 ∷ []) wn00307 ▸ done

-- pass [Sd1] [CS13]: 1 steps
lem-pass-Sd1-vs-CS13 : ⟪ (S1⁻ ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ S1⁻ ∷ []) ⟫ʷ
lem-pass-Sd1-vs-CS13 = run b0
  where
  b0 : Chain (S1⁻ ∷ CS13 ∷ []) (CS13 ∷ S1⁻ ∷ [])
  b0 = at 0 2 (CS13 ∷ S1⁻ ∷ []) wn00308 ▸ done

-- pass [CCZ012] [CSd02]: 1 steps
lem-pass-CCZ012-vs-CSd02 : ⟪ (CCZ012 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ CCZ012 ∷ []) ⟫ʷ
lem-pass-CCZ012-vs-CSd02 = run b0
  where
  b0 : Chain (CCZ012 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CCZ012 ∷ [])
  b0 = at 0 2 (CS02⁻ ∷ CCZ012 ∷ []) wn00254 ▸ done

-- pass [Sd1] [CSd13]: 1 steps
lem-pass-Sd1-vs-CSd13 : ⟪ (S1⁻ ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ S1⁻ ∷ []) ⟫ʷ
lem-pass-Sd1-vs-CSd13 = run b0
  where
  b0 : Chain (S1⁻ ∷ CS13⁻ ∷ []) (CS13⁻ ∷ S1⁻ ∷ [])
  b0 = at 0 2 (CS13⁻ ∷ S1⁻ ∷ []) wn00309 ▸ done

-- bridge G-pp: 43 steps
lem-bridge-G-pp : ⟪ (Toff012 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ Toff012 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ CS12 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-bridge-G-pp = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (run b5)))))
  where
  b0 : Chain (Toff012 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ Toff012 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ CS12 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ []) (Toff012 ∷ CS03 ∷ Sw01 ∷ Sw01 ∷ Toff012 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ CS12 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ [])
  b0 = at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] wn00003 ▸
       at 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 2 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 3 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 1 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Toff012 ∷ CS03 ∷ Sw01 ∷ Sw01 ∷ Toff012 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ CS12 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ Sw01 ∷ CS13 ∷ CS13 ∷ CS13 ∷ Sw01 ∷ [])
  b1 = at 2 2 [] wn00031 ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 5 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] wn00003 ▸ done

  b2 : Chain (Toff012 ∷ CS03 ∷ Toff012 ∷ Sw01 ∷ CS13 ∷ CS13 ∷ CS13 ∷ Sw01 ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03 ∷ Sw23 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ CS13 ∷ Sw01 ∷ [])
  b2 = at 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 4 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 3 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸ done

  b3 : Chain (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03 ∷ Sw23 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ CS13 ∷ Sw01 ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03 ∷ CS03 ∷ CS03 ∷ [])
  b3 = at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 4 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00031 ▸ done

  b4 : Chain (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03 ∷ CS03 ∷ CS03 ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ [])
  b4 = at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] wn00003 ▸
       at 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00003 ▸
       at 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00003 ▸
       at 4 3 (CS02⁻ ∷ []) wn00310 ▸ done

  b5 : Chain (Toff012 ∷ CS03 ∷ Toff012 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ [])
  b5 = at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00003 ▸ done

-- sw0 S0: 2 steps
lem-sw0-S0 : ⟪ (Sw01 ∷ S0 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ []) ⟫ʷ
lem-sw0-S0 = run b0
  where
  b0 : Chain (Sw01 ∷ S0 ∷ Sw01 ∷ []) (S1 ∷ [])
  b0 = at 0 2 (S1 ∷ Sw01 ∷ []) wn00311 ▸
       at 1 2 [] wn00031 ▸ done

-- sw0 Sd0: 2 steps
lem-sw0-Sd0 : ⟪ (Sw01 ∷ S0⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (S1⁻ ∷ []) ⟫ʷ
lem-sw0-Sd0 = run b0
  where
  b0 : Chain (Sw01 ∷ S0⁻ ∷ Sw01 ∷ []) (S1⁻ ∷ [])
  b0 = at 0 2 (S1⁻ ∷ Sw01 ∷ []) wn00312 ▸
       at 1 2 [] wn00031 ▸ done

-- sw0 K0: 2 steps
lem-sw0-K0 : ⟪ (Sw01 ∷ K0 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (K1 ∷ []) ⟫ʷ
lem-sw0-K0 = run b0
  where
  b0 : Chain (Sw01 ∷ K0 ∷ Sw01 ∷ []) (K1 ∷ [])
  b0 = at 0 2 (K1 ∷ Sw01 ∷ []) wn00123 ▸
       at 1 2 [] wn00031 ▸ done

-- sw0 Kd0: 2 steps
lem-sw0-Kd0 : ⟪ (Sw01 ∷ K0⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (K1⁻ ∷ []) ⟫ʷ
lem-sw0-Kd0 = run b0
  where
  b0 : Chain (Sw01 ∷ K0⁻ ∷ Sw01 ∷ []) (K1⁻ ∷ [])
  b0 = at 0 2 (K1⁻ ∷ Sw01 ∷ []) wn00313 ▸
       at 1 2 [] wn00031 ▸ done

-- sw0 X0: 2 steps
lem-sw0-X0 : ⟪ (Sw01 ∷ X0 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ []) ⟫ʷ
lem-sw0-X0 = run b0
  where
  b0 : Chain (Sw01 ∷ X0 ∷ Sw01 ∷ []) (X1 ∷ [])
  b0 = at 0 2 (X1 ∷ Sw01 ∷ []) wn00220 ▸
       at 1 2 [] wn00031 ▸ done

-- sw0 Z0: 2 steps
lem-sw0-Z0 : ⟪ (Sw01 ∷ Z0 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Z1 ∷ []) ⟫ʷ
lem-sw0-Z0 = run b0
  where
  b0 : Chain (Sw01 ∷ Z0 ∷ Sw01 ∷ []) (Z1 ∷ [])
  b0 = at 0 2 (Z1 ∷ Sw01 ∷ []) wn00314 ▸
       at 1 2 [] wn00031 ▸ done

-- sw0 S1: 2 steps
lem-sw0-S1 : ⟪ (Sw01 ∷ S1 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ []) ⟫ʷ
lem-sw0-S1 = run b0
  where
  b0 : Chain (Sw01 ∷ S1 ∷ Sw01 ∷ []) (S0 ∷ [])
  b0 = at 0 2 (S0 ∷ Sw01 ∷ []) wn00315 ▸
       at 1 2 [] wn00031 ▸ done

-- sw0 Sd1: 2 steps
lem-sw0-Sd1 : ⟪ (Sw01 ∷ S1⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ []) ⟫ʷ
lem-sw0-Sd1 = run b0
  where
  b0 : Chain (Sw01 ∷ S1⁻ ∷ Sw01 ∷ []) (S0⁻ ∷ [])
  b0 = at 0 2 (S0⁻ ∷ Sw01 ∷ []) wn00316 ▸
       at 1 2 [] wn00031 ▸ done

-- sw0 K1: 2 steps
lem-sw0-K1 : ⟪ (Sw01 ∷ K1 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ []) ⟫ʷ
lem-sw0-K1 = run b0
  where
  b0 : Chain (Sw01 ∷ K1 ∷ Sw01 ∷ []) (K0 ∷ [])
  b0 = at 0 2 (K0 ∷ Sw01 ∷ []) wn00121 ▸
       at 1 2 [] wn00031 ▸ done

-- sw0 Kd1: 2 steps
lem-sw0-Kd1 : ⟪ (Sw01 ∷ K1⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ []) ⟫ʷ
lem-sw0-Kd1 = run b0
  where
  b0 : Chain (Sw01 ∷ K1⁻ ∷ Sw01 ∷ []) (K0⁻ ∷ [])
  b0 = at 0 2 (K0⁻ ∷ Sw01 ∷ []) wn00129 ▸
       at 1 2 [] wn00031 ▸ done

-- sw0 X1: 2 steps
lem-sw0-X1 : ⟪ (Sw01 ∷ X1 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ []) ⟫ʷ
lem-sw0-X1 = run b0
  where
  b0 : Chain (Sw01 ∷ X1 ∷ Sw01 ∷ []) (X0 ∷ [])
  b0 = at 0 2 (X0 ∷ Sw01 ∷ []) wn00317 ▸
       at 1 2 [] wn00031 ▸ done

-- sw0 Z1: 2 steps
lem-sw0-Z1 : ⟪ (Sw01 ∷ Z1 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Z0 ∷ []) ⟫ʷ
lem-sw0-Z1 = run b0
  where
  b0 : Chain (Sw01 ∷ Z1 ∷ Sw01 ∷ []) (Z0 ∷ [])
  b0 = at 0 2 (Z0 ∷ Sw01 ∷ []) wn00318 ▸
       at 1 2 [] wn00031 ▸ done

-- sw0 S2: 2 steps
lem-sw0-S2 : ⟪ (Sw01 ∷ S2 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (S2 ∷ []) ⟫ʷ
lem-sw0-S2 = run b0
  where
  b0 : Chain (Sw01 ∷ S2 ∷ Sw01 ∷ []) (S2 ∷ [])
  b0 = at 0 2 (S2 ∷ Sw01 ∷ []) (low-comm (Swap) (S)) ▸
       at 1 2 [] wn00031 ▸ done

-- sw0 Sd2: 2 steps
lem-sw0-Sd2 : ⟪ (Sw01 ∷ S2⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (S2⁻ ∷ []) ⟫ʷ
lem-sw0-Sd2 = run b0
  where
  b0 : Chain (Sw01 ∷ S2⁻ ∷ Sw01 ∷ []) (S2⁻ ∷ [])
  b0 = at 0 2 (S2⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((S • S • S))) ▸
       at 1 2 [] wn00031 ▸ done

-- sw0 K2: 2 steps
lem-sw0-K2 : ⟪ (Sw01 ∷ K2 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (K2 ∷ []) ⟫ʷ
lem-sw0-K2 = run b0
  where
  b0 : Chain (Sw01 ∷ K2 ∷ Sw01 ∷ []) (K2 ∷ [])
  b0 = at 0 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 1 2 [] wn00031 ▸ done

-- sw0 Kd2: 2 steps
lem-sw0-Kd2 : ⟪ (Sw01 ∷ K2⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (K2⁻ ∷ []) ⟫ʷ
lem-sw0-Kd2 = run b0
  where
  b0 : Chain (Sw01 ∷ K2⁻ ∷ Sw01 ∷ []) (K2⁻ ∷ [])
  b0 = at 0 2 (K2⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((K • iI))) ▸
       at 1 2 [] wn00031 ▸ done

-- sw0 X2: 2 steps
lem-sw0-X2 : ⟪ (Sw01 ∷ X2 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ []) ⟫ʷ
lem-sw0-X2 = run b0
  where
  b0 : Chain (Sw01 ∷ X2 ∷ Sw01 ∷ []) (X2 ∷ [])
  b0 = at 0 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸
       at 1 2 [] wn00031 ▸ done

-- sw0 Z2: 2 steps
lem-sw0-Z2 : ⟪ (Sw01 ∷ Z2 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Z2 ∷ []) ⟫ʷ
lem-sw0-Z2 = run b0
  where
  b0 : Chain (Sw01 ∷ Z2 ∷ Sw01 ∷ []) (Z2 ∷ [])
  b0 = at 0 2 (Z2 ∷ Sw01 ∷ []) (low-comm (Swap) (Z)) ▸
       at 1 2 [] wn00031 ▸ done

-- sw0 S3: 2 steps
lem-sw0-S3 : ⟪ (Sw01 ∷ S3 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (S3 ∷ []) ⟫ʷ
lem-sw0-S3 = run b0
  where
  b0 : Chain (Sw01 ∷ S3 ∷ Sw01 ∷ []) (S3 ∷ [])
  b0 = at 0 2 (S3 ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑))) ▸
       at 1 2 [] wn00031 ▸ done

-- sw0 Sd3: 2 steps
lem-sw0-Sd3 : ⟪ (Sw01 ∷ S3⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (S3⁻ ∷ []) ⟫ʷ
lem-sw0-Sd3 = run b0
  where
  b0 : Chain (Sw01 ∷ S3⁻ ∷ Sw01 ∷ []) (S3⁻ ∷ [])
  b0 = at 0 2 (S3⁻ ∷ Sw01 ∷ []) (low-comm (Swap) (((S • S • S) ↑))) ▸
       at 1 2 [] wn00031 ▸ done

-- sw0 K3: 2 steps
lem-sw0-K3 : ⟪ (Sw01 ∷ K3 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (K3 ∷ []) ⟫ʷ
lem-sw0-K3 = run b0
  where
  b0 : Chain (Sw01 ∷ K3 ∷ Sw01 ∷ []) (K3 ∷ [])
  b0 = at 0 2 (K3 ∷ Sw01 ∷ []) (low-comm (Swap) ((K ↑))) ▸
       at 1 2 [] wn00031 ▸ done

-- sw0 Kd3: 2 steps
lem-sw0-Kd3 : ⟪ (Sw01 ∷ K3⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (K3⁻ ∷ []) ⟫ʷ
lem-sw0-Kd3 = run b0
  where
  b0 : Chain (Sw01 ∷ K3⁻ ∷ Sw01 ∷ []) (K3⁻ ∷ [])
  b0 = at 0 2 (K3⁻ ∷ Sw01 ∷ []) (low-comm (Swap) (((K • iI) ↑))) ▸
       at 1 2 [] wn00031 ▸ done

-- sw0 X3: 2 steps
lem-sw0-X3 : ⟪ (Sw01 ∷ X3 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ []) ⟫ʷ
lem-sw0-X3 = run b0
  where
  b0 : Chain (Sw01 ∷ X3 ∷ Sw01 ∷ []) (X3 ∷ [])
  b0 = at 0 2 (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑))) ▸
       at 1 2 [] wn00031 ▸ done

-- sw0 Z3: 2 steps
lem-sw0-Z3 : ⟪ (Sw01 ∷ Z3 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Z3 ∷ []) ⟫ʷ
lem-sw0-Z3 = run b0
  where
  b0 : Chain (Sw01 ∷ Z3 ∷ Sw01 ∷ []) (Z3 ∷ [])
  b0 = at 0 2 (Z3 ∷ Sw01 ∷ []) (low-comm (Swap) ((Z ↑))) ▸
       at 1 2 [] wn00031 ▸ done

-- sw0 CS01: 2 steps
lem-sw0-CS01 : ⟪ (Sw01 ∷ CS01 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ []) ⟫ʷ
lem-sw0-CS01 = run b0
  where
  b0 : Chain (Sw01 ∷ CS01 ∷ Sw01 ∷ []) (CS01 ∷ [])
  b0 = at 0 2 (CS01 ∷ Sw01 ∷ []) wn00219 ▸
       at 1 2 [] wn00031 ▸ done

-- sw0 CSd01: 2 steps
lem-sw0-CSd01 : ⟪ (Sw01 ∷ CS01⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ []) ⟫ʷ
lem-sw0-CSd01 = run b0
  where
  b0 : Chain (Sw01 ∷ CS01⁻ ∷ Sw01 ∷ []) (CS01⁻ ∷ [])
  b0 = at 0 2 (CS01⁻ ∷ Sw01 ∷ []) wn00319 ▸
       at 1 2 [] wn00031 ▸ done

-- sw0 CZ01: 2 steps
lem-sw0-CZ01 : ⟪ (Sw01 ∷ CZ01 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CZ01 ∷ []) ⟫ʷ
lem-sw0-CZ01 = run b0
  where
  b0 : Chain (Sw01 ∷ CZ01 ∷ Sw01 ∷ []) (CZ01 ∷ [])
  b0 = at 0 2 (CZ01 ∷ Sw01 ∷ []) wn00320 ▸
       at 1 2 [] wn00031 ▸ done

-- sw0 CX01: 2 steps
lem-sw0-CX01 : ⟪ (Sw01 ∷ CX01 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CX10 ∷ []) ⟫ʷ
lem-sw0-CX01 = run b0
  where
  b0 : Chain (Sw01 ∷ CX01 ∷ Sw01 ∷ []) (CX10 ∷ [])
  b0 = at 0 2 (CX10 ∷ Sw01 ∷ []) wn00028 ▸
       at 1 2 [] wn00031 ▸ done

-- sw0 CK01: 2 steps
lem-sw0-CK01 : ⟪ (Sw01 ∷ CK01 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CK10 ∷ []) ⟫ʷ
lem-sw0-CK01 = run b0
  where
  b0 : Chain (Sw01 ∷ CK01 ∷ Sw01 ∷ []) (CK10 ∷ [])
  b0 = at 0 2 (CK10 ∷ Sw01 ∷ []) wn00221 ▸
       at 1 2 [] wn00031 ▸ done

-- sw0 CKd01: 2 steps
lem-sw0-CKd01 : ⟪ (Sw01 ∷ CK01⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CK10⁻ ∷ []) ⟫ʷ
lem-sw0-CKd01 = run b0
  where
  b0 : Chain (Sw01 ∷ CK01⁻ ∷ Sw01 ∷ []) (CK10⁻ ∷ [])
  b0 = at 0 2 (CK10⁻ ∷ Sw01 ∷ []) wn00321 ▸
       at 1 2 [] wn00031 ▸ done

-- sw0 CS02: 2 steps
lem-sw0-CS02 : ⟪ (Sw01 ∷ CS02 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ []) ⟫ʷ
lem-sw0-CS02 = run b0
  where
  b0 : Chain (Sw01 ∷ CS02 ∷ Sw01 ∷ []) (CS12 ∷ [])
  b0 = at 0 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 1 2 [] wn00031 ▸ done

-- sw0 CSd02: 2 steps
lem-sw0-CSd02 : ⟪ (Sw01 ∷ CS02⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ []) ⟫ʷ
lem-sw0-CSd02 = run b0
  where
  b0 : Chain (Sw01 ∷ CS02⁻ ∷ Sw01 ∷ []) (CS12⁻ ∷ [])
  b0 = at 0 2 (CS12⁻ ∷ Sw01 ∷ []) wn00322 ▸
       at 1 2 [] wn00031 ▸ done

-- sw0 CZ02: 2 steps
lem-sw0-CZ02 : ⟪ (Sw01 ∷ CZ02 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CZ12 ∷ []) ⟫ʷ
lem-sw0-CZ02 = run b0
  where
  b0 : Chain (Sw01 ∷ CZ02 ∷ Sw01 ∷ []) (CZ12 ∷ [])
  b0 = at 0 2 (CZ12 ∷ Sw01 ∷ []) wn00323 ▸
       at 1 2 [] wn00031 ▸ done

-- sw0 CX02: 2 steps
lem-sw0-CX02 : ⟪ (Sw01 ∷ CX02 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CX12 ∷ []) ⟫ʷ
lem-sw0-CX02 = run b0
  where
  b0 : Chain (Sw01 ∷ CX02 ∷ Sw01 ∷ []) (CX12 ∷ [])
  b0 = at 0 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 1 2 [] wn00031 ▸ done

-- sw0 CK02: 2 steps
lem-sw0-CK02 : ⟪ (Sw01 ∷ CK02 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CK12 ∷ []) ⟫ʷ
lem-sw0-CK02 = run b0
  where
  b0 : Chain (Sw01 ∷ CK02 ∷ Sw01 ∷ []) (CK12 ∷ [])
  b0 = at 0 2 (CK12 ∷ Sw01 ∷ []) wn00324 ▸
       at 1 2 [] wn00031 ▸ done

-- sw0 CKd02: 2 steps
lem-sw0-CKd02 : ⟪ (Sw01 ∷ CK02⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CK12⁻ ∷ []) ⟫ʷ
lem-sw0-CKd02 = run b0
  where
  b0 : Chain (Sw01 ∷ CK02⁻ ∷ Sw01 ∷ []) (CK12⁻ ∷ [])
  b0 = at 0 2 (CK12⁻ ∷ Sw01 ∷ []) wn00325 ▸
       at 1 2 [] wn00031 ▸ done

-- sw0 CS03: 6 steps
lem-sw0-CS03 : ⟪ (Sw01 ∷ CS03 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ []) ⟫ʷ
lem-sw0-CS03 = run b0
  where
  b0 : Chain (Sw01 ∷ CS03 ∷ Sw01 ∷ []) (CS13 ∷ [])
  b0 = at 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 1 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 2 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 0 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00031 ▸ done

-- sw0 CSd03: 6 steps
lem-sw0-CSd03 : ⟪ (Sw01 ∷ CS03⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ []) ⟫ʷ
lem-sw0-CSd03 = run b0
  where
  b0 : Chain (Sw01 ∷ CS03⁻ ∷ Sw01 ∷ []) (CS13⁻ ∷ [])
  b0 = at 1 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 1 2 (CS12⁻ ∷ Sw01 ∷ []) wn00322 ▸
       at 2 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 0 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00031 ▸ done

-- sw0 CZ03: 6 steps
lem-sw0-CZ03 : ⟪ (Sw01 ∷ CZ03 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CZ13 ∷ []) ⟫ʷ
lem-sw0-CZ03 = run b0
  where
  b0 : Chain (Sw01 ∷ CZ03 ∷ Sw01 ∷ []) (CZ13 ∷ [])
  b0 = at 1 1 (Sw23 ∷ CZ02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 1 2 (CZ12 ∷ Sw01 ∷ []) wn00323 ▸
       at 2 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 0 3 (CZ13 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00031 ▸ done

-- sw0 CX03: 6 steps
lem-sw0-CX03 : ⟪ (Sw01 ∷ CX03 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CX13 ∷ []) ⟫ʷ
lem-sw0-CX03 = run b0
  where
  b0 : Chain (Sw01 ∷ CX03 ∷ Sw01 ∷ []) (CX13 ∷ [])
  b0 = at 1 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 1 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 2 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 0 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00031 ▸ done

-- sw0 CK03: 6 steps
lem-sw0-CK03 : ⟪ (Sw01 ∷ CK03 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CK13 ∷ []) ⟫ʷ
lem-sw0-CK03 = run b0
  where
  b0 : Chain (Sw01 ∷ CK03 ∷ Sw01 ∷ []) (CK13 ∷ [])
  b0 = at 1 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 1 2 (CK12 ∷ Sw01 ∷ []) wn00324 ▸
       at 2 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 0 3 (CK13 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00031 ▸ done

-- sw0 CKd03: 6 steps
lem-sw0-CKd03 : ⟪ (Sw01 ∷ CK03⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CK13⁻ ∷ []) ⟫ʷ
lem-sw0-CKd03 = run b0
  where
  b0 : Chain (Sw01 ∷ CK03⁻ ∷ Sw01 ∷ []) (CK13⁻ ∷ [])
  b0 = at 1 1 (Sw23 ∷ CK02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 1 2 (CK12⁻ ∷ Sw01 ∷ []) wn00325 ▸
       at 2 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 0 3 (CK13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00031 ▸ done

-- sw0 CX10: 2 steps
lem-sw0-CX10 : ⟪ (Sw01 ∷ CX10 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CX01 ∷ []) ⟫ʷ
lem-sw0-CX10 = run b0
  where
  b0 : Chain (Sw01 ∷ CX10 ∷ Sw01 ∷ []) (CX01 ∷ [])
  b0 = at 0 2 (CX01 ∷ Sw01 ∷ []) wn00326 ▸
       at 1 2 [] wn00031 ▸ done

-- sw0 CK10: 2 steps
lem-sw0-CK10 : ⟪ (Sw01 ∷ CK10 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CK01 ∷ []) ⟫ʷ
lem-sw0-CK10 = run b0
  where
  b0 : Chain (Sw01 ∷ CK10 ∷ Sw01 ∷ []) (CK01 ∷ [])
  b0 = at 0 2 (CK01 ∷ Sw01 ∷ []) wn00327 ▸
       at 1 2 [] wn00031 ▸ done

-- sw0 CKd10: 2 steps
lem-sw0-CKd10 : ⟪ (Sw01 ∷ CK10⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CK01⁻ ∷ []) ⟫ʷ
lem-sw0-CKd10 = run b0
  where
  b0 : Chain (Sw01 ∷ CK10⁻ ∷ Sw01 ∷ []) (CK01⁻ ∷ [])
  b0 = at 0 2 (CK01⁻ ∷ Sw01 ∷ []) wn00328 ▸
       at 1 2 [] wn00031 ▸ done

-- sw0 CS12: 2 steps
lem-sw0-CS12 : ⟪ (Sw01 ∷ CS12 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ []) ⟫ʷ
lem-sw0-CS12 = run b0
  where
  b0 : Chain (Sw01 ∷ CS12 ∷ Sw01 ∷ []) (CS02 ∷ [])
  b0 = at 0 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 1 2 [] wn00031 ▸ done

-- sw0 CSd12: 2 steps
lem-sw0-CSd12 : ⟪ (Sw01 ∷ CS12⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ []) ⟫ʷ
lem-sw0-CSd12 = run b0
  where
  b0 : Chain (Sw01 ∷ CS12⁻ ∷ Sw01 ∷ []) (CS02⁻ ∷ [])
  b0 = at 0 2 (CS02⁻ ∷ Sw01 ∷ []) wn00029 ▸
       at 1 2 [] wn00031 ▸ done

-- sw0 CZ12: 2 steps
lem-sw0-CZ12 : ⟪ (Sw01 ∷ CZ12 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CZ02 ∷ []) ⟫ʷ
lem-sw0-CZ12 = run b0
  where
  b0 : Chain (Sw01 ∷ CZ12 ∷ Sw01 ∷ []) (CZ02 ∷ [])
  b0 = at 0 2 (CZ02 ∷ Sw01 ∷ []) wn00191 ▸
       at 1 2 [] wn00031 ▸ done

-- sw0 CX12: 2 steps
lem-sw0-CX12 : ⟪ (Sw01 ∷ CX12 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CX02 ∷ []) ⟫ʷ
lem-sw0-CX12 = run b0
  where
  b0 : Chain (Sw01 ∷ CX12 ∷ Sw01 ∷ []) (CX02 ∷ [])
  b0 = at 0 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 1 2 [] wn00031 ▸ done

-- sw0 CK12: 2 steps
lem-sw0-CK12 : ⟪ (Sw01 ∷ CK12 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CK02 ∷ []) ⟫ʷ
lem-sw0-CK12 = run b0
  where
  b0 : Chain (Sw01 ∷ CK12 ∷ Sw01 ∷ []) (CK02 ∷ [])
  b0 = at 0 2 (CK02 ∷ Sw01 ∷ []) wn00329 ▸
       at 1 2 [] wn00031 ▸ done

-- sw0 CKd12: 2 steps
lem-sw0-CKd12 : ⟪ (Sw01 ∷ CK12⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CK02⁻ ∷ []) ⟫ʷ
lem-sw0-CKd12 = run b0
  where
  b0 : Chain (Sw01 ∷ CK12⁻ ∷ Sw01 ∷ []) (CK02⁻ ∷ [])
  b0 = at 0 2 (CK02⁻ ∷ Sw01 ∷ []) wn00330 ▸
       at 1 2 [] wn00031 ▸ done

-- sw0 CS13: 6 steps
lem-sw0-CS13 : ⟪ (Sw01 ∷ CS13 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ []) ⟫ʷ
lem-sw0-CS13 = run b0
  where
  b0 : Chain (Sw01 ∷ CS13 ∷ Sw01 ∷ []) (CS03 ∷ [])
  b0 = at 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 1 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 2 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 0 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00031 ▸ done

-- sw0 CSd13: 6 steps
lem-sw0-CSd13 : ⟪ (Sw01 ∷ CS13⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ []) ⟫ʷ
lem-sw0-CSd13 = run b0
  where
  b0 : Chain (Sw01 ∷ CS13⁻ ∷ Sw01 ∷ []) (CS03⁻ ∷ [])
  b0 = at 1 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 1 2 (CS02⁻ ∷ Sw01 ∷ []) wn00029 ▸
       at 2 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 0 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00031 ▸ done

-- sw0 CZ13: 6 steps
lem-sw0-CZ13 : ⟪ (Sw01 ∷ CZ13 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CZ03 ∷ []) ⟫ʷ
lem-sw0-CZ13 = run b0
  where
  b0 : Chain (Sw01 ∷ CZ13 ∷ Sw01 ∷ []) (CZ03 ∷ [])
  b0 = at 1 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 1 2 (CZ02 ∷ Sw01 ∷ []) wn00191 ▸
       at 2 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 0 3 (CZ03 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00031 ▸ done

-- sw0 CX13: 6 steps
lem-sw0-CX13 : ⟪ (Sw01 ∷ CX13 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CX03 ∷ []) ⟫ʷ
lem-sw0-CX13 = run b0
  where
  b0 : Chain (Sw01 ∷ CX13 ∷ Sw01 ∷ []) (CX03 ∷ [])
  b0 = at 1 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 1 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 2 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 0 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00031 ▸ done

-- sw0 CK13: 6 steps
lem-sw0-CK13 : ⟪ (Sw01 ∷ CK13 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CK03 ∷ []) ⟫ʷ
lem-sw0-CK13 = run b0
  where
  b0 : Chain (Sw01 ∷ CK13 ∷ Sw01 ∷ []) (CK03 ∷ [])
  b0 = at 1 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 1 2 (CK02 ∷ Sw01 ∷ []) wn00329 ▸
       at 2 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 0 3 (CK03 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00031 ▸ done

-- sw0 CKd13: 6 steps
lem-sw0-CKd13 : ⟪ (Sw01 ∷ CK13⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CK03⁻ ∷ []) ⟫ʷ
lem-sw0-CKd13 = run b0
  where
  b0 : Chain (Sw01 ∷ CK13⁻ ∷ Sw01 ∷ []) (CK03⁻ ∷ [])
  b0 = at 1 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 1 2 (CK02⁻ ∷ Sw01 ∷ []) wn00330 ▸
       at 2 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 0 3 (CK03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00031 ▸ done

-- sw0 CX20: 2 steps
lem-sw0-CX20 : ⟪ (Sw01 ∷ CX20 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CX21 ∷ []) ⟫ʷ
lem-sw0-CX20 = run b0
  where
  b0 : Chain (Sw01 ∷ CX20 ∷ Sw01 ∷ []) (CX21 ∷ [])
  b0 = at 0 2 (CX21 ∷ Sw01 ∷ []) wn00331 ▸
       at 1 2 [] wn00031 ▸ done

-- sw0 CK20: 2 steps
lem-sw0-CK20 : ⟪ (Sw01 ∷ CK20 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CK21 ∷ []) ⟫ʷ
lem-sw0-CK20 = run b0
  where
  b0 : Chain (Sw01 ∷ CK20 ∷ Sw01 ∷ []) (CK21 ∷ [])
  b0 = at 0 2 (CK21 ∷ Sw01 ∷ []) wn00275 ▸
       at 1 2 [] wn00031 ▸ done

-- sw0 CKd20: 2 steps
lem-sw0-CKd20 : ⟪ (Sw01 ∷ CK20⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CK21⁻ ∷ []) ⟫ʷ
lem-sw0-CKd20 = run b0
  where
  b0 : Chain (Sw01 ∷ CK20⁻ ∷ Sw01 ∷ []) (CK21⁻ ∷ [])
  b0 = at 0 2 (CK21⁻ ∷ Sw01 ∷ []) wn00332 ▸
       at 1 2 [] wn00031 ▸ done

-- sw0 CX21: 2 steps
lem-sw0-CX21 : ⟪ (Sw01 ∷ CX21 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CX20 ∷ []) ⟫ʷ
lem-sw0-CX21 = run b0
  where
  b0 : Chain (Sw01 ∷ CX21 ∷ Sw01 ∷ []) (CX20 ∷ [])
  b0 = at 0 2 (CX20 ∷ Sw01 ∷ []) wn00039 ▸
       at 1 2 [] wn00031 ▸ done

-- sw0 CK21: 2 steps
lem-sw0-CK21 : ⟪ (Sw01 ∷ CK21 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CK20 ∷ []) ⟫ʷ
lem-sw0-CK21 = run b0
  where
  b0 : Chain (Sw01 ∷ CK21 ∷ Sw01 ∷ []) (CK20 ∷ [])
  b0 = at 0 2 (CK20 ∷ Sw01 ∷ []) wn00142 ▸
       at 1 2 [] wn00031 ▸ done

-- sw0 CKd21: 2 steps
lem-sw0-CKd21 : ⟪ (Sw01 ∷ CK21⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CK20⁻ ∷ []) ⟫ʷ
lem-sw0-CKd21 = run b0
  where
  b0 : Chain (Sw01 ∷ CK21⁻ ∷ Sw01 ∷ []) (CK20⁻ ∷ [])
  b0 = at 0 2 (CK20⁻ ∷ Sw01 ∷ []) wn00139 ▸
       at 1 2 [] wn00031 ▸ done

-- sw0 CS23: 2 steps
lem-sw0-CS23 : ⟪ (Sw01 ∷ CS23 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ []) ⟫ʷ
lem-sw0-CS23 = run b0
  where
  b0 : Chain (Sw01 ∷ CS23 ∷ Sw01 ∷ []) (CS23 ∷ [])
  b0 = at 0 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 1 2 [] wn00031 ▸ done

-- sw0 CSd23: 2 steps
lem-sw0-CSd23 : ⟪ (Sw01 ∷ CS23⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ []) ⟫ʷ
lem-sw0-CSd23 = run b0
  where
  b0 : Chain (Sw01 ∷ CS23⁻ ∷ Sw01 ∷ []) (CS23⁻ ∷ [])
  b0 = at 0 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 1 2 [] wn00031 ▸ done

-- sw0 CZ23: 2 steps
lem-sw0-CZ23 : ⟪ (Sw01 ∷ CZ23 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CZ23 ∷ []) ⟫ʷ
lem-sw0-CZ23 = run b0
  where
  b0 : Chain (Sw01 ∷ CZ23 ∷ Sw01 ∷ []) (CZ23 ∷ [])
  b0 = at 0 2 (CZ23 ∷ Sw01 ∷ []) (low-comm (Swap) (CZ)) ▸
       at 1 2 [] wn00031 ▸ done

-- sw0 CX23: 2 steps
lem-sw0-CX23 : ⟪ (Sw01 ∷ CX23 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CX23 ∷ []) ⟫ʷ
lem-sw0-CX23 = run b0
  where
  b0 : Chain (Sw01 ∷ CX23 ∷ Sw01 ∷ []) (CX23 ∷ [])
  b0 = at 0 2 (CX23 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₀₁)) ▸
       at 1 2 [] wn00031 ▸ done

-- sw0 CK23: 2 steps
lem-sw0-CK23 : ⟪ (Sw01 ∷ CK23 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CK23 ∷ []) ⟫ʷ
lem-sw0-CK23 = run b0
  where
  b0 : Chain (Sw01 ∷ CK23 ∷ Sw01 ∷ []) (CK23 ∷ [])
  b0 = at 0 2 (CK23 ∷ Sw01 ∷ []) (low-comm (Swap) (CK₀₁)) ▸
       at 1 2 [] wn00031 ▸ done

-- sw0 CKd23: 2 steps
lem-sw0-CKd23 : ⟪ (Sw01 ∷ CK23⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CK23⁻ ∷ []) ⟫ʷ
lem-sw0-CKd23 = run b0
  where
  b0 : Chain (Sw01 ∷ CK23⁻ ∷ Sw01 ∷ []) (CK23⁻ ∷ [])
  b0 = at 0 2 (CK23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((S • CK₀₁))) ▸
       at 1 2 [] wn00031 ▸ done

-- sw0 CX30: 6 steps
lem-sw0-CX30 : ⟪ (Sw01 ∷ CX30 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CX31 ∷ []) ⟫ʷ
lem-sw0-CX30 = run b0
  where
  b0 : Chain (Sw01 ∷ CX30 ∷ Sw01 ∷ []) (CX31 ∷ [])
  b0 = at 1 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 1 2 (CX21 ∷ Sw01 ∷ []) wn00331 ▸
       at 2 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 0 3 (CX31 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00031 ▸ done

-- sw0 CK30: 6 steps
lem-sw0-CK30 : ⟪ (Sw01 ∷ CK30 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CK31 ∷ []) ⟫ʷ
lem-sw0-CK30 = run b0
  where
  b0 : Chain (Sw01 ∷ CK30 ∷ Sw01 ∷ []) (CK31 ∷ [])
  b0 = at 1 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 1 2 (CK21 ∷ Sw01 ∷ []) wn00275 ▸
       at 2 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 0 3 (CK31 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00031 ▸ done

-- sw0 CKd30: 6 steps
lem-sw0-CKd30 : ⟪ (Sw01 ∷ CK30⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CK31⁻ ∷ []) ⟫ʷ
lem-sw0-CKd30 = run b0
  where
  b0 : Chain (Sw01 ∷ CK30⁻ ∷ Sw01 ∷ []) (CK31⁻ ∷ [])
  b0 = at 1 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 1 2 (CK21⁻ ∷ Sw01 ∷ []) wn00332 ▸
       at 2 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 0 3 (CK31⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00031 ▸ done

-- sw0 CX31: 6 steps
lem-sw0-CX31 : ⟪ (Sw01 ∷ CX31 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CX30 ∷ []) ⟫ʷ
lem-sw0-CX31 = run b0
  where
  b0 : Chain (Sw01 ∷ CX31 ∷ Sw01 ∷ []) (CX30 ∷ [])
  b0 = at 1 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 1 2 (CX20 ∷ Sw01 ∷ []) wn00039 ▸
       at 2 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 0 3 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00031 ▸ done

-- sw0 CK31: 6 steps
lem-sw0-CK31 : ⟪ (Sw01 ∷ CK31 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CK30 ∷ []) ⟫ʷ
lem-sw0-CK31 = run b0
  where
  b0 : Chain (Sw01 ∷ CK31 ∷ Sw01 ∷ []) (CK30 ∷ [])
  b0 = at 1 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 1 2 (CK20 ∷ Sw01 ∷ []) wn00142 ▸
       at 2 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 0 3 (CK30 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00031 ▸ done

-- sw0 CKd31: 6 steps
lem-sw0-CKd31 : ⟪ (Sw01 ∷ CK31⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CK30⁻ ∷ []) ⟫ʷ
lem-sw0-CKd31 = run b0
  where
  b0 : Chain (Sw01 ∷ CK31⁻ ∷ Sw01 ∷ []) (CK30⁻ ∷ [])
  b0 = at 1 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 1 2 (CK20⁻ ∷ Sw01 ∷ []) wn00139 ▸
       at 2 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 0 3 (CK30⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00031 ▸ done

-- sw0 CX32: 2 steps
lem-sw0-CX32 : ⟪ (Sw01 ∷ CX32 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CX32 ∷ []) ⟫ʷ
lem-sw0-CX32 = run b0
  where
  b0 : Chain (Sw01 ∷ CX32 ∷ Sw01 ∷ []) (CX32 ∷ [])
  b0 = at 0 2 (CX32 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₁₀)) ▸
       at 1 2 [] wn00031 ▸ done

-- sw0 CK32: 2 steps
lem-sw0-CK32 : ⟪ (Sw01 ∷ CK32 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CK32 ∷ []) ⟫ʷ
lem-sw0-CK32 = run b0
  where
  b0 : Chain (Sw01 ∷ CK32 ∷ Sw01 ∷ []) (CK32 ∷ [])
  b0 = at 0 2 (CK32 ∷ Sw01 ∷ []) (low-comm (Swap) (CK₁₀)) ▸
       at 1 2 [] wn00031 ▸ done

-- sw0 CKd32: 2 steps
lem-sw0-CKd32 : ⟪ (Sw01 ∷ CK32⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CK32⁻ ∷ []) ⟫ʷ
lem-sw0-CKd32 = run b0
  where
  b0 : Chain (Sw01 ∷ CK32⁻ ∷ Sw01 ∷ []) (CK32⁻ ∷ [])
  b0 = at 0 2 (CK32⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑ • CK₁₀))) ▸
       at 1 2 [] wn00031 ▸ done

-- sw0 CCZ012: 9 steps
lem-sw0-CCZ012 : ⟪ (Sw01 ∷ CCZ012 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ []) ⟫ʷ
lem-sw0-CCZ012 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw01 ∷ CCZ012 ∷ Sw01 ∷ []) (CCZ012 ∷ Sw01 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 1 2 (CX10 ∷ Sw01 ∷ []) wn00028 ▸
       at 2 2 (CS02⁻ ∷ Sw01 ∷ []) wn00029 ▸
       at 3 2 (CX10 ∷ Sw01 ∷ []) wn00028 ▸
       at 4 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 0 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) wn00011 ▸
       at 0 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (CCZ012 ∷ Sw01 ∷ Sw01 ∷ []) (CCZ012 ∷ [])
  b1 = at 1 2 [] wn00031 ▸ done

-- sw0 CCZ013: 41 steps
lem-sw0-CCZ013 : ⟪ (Sw01 ∷ CCZ013 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ []) ⟫ʷ
lem-sw0-CCZ013 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (run b5)))))
  where
  b0 : Chain (Sw01 ∷ CCZ013 ∷ Sw01 ∷ []) (Sw01 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b1 : Chain (Sw01 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ []) (CS03 ∷ Sw01 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw01 ∷ [])
  b1 = at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 5 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00003 ▸
       at 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 1 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 2 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 0 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (CS03 ∷ Sw01 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw01 ∷ []) (CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ Sw01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ [])
  b2 = at 1 2 (CX10 ∷ Sw01 ∷ []) wn00028 ▸
       at 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 3 2 (CS02⁻ ∷ Sw01 ∷ []) wn00029 ▸
       at 4 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 2 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX10 ∷ Sw01 ∷ []) wn00028 ▸
       at 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b3 : Chain (CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ Sw01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ []) (Sw23 ∷ CS02 ∷ CX10 ∷ Sw23 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ Sw01 ∷ Sw01 ∷ [])
  b3 = at 4 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00003 ▸
       at 2 2 (CX10 ∷ Sw23 ∷ []) (sym (low-comm (CX₁₀) (Swap))) ▸ done

  b4 : Chain (Sw23 ∷ CS02 ∷ CX10 ∷ Sw23 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ Sw01 ∷ Sw01 ∷ []) (CCZ013 ∷ Sw01 ∷ Sw01 ∷ [])
  b4 = at 4 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] wn00003 ▸
       at 4 2 (CX10 ∷ Sw23 ∷ []) (sym (low-comm (CX₁₀) (Swap))) ▸
       at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00003 ▸
       at 1 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) wn00011 ▸
       at 1 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸ done

  b5 : Chain (CCZ013 ∷ Sw01 ∷ Sw01 ∷ []) (CCZ013 ∷ [])
  b5 = at 1 2 [] wn00031 ▸ done

-- sw0 CCZ023: 24 steps
lem-sw0-CCZ023 : ⟪ (Sw01 ∷ CCZ023 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ []) ⟫ʷ
lem-sw0-CCZ023 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw01 ∷ CCZ023 ∷ Sw01 ∷ []) (Sw01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 2 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 3 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 4 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b1 : Chain (Sw01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ []) (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw01 ∷ CS03 ∷ Sw01 ∷ [])
  b1 = at 6 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00031 ▸
       at 0 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 1 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 2 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 3 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸ done

  b2 : Chain (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw01 ∷ CS03 ∷ Sw01 ∷ []) (CCZ123 ∷ [])
  b2 = at 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 0 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) wn00026 ▸
       at 0 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00031 ▸ done

-- sw0 CCZ123: 24 steps
lem-sw0-CCZ123 : ⟪ (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ []) ⟫ʷ
lem-sw0-CCZ123 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) (CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 1 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 2 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 3 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸ done

  b1 : Chain (CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ Sw01 ∷ []) (Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ [])
  b1 = at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 4 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 1 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 2 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 3 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 4 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ []) (CCZ023 ∷ [])
  b2 = at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 1 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) wn00026 ▸
       at 1 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00031 ▸ done

-- sw0 TOFF012: 12 steps
lem-sw0-TOFF012 : ⟪ (Sw01 ∷ Toff012 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ []) ⟫ʷ
lem-sw0-TOFF012 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw01 ∷ Toff012 ∷ Sw01 ∷ []) (K1 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K1 ∷ Sw01 ∷ ι ∷ Sw01 ∷ [])
  b0 = at 1 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (K1 ∷ Sw01 ∷ []) wn00123 ▸
       at 1 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 2 2 (CX10 ∷ Sw01 ∷ []) wn00028 ▸
       at 3 2 (CS02⁻ ∷ Sw01 ∷ []) wn00029 ▸
       at 4 2 (CX10 ∷ Sw01 ∷ []) wn00028 ▸
       at 5 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 6 2 (K1 ∷ Sw01 ∷ []) wn00123 ▸ done

  b1 : Chain (K1 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K1 ∷ Sw01 ∷ ι ∷ Sw01 ∷ []) (Toff102 ∷ [])
  b1 = at 7 2 (ι1 ∷ Sw01 ∷ []) wn00124 ▸
       at 0 8 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) wn00274 ▸
       at 0 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00031 ▸ done

-- sw0 TOFF013: 50 steps
lem-sw0-TOFF013 : ⟪ (Sw01 ∷ Toff013 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Toff103 ∷ []) ⟫ʷ
lem-sw0-TOFF013 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (run b6))))))
  where
  b0 : Chain (Sw01 ∷ Toff013 ∷ Sw01 ∷ []) (Sw01 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 4 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw01 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw01 ∷ []) (K1 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw01 ∷ [])
  b1 = at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 8 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 9 2 [] wn00003 ▸
       at 0 2 (K1 ∷ Sw01 ∷ []) wn00123 ▸
       at 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (K1 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw01 ∷ []) (K1 ∷ CS03 ∷ CX10 ∷ Sw23 ∷ CS02⁻ ∷ Sw01 ∷ Sw23 ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw01 ∷ [])
  b2 = at 1 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 2 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 3 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 1 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CX10 ∷ Sw01 ∷ []) wn00028 ▸
       at 4 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 4 2 (CS02⁻ ∷ Sw01 ∷ []) wn00029 ▸ done

  b3 : Chain (K1 ∷ CS03 ∷ CX10 ∷ Sw23 ∷ CS02⁻ ∷ Sw01 ∷ Sw23 ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw01 ∷ []) (K1 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ Sw01 ∷ K0 ∷ ι ∷ Sw01 ∷ [])
  b3 = at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 3 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX10 ∷ Sw01 ∷ []) wn00028 ▸
       at 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b4 : Chain (K1 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ Sw01 ∷ K0 ∷ ι ∷ Sw01 ∷ []) (Sw23 ∷ K1 ∷ CS02 ∷ CX10 ∷ Sw23 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ CX10 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ [])
  b4 = at 6 2 (K1 ∷ Sw01 ∷ []) wn00123 ▸
       at 7 2 (ι1 ∷ Sw01 ∷ []) wn00124 ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00003 ▸
       at 3 2 (CX10 ∷ Sw23 ∷ []) (sym (low-comm (CX₁₀) (Swap))) ▸
       at 5 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b5 : Chain (Sw23 ∷ K1 ∷ CS02 ∷ CX10 ∷ Sw23 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ CX10 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ []) (Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ [])
  b5 = at 4 2 [] wn00003 ▸
       at 5 2 (CX10 ∷ Sw23 ∷ []) (sym (low-comm (CX₁₀) (Swap))) ▸
       at 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00003 ▸
       at 7 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 8 2 (ι1 ∷ Sw23 ∷ []) (sym (low-comm ((iI ↑)) (Swap))) ▸
       at 1 8 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) wn00274 ▸
       at 1 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸ done

  b6 : Chain (Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ []) (Toff103 ∷ [])
  b6 = at 0 3 (Toff103 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] wn00031 ▸ done
