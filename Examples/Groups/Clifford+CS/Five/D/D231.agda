{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D231 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Lits using (lw0 ; lw1 ; lw2 ; lw3 ; lw4)
open import Examples.Groups.Clifford+CS.Five.Resps using (pw0 ; pw1 ; pw2 ; pw3 ; pw4)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-F0)
open import Examples.Groups.Clifford+CS.Five.D.D135 using (lem-F1-CS-K1)
open import Examples.Groups.Clifford+CS.Five.D.D138 using (lem-F0-at011220 ; lem-F1-comm-CS-CS)
open import Examples.Groups.Clifford+CS.Five.D.D139 using (lem-F1-rel-266 ; lem-F1-rel-267)
open import Examples.Groups.Clifford+CS.Five.D.D140 using (lem-F1-rel-268)
open import Examples.Groups.Clifford+CS.Five.D.D191 using (lem-F0-at02132031)
open import Examples.Groups.Clifford+CS.Five.D.D230 using (lem-F1-CS-K0-at02132031)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-nat-0-SBOX⟨0·1·42·3⟩ ; lem-nat-0-SBOX⟨1·0·42·3⟩ ; lem-nat-1-SBOX⟨1·0·42·3⟩ ; lem-nat-1-SBOX⟨2·0·41·3⟩ ; lem-nat-1-SBOX⟨3·0·41·2⟩ ; lem-nat-2-SBOX⟨1·0·43·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R020 using (lem-nat-2-SBOX⟨0·1·42·3⟩ ; lem-nat-2-SBOX⟨0·1·43·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R021 using (lem-nat-0-SBOX⟨0·2·43·1⟩ ; lem-nat-0-SBOX⟨1·2·43·0⟩ ; lem-nat-1-SBOX⟨0·1·43·2⟩ ; lem-nat-1-SBOX⟨0·2·43·1⟩)
open import Examples.Groups.Clifford+CS.Five.D.R023 using (lem-nat-2-SBOX⟨1·0·42·3⟩)
open import Examples.Groups.Clifford+CS.Five.D.R032 using (lem-nat-0-SBOX⟨3·0·42·1⟩)
open import Examples.Groups.Clifford+CS.Five.D.R033 using (lem-nat-0-SBOX⟨0·1·43·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R034 using (lem-nat-0-CK41 ; lem-nat-0-SBOX⟨1·0·43·2⟩ ; lem-nat-1-CK40 ; lem-nat-2-CK40)
open import Examples.Groups.Clifford+CS.Five.D.R037 using (lem-nat-1-SBOX⟨3·0·42·1⟩ ; lem-nat-2-SBOX⟨2·0·41·3⟩ ; lem-nat-2-SBOX⟨3·0·41·2⟩)
open import Examples.Groups.Clifford+CS.Five.D.R043 using (lem-nat-0-SBOX⟨3·1·42·0⟩)
-- tr CS-K0 at 2: 1 steps
lem-tr-CS-K0-at-2 : Complete 4 → ⟪ (Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-tr-CS-K0-at-2 c4 = run b0
  where
  b0 : Chain (Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ CS24 ∷ []) (CS24 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ [])
  b0 = at 0 5 (CS24 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ []) (lem-F1-CS-K0-at02132031 c4) ▸ done


-- tr CS-K1 at 0: 1 steps
lem-tr-CS-K1-at-0 : Complete 4 → ⟪ (Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-tr-CS-K1-at-0 c4 = run b0
  where
  b0 : Chain (Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ CS14 ∷ []) (CS14 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ [])
  b0 = at 0 5 (CS14 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) (lem-F1-CS-K1 c4) ▸ done


-- F1 CS-K1 @1221: 13 steps
lem-F1-CS-K1-at1221 : Complete 4 → ⟪ (Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ CK42 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CK42 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ
lem-F1-CS-K1-at1221 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ CK42 ∷ CS24 ∷ []) (CS24 ∷ Sw12 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sw12 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ c4) ▸
       at 2 2 (CK41 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CK42 ∷ []) (CK41 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ c4) ▸
       at 4 2 (CK41 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CK42 ∷ []) (CK41 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CS14 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS24 ∷ []) (CS14 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 5 (CS14 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) (lem-F1-CS-K1 c4) ▸
       at 0 2 (CS24 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CS14 ∷ []) (CS24 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CS24 ∷ Sw12 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sw12 ∷ []) (CS24 ∷ CK42 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ [])
  b1 = at 1 2 (CK42 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CK41 ∷ []) (CK42 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·41·3⟩ c4) ▸
       at 3 2 (CK42 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CK41 ∷ []) (CK42 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Sb1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·41·3⟩ c4) ▸
       at 5 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- F1 CS-K1 @011220: 13 steps
lem-F1-CS-K1-at011220 : Complete 4 → ⟪ (Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-F1-CS-K1-at011220 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ CS24 ∷ []) (CS24 ∷ Sw01 ∷ CK42 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ Sw01 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ c4) ▸
       at 2 2 (CK42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑)) ▸
       at 3 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ c4) ▸
       at 4 2 (CK42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑)) ▸
       at 5 2 (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑)) ▸
       at 1 5 (CS24 ∷ CK42 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ []) (lem-F1-CS-K1-at1221 c4) ▸
       at 0 2 (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑)) ▸ done

  b1 : Chain (CS24 ∷ Sw01 ∷ CK42 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ Sw01 ∷ []) (CS24 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ [])
  b1 = at 1 2 (CK42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑)) ▸
       at 2 2 (Sb0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·42·3⟩ c4) ▸
       at 3 2 (CK42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑)) ▸
       at 4 2 (Sb0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·42·3⟩ c4) ▸
       at 5 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- tr CS-K1 at 1: 1 steps
lem-tr-CS-K1-at-1 : Complete 4 → ⟪ (Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-tr-CS-K1-at-1 c4 = run b0
  where
  b0 : Chain (Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ CS24 ∷ []) (CS24 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ [])
  b0 = at 0 5 (CS24 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ []) (lem-F1-CS-K1-at011220 c4) ▸ done


-- F1 CS-K1 @132132: 13 steps
lem-F1-CS-K1-at132132 : Complete 4 → ⟪ (Sb1-0-43-2 ∷ CK43 ∷ Sb1-0-43-2 ∷ CK43 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ CK43 ∷ Sb1-0-43-2 ∷ CK43 ∷ Sb1-0-43-2 ∷ []) ⟫ʷ
lem-F1-CS-K1-at132132 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb1-0-43-2 ∷ CK43 ∷ Sb1-0-43-2 ∷ CK43 ∷ CS34 ∷ []) (CS34 ∷ Sw23 ∷ CK42 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ Sw23 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb1-0-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·43·2⟩ c4) ▸
       at 2 2 (CK42 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CK43 ∷ []) (CK42 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Sb1-0-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·43·2⟩ c4) ▸
       at 4 2 (CK42 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CK43 ∷ []) (CK42 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CS24 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS34 ∷ []) (CS24 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 5 (CS24 ∷ CK42 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ []) (lem-F1-CS-K1-at1221 c4) ▸
       at 0 2 (CS34 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CS24 ∷ []) (CS34 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CS34 ∷ Sw23 ∷ CK42 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ Sw23 ∷ []) (CS34 ∷ CK43 ∷ Sb1-0-43-2 ∷ CK43 ∷ Sb1-0-43-2 ∷ [])
  b1 = at 1 2 (CK43 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CK42 ∷ []) (CK43 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb1-0-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·42·3⟩ c4) ▸
       at 3 2 (CK43 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CK42 ∷ []) (CK43 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Sb1-0-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·42·3⟩ c4) ▸
       at 5 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- F1 CS-K1 @01132032: 13 steps
lem-F1-CS-K1-at01132032 : Complete 4 → ⟪ (Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ CK43 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ CK43 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ
lem-F1-CS-K1-at01132032 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ CK43 ∷ CS34 ∷ []) (CS34 ∷ Sw01 ∷ CK43 ∷ Sb1-0-43-2 ∷ CK43 ∷ Sb1-0-43-2 ∷ Sw01 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb1-0-43-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·43·2⟩ c4) ▸
       at 2 2 (CK43 ∷ Sw01 ∷ []) (c₂ (Swap) (CK₁₀ ↑)) ▸
       at 3 2 (Sb1-0-43-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·43·2⟩ c4) ▸
       at 4 2 (CK43 ∷ Sw01 ∷ []) (c₂ (Swap) (CK₁₀ ↑)) ▸
       at 5 2 (CS34 ∷ Sw01 ∷ []) (c₂ (Swap) (CS ↑)) ▸
       at 1 5 (CS34 ∷ CK43 ∷ Sb1-0-43-2 ∷ CK43 ∷ Sb1-0-43-2 ∷ []) (lem-F1-CS-K1-at132132 c4) ▸
       at 0 2 (CS34 ∷ Sw01 ∷ []) (c₂ (Swap) (CS ↑)) ▸ done

  b1 : Chain (CS34 ∷ Sw01 ∷ CK43 ∷ Sb1-0-43-2 ∷ CK43 ∷ Sb1-0-43-2 ∷ Sw01 ∷ []) (CS34 ∷ CK43 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ [])
  b1 = at 1 2 (CK43 ∷ Sw01 ∷ []) (c₂ (Swap) (CK₁₀ ↑)) ▸
       at 2 2 (Sb0-1-43-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·43·2⟩ c4) ▸
       at 3 2 (CK43 ∷ Sw01 ∷ []) (c₂ (Swap) (CK₁₀ ↑)) ▸
       at 4 2 (Sb0-1-43-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·43·2⟩ c4) ▸
       at 5 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- F1 CS-K1 @02132031: 13 steps
lem-F1-CS-K1-at02132031 : Complete 4 → ⟪ (Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-F1-CS-K1-at02132031 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ CS34 ∷ []) (CS34 ∷ Sw12 ∷ CK43 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ Sw12 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·43·1⟩ c4) ▸
       at 2 2 (CK43 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CK₁₀)) ▸
       at 3 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·43·1⟩ c4) ▸
       at 4 2 (CK43 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CK₁₀)) ▸
       at 5 2 (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS)) ▸
       at 1 5 (CS34 ∷ CK43 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ []) (lem-F1-CS-K1-at01132032 c4) ▸
       at 0 2 (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS)) ▸ done

  b1 : Chain (CS34 ∷ Sw12 ∷ CK43 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ Sw12 ∷ []) (CS34 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ [])
  b1 = at 1 2 (CK43 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CK₁₀)) ▸
       at 2 2 (Sb0-2-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·43·2⟩ c4) ▸
       at 3 2 (CK43 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CK₁₀)) ▸
       at 4 2 (Sb0-2-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·43·2⟩ c4) ▸
       at 5 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- tr CS-K1 at 2: 1 steps
lem-tr-CS-K1-at-2 : Complete 4 → ⟪ (Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-tr-CS-K1-at-2 c4 = run b0
  where
  b0 : Chain (Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ CS34 ∷ []) (CS34 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ [])
  b0 = at 0 5 (CS34 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ []) (lem-F1-CS-K1-at02132031 c4) ▸ done


-- tr comm-CS-CS at 0: 1 steps
lem-tr-comm-CS-CS-at-0 : Complete 4 → ⟪ (Sb0-1-42-3 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-tr-comm-CS-CS-at-0 c4 = run b0
  where
  b0 : Chain (Sb0-1-42-3 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ Sb0-1-42-3 ∷ [])
  b0 = at 0 2 (Sb2-0-41-3 ∷ Sb0-1-42-3 ∷ []) (lem-F1-comm-CS-CS c4) ▸ done


-- F1 comm-CS-CS @2332: 7 steps
lem-F1-comm-CS-CS-at2332 : Complete 4 → ⟪ (Sb0-1-43-2 ∷ Sb3-0-41-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-41-2 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ
lem-F1-comm-CS-CS-at2332 c4 = run b0
  where
  b0 : Chain (Sb0-1-43-2 ∷ Sb3-0-41-2 ∷ []) (Sb3-0-41-2 ∷ Sb0-1-43-2 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·43·2⟩ c4) ▸
       at 2 2 (Sb2-0-41-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·0·41·2⟩ c4) ▸
       at 1 2 (Sb2-0-41-3 ∷ Sb0-1-42-3 ∷ []) (lem-F1-comm-CS-CS c4) ▸
       at 0 2 (Sb3-0-41-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨2·0·41·3⟩ c4) ▸
       at 1 2 (Sb0-1-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·42·3⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- F1 comm-CS-CS @122331: 7 steps
lem-F1-comm-CS-CS-at122331 : Complete 4 → ⟪ (Sb0-2-43-1 ∷ Sb3-0-42-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-42-1 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-F1-comm-CS-CS-at122331 c4 = run b0
  where
  b0 : Chain (Sb0-2-43-1 ∷ Sb3-0-42-1 ∷ []) (Sb3-0-42-1 ∷ Sb0-2-43-1 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·43·1⟩ c4) ▸
       at 2 2 (Sb3-0-41-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·42·1⟩ c4) ▸
       at 1 2 (Sb3-0-41-2 ∷ Sb0-1-43-2 ∷ []) (lem-F1-comm-CS-CS-at2332 c4) ▸
       at 0 2 (Sb3-0-42-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·41·2⟩ c4) ▸
       at 1 2 (Sb0-2-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·43·2⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- F1 comm-CS-CS @01122330: 7 steps
lem-F1-comm-CS-CS-at01122330 : Complete 4 → ⟪ (Sb1-2-43-0 ∷ Sb3-1-42-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-1-42-0 ∷ Sb1-2-43-0 ∷ []) ⟫ʷ
lem-F1-comm-CS-CS-at01122330 c4 = run b0
  where
  b0 : Chain (Sb1-2-43-0 ∷ Sb3-1-42-0 ∷ []) (Sb3-1-42-0 ∷ Sb1-2-43-0 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-2-43-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·2·43·0⟩ c4) ▸
       at 2 2 (Sb3-0-42-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·1·42·0⟩ c4) ▸
       at 1 2 (Sb3-0-42-1 ∷ Sb0-2-43-1 ∷ []) (lem-F1-comm-CS-CS-at122331 c4) ▸
       at 0 2 (Sb3-1-42-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·0·42·1⟩ c4) ▸
       at 1 2 (Sb1-2-43-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·2·43·1⟩ c4) ▸
       at 2 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- F0 @2332: 5 steps
lem-F0-at2332 : Complete 4 → ⟪ (Sb3-0-41-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ []) ⟫ʷ
lem-F0-at2332 c4 = run b0
  where
  b0 : Chain (Sb3-0-41-2 ∷ []) (Sb2-0-41-3 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb2-0-41-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·0·41·2⟩ c4) ▸
       at 1 1 (Sb3-0-41-2 ∷ []) (lem-F0 c4) ▸
       at 0 2 (Sb2-0-41-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·0·41·2⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- F0 @122331: 5 steps
lem-F0-at122331 : Complete 4 → ⟪ (Sb3-0-42-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-42-3 ∷ []) ⟫ʷ
lem-F0-at122331 c4 = run b0
  where
  b0 : Chain (Sb3-0-42-1 ∷ []) (Sb1-0-42-3 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb3-0-41-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·42·1⟩ c4) ▸
       at 1 1 (Sb2-0-41-3 ∷ []) (lem-F0-at2332 c4) ▸
       at 0 2 (Sb1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·41·3⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- F0 @01122330: 5 steps
lem-F0-at01122330 : Complete 4 → ⟪ (Sb3-1-42-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ []) ⟫ʷ
lem-F0-at01122330 c4 = run b0
  where
  b0 : Chain (Sb3-1-42-0 ∷ []) (Sb0-1-42-3 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb3-0-42-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·1·42·0⟩ c4) ▸
       at 1 1 (Sb1-0-42-3 ∷ []) (lem-F0-at122331 c4) ▸
       at 0 2 (Sb0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·42·3⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- F0 @02132130: 5 steps
lem-F0-at02132130 : Complete 4 → ⟪ (Sb1-2-43-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ []) ⟫ʷ
lem-F0-at02132130 c4 = run b0
  where
  b0 : Chain (Sb1-2-43-0 ∷ []) (Sb0-2-43-1 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-2-43-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·2·43·0⟩ c4) ▸
       at 1 1 (Sb1-2-43-0 ∷ []) (lem-F0-at02132031 c4) ▸
       at 0 2 (Sb0-2-43-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·2·43·0⟩ c4) ▸
       at 1 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- tr comm-CS-CS at 1: 5 steps
lem-tr-comm-CS-CS-at-1 : Complete 4 → ⟪ (Sb0-2-43-1 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-tr-comm-CS-CS-at-1 c4 = run b0
  where
  b0 : Chain (Sb0-2-43-1 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ Sb0-2-43-1 ∷ [])
  b0 = at 0 1 (Sb1-2-43-0 ∷ []) (lem-F0-at02132031 c4) ▸
       at 1 1 (Sb3-1-42-0 ∷ []) (lem-F0-at011220 c4) ▸
       at 0 2 (Sb3-1-42-0 ∷ Sb1-2-43-0 ∷ []) (lem-F1-comm-CS-CS-at01122330 c4) ▸
       at 0 1 (Sb0-1-42-3 ∷ []) (lem-F0-at01122330 c4) ▸
       at 1 1 (Sb0-2-43-1 ∷ []) (lem-F0-at02132130 c4) ▸ done


-- tr rel-266 at 0: 1 steps
lem-tr-rel-266-at-0 : Complete 4 → ⟪ (CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ S4 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ []) ⟫ʷ
lem-tr-rel-266-at-0 c4 = run b0
  where
  b0 : Chain (CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ S4 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ S4 ∷ []) (CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ [])
  b0 = at 0 21 (CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ []) (lem-F1-rel-266 c4) ▸ done


-- F1 rel-266 @2332: 45 steps
lem-F1-rel-266-at2332 : Complete 4 → ⟪ (CK40 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK40 ∷ S4 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ CK40 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK40 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK43 ∷ S4 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ S4 ∷ Sb3-0-41-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ S4 ∷ CK43 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK43 ∷ S4 ∷ []) ⟫ʷ
lem-F1-rel-266-at2332 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (run b5)))))
  where
  b0 : Chain (CK40 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK40 ∷ S4 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ CK40 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK40 ∷ S4 ∷ []) (Sw23 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ S4 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sw23 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ CK40 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK40 ∷ S4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CK40 ∷ Sw23 ∷ []) (lem-nat-2-CK40 c4) ▸
       at 2 2 (Sb2-0-41-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·0·41·2⟩ c4) ▸
       at 3 2 (Sb2-0-41-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·0·41·2⟩ c4) ▸
       at 4 2 (CK40 ∷ Sw23 ∷ []) (lem-nat-2-CK40 c4) ▸
       at 5 2 (S4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (S)) ▸
       at 6 2 (CK41 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CK41 ∷ []) (CK41 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Sb2-0-41-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·0·41·2⟩ c4) ▸ done

  b1 : Chain (Sw23 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ S4 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sw23 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ CK40 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK40 ∷ S4 ∷ []) (Sw23 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ S4 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sw23 ∷ S4 ∷ CK40 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK40 ∷ S4 ∷ [])
  b1 = at 8 2 (Sb2-0-41-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·0·41·2⟩ c4) ▸
       at 9 2 (CK41 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CK41 ∷ []) (CK41 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (S4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (S)) ▸
       at 11 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·43·2⟩ c4) ▸
       at 12 2 (CK41 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CK41 ∷ []) (CK41 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 13 2 (Sb2-0-41-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·0·41·2⟩ c4) ▸
       at 14 2 (Sb2-0-41-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·0·41·2⟩ c4) ▸
       at 15 2 (CK41 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CK41 ∷ []) (CK41 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Sw23 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ S4 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sw23 ∷ S4 ∷ CK40 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK40 ∷ S4 ∷ []) (CK43 ∷ Sw23 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sw23 ∷ [])
  b2 = at 16 2 (S4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (S)) ▸
       at 17 2 (CK40 ∷ Sw23 ∷ []) (lem-nat-2-CK40 c4) ▸
       at 18 2 (Sb2-0-41-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·0·41·2⟩ c4) ▸
       at 19 2 (Sb2-0-41-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·0·41·2⟩ c4) ▸
       at 20 2 (CK40 ∷ Sw23 ∷ []) (lem-nat-2-CK40 c4) ▸
       at 21 2 (S4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (S)) ▸
       at 1 21 (CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ []) (lem-F1-rel-266 c4) ▸
       at 0 2 (CK43 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CK42 ∷ []) (CK43 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸ done

  b3 : Chain (CK43 ∷ Sw23 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sw23 ∷ []) (CK43 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK43 ∷ S4 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sw23 ∷ S4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sw23 ∷ [])
  b3 = at 1 2 (Sb0-1-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·42·3⟩ c4) ▸
       at 2 2 (Sb0-1-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·42·3⟩ c4) ▸
       at 3 2 (CK43 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CK42 ∷ []) (CK43 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (S4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (S)) ▸
       at 5 2 (CK41 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CK41 ∷ []) (CK41 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Sb0-1-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·42·3⟩ c4) ▸
       at 7 2 (Sb0-1-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·42·3⟩ c4) ▸
       at 8 2 (CK41 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CK41 ∷ []) (CK41 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸ done

  b4 : Chain (CK43 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK43 ∷ S4 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sw23 ∷ S4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sw23 ∷ []) (CK43 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK43 ∷ S4 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ S4 ∷ Sb3-0-41-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ S4 ∷ CK43 ∷ Sw23 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sw23 ∷ [])
  b4 = at 9 2 (S4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (S)) ▸
       at 10 2 (Sb3-0-41-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨2·0·41·3⟩ c4) ▸
       at 11 2 (CK41 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CK41 ∷ []) (CK41 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (Sb0-1-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·42·3⟩ c4) ▸
       at 13 2 (Sb0-1-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·42·3⟩ c4) ▸
       at 14 2 (CK41 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CK41 ∷ []) (CK41 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 15 2 (S4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (S)) ▸
       at 16 2 (CK43 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CK42 ∷ []) (CK43 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸ done

  b5 : Chain (CK43 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK43 ∷ S4 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ S4 ∷ Sb3-0-41-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ S4 ∷ CK43 ∷ Sw23 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sw23 ∷ []) (CK43 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK43 ∷ S4 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ S4 ∷ Sb3-0-41-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ S4 ∷ CK43 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK43 ∷ S4 ∷ [])
  b5 = at 17 2 (Sb0-1-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·42·3⟩ c4) ▸
       at 18 2 (Sb0-1-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·42·3⟩ c4) ▸
       at 19 2 (CK43 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CK42 ∷ []) (CK43 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 20 2 (S4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (S)) ▸
       at 21 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- F1 rel-266 @122331: 45 steps
lem-F1-rel-266-at122331 : Complete 4 → ⟪ (CK40 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK40 ∷ S4 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ CK40 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK40 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ Sb3-0-42-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ []) ⟫ʷ
lem-F1-rel-266-at122331 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (run b5)))))
  where
  b0 : Chain (CK40 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK40 ∷ S4 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ CK40 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK40 ∷ S4 ∷ []) (Sw12 ∷ CK40 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK40 ∷ S4 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sw12 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ CK40 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK40 ∷ S4 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CK40 ∷ Sw12 ∷ []) (lem-nat-1-CK40 c4) ▸
       at 2 2 (Sb3-0-41-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·42·1⟩ c4) ▸
       at 3 2 (Sb3-0-41-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·42·1⟩ c4) ▸
       at 4 2 (CK40 ∷ Sw12 ∷ []) (lem-nat-1-CK40 c4) ▸
       at 5 2 (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑)) ▸
       at 6 2 (CK41 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CK42 ∷ []) (CK41 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Sb3-0-41-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·42·1⟩ c4) ▸ done

  b1 : Chain (Sw12 ∷ CK40 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK40 ∷ S4 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sw12 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ CK40 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK40 ∷ S4 ∷ []) (Sw12 ∷ CK40 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK40 ∷ S4 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ Sw12 ∷ S4 ∷ CK40 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK40 ∷ S4 ∷ [])
  b1 = at 8 2 (Sb3-0-41-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·42·1⟩ c4) ▸
       at 9 2 (CK41 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CK42 ∷ []) (CK41 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑)) ▸
       at 11 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·43·1⟩ c4) ▸
       at 12 2 (CK41 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CK42 ∷ []) (CK41 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 13 2 (Sb3-0-41-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·42·1⟩ c4) ▸
       at 14 2 (Sb3-0-41-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·42·1⟩ c4) ▸
       at 15 2 (CK41 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CK42 ∷ []) (CK41 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Sw12 ∷ CK40 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK40 ∷ S4 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ Sw12 ∷ S4 ∷ CK40 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK40 ∷ S4 ∷ []) (CK43 ∷ Sw12 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK43 ∷ S4 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ S4 ∷ Sb3-0-41-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ S4 ∷ CK43 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK43 ∷ S4 ∷ Sw12 ∷ [])
  b2 = at 16 2 (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑)) ▸
       at 17 2 (CK40 ∷ Sw12 ∷ []) (lem-nat-1-CK40 c4) ▸
       at 18 2 (Sb3-0-41-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·42·1⟩ c4) ▸
       at 19 2 (Sb3-0-41-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·42·1⟩ c4) ▸
       at 20 2 (CK40 ∷ Sw12 ∷ []) (lem-nat-1-CK40 c4) ▸
       at 21 2 (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑)) ▸
       at 1 21 (CK43 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK43 ∷ S4 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ S4 ∷ Sb3-0-41-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ S4 ∷ CK43 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK43 ∷ S4 ∷ []) (lem-F1-rel-266-at2332 c4) ▸
       at 0 2 (CK43 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CK₁₀)) ▸ done

  b3 : Chain (CK43 ∷ Sw12 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK43 ∷ S4 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ S4 ∷ Sb3-0-41-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ S4 ∷ CK43 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK43 ∷ S4 ∷ Sw12 ∷ []) (CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sw12 ∷ S4 ∷ Sb3-0-41-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ S4 ∷ CK43 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK43 ∷ S4 ∷ Sw12 ∷ [])
  b3 = at 1 2 (Sb0-2-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·43·2⟩ c4) ▸
       at 2 2 (Sb0-2-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·43·2⟩ c4) ▸
       at 3 2 (CK43 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CK₁₀)) ▸
       at 4 2 (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑)) ▸
       at 5 2 (CK42 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CK41 ∷ []) (CK42 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Sb0-2-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·43·2⟩ c4) ▸
       at 7 2 (Sb0-2-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·43·2⟩ c4) ▸
       at 8 2 (CK42 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CK41 ∷ []) (CK42 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸ done

  b4 : Chain (CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sw12 ∷ S4 ∷ Sb3-0-41-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ S4 ∷ CK43 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK43 ∷ S4 ∷ Sw12 ∷ []) (CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ Sb3-0-42-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sw12 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK43 ∷ S4 ∷ Sw12 ∷ [])
  b4 = at 9 2 (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑)) ▸
       at 10 2 (Sb3-0-42-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·41·2⟩ c4) ▸
       at 11 2 (CK42 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CK41 ∷ []) (CK42 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (Sb0-2-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·43·2⟩ c4) ▸
       at 13 2 (Sb0-2-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·43·2⟩ c4) ▸
       at 14 2 (CK42 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CK41 ∷ []) (CK42 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 15 2 (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑)) ▸
       at 16 2 (CK43 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CK₁₀)) ▸ done

  b5 : Chain (CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ Sb3-0-42-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sw12 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK43 ∷ S4 ∷ Sw12 ∷ []) (CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ Sb3-0-42-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ [])
  b5 = at 17 2 (Sb0-2-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·43·2⟩ c4) ▸
       at 18 2 (Sb0-2-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·43·2⟩ c4) ▸
       at 19 2 (CK43 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CK₁₀)) ▸
       at 20 2 (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑)) ▸
       at 21 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- F1 rel-266 @01122330: 45 steps
lem-F1-rel-266-at01122330 : Complete 4 → ⟪ (CK41 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ Sb1-2-43-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK41 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ S4 ∷ Sb3-1-42-0 ∷ CK42 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK43 ∷ S4 ∷ []) ⟫ʷ
lem-F1-rel-266-at01122330 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (run b5)))))
  where
  b0 : Chain (CK41 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ Sb1-2-43-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK41 ∷ S4 ∷ []) (Sw01 ∷ CK40 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK40 ∷ S4 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sw01 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ Sb1-2-43-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK41 ∷ S4 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CK40 ∷ Sw01 ∷ []) (lem-nat-0-CK41 c4) ▸
       at 2 2 (Sb3-0-42-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·1·42·0⟩ c4) ▸
       at 3 2 (Sb3-0-42-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·1·42·0⟩ c4) ▸
       at 4 2 (CK40 ∷ Sw01 ∷ []) (lem-nat-0-CK41 c4) ▸
       at 5 2 (S4 ∷ Sw01 ∷ []) (c₂ (Swap) (S ↑ ↑)) ▸
       at 6 2 (CK42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑)) ▸
       at 7 2 (Sb3-0-42-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·1·42·0⟩ c4) ▸ done

  b1 : Chain (Sw01 ∷ CK40 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK40 ∷ S4 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sw01 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ Sb1-2-43-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK41 ∷ S4 ∷ []) (Sw01 ∷ CK40 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK40 ∷ S4 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ Sw01 ∷ S4 ∷ CK41 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK41 ∷ S4 ∷ [])
  b1 = at 8 2 (Sb3-0-42-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·1·42·0⟩ c4) ▸
       at 9 2 (CK42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑)) ▸
       at 10 2 (S4 ∷ Sw01 ∷ []) (c₂ (Swap) (S ↑ ↑)) ▸
       at 11 2 (Sb0-2-43-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·2·43·0⟩ c4) ▸
       at 12 2 (CK42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑)) ▸
       at 13 2 (Sb3-0-42-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·1·42·0⟩ c4) ▸
       at 14 2 (Sb3-0-42-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·1·42·0⟩ c4) ▸
       at 15 2 (CK42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑)) ▸ done

  b2 : Chain (Sw01 ∷ CK40 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK40 ∷ S4 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ Sw01 ∷ S4 ∷ CK41 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK41 ∷ S4 ∷ []) (CK43 ∷ Sw01 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ Sb3-0-42-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sw01 ∷ [])
  b2 = at 16 2 (S4 ∷ Sw01 ∷ []) (c₂ (Swap) (S ↑ ↑)) ▸
       at 17 2 (CK40 ∷ Sw01 ∷ []) (lem-nat-0-CK41 c4) ▸
       at 18 2 (Sb3-0-42-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·1·42·0⟩ c4) ▸
       at 19 2 (Sb3-0-42-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·1·42·0⟩ c4) ▸
       at 20 2 (CK40 ∷ Sw01 ∷ []) (lem-nat-0-CK41 c4) ▸
       at 21 2 (S4 ∷ Sw01 ∷ []) (c₂ (Swap) (S ↑ ↑)) ▸
       at 1 21 (CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ Sb3-0-42-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ []) (lem-F1-rel-266-at122331 c4) ▸
       at 0 2 (CK43 ∷ Sw01 ∷ []) (c₂ (Swap) (CK₁₀ ↑)) ▸ done

  b3 : Chain (CK43 ∷ Sw01 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ Sb3-0-42-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sw01 ∷ []) (CK43 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ Sw01 ∷ S4 ∷ Sb3-0-42-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sw01 ∷ [])
  b3 = at 1 2 (Sb1-2-43-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·2·43·1⟩ c4) ▸
       at 2 2 (Sb1-2-43-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·2·43·1⟩ c4) ▸
       at 3 2 (CK43 ∷ Sw01 ∷ []) (c₂ (Swap) (CK₁₀ ↑)) ▸
       at 4 2 (S4 ∷ Sw01 ∷ []) (c₂ (Swap) (S ↑ ↑)) ▸
       at 5 2 (CK42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑)) ▸
       at 6 2 (Sb1-2-43-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·2·43·1⟩ c4) ▸
       at 7 2 (Sb1-2-43-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·2·43·1⟩ c4) ▸
       at 8 2 (CK42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑)) ▸ done

  b4 : Chain (CK43 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ Sw01 ∷ S4 ∷ Sb3-0-42-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sw01 ∷ []) (CK43 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ S4 ∷ Sb3-1-42-0 ∷ CK42 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sw01 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sw01 ∷ [])
  b4 = at 9 2 (S4 ∷ Sw01 ∷ []) (c₂ (Swap) (S ↑ ↑)) ▸
       at 10 2 (Sb3-1-42-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·0·42·1⟩ c4) ▸
       at 11 2 (CK42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑)) ▸
       at 12 2 (Sb1-2-43-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·2·43·1⟩ c4) ▸
       at 13 2 (Sb1-2-43-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·2·43·1⟩ c4) ▸
       at 14 2 (CK42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑)) ▸
       at 15 2 (S4 ∷ Sw01 ∷ []) (c₂ (Swap) (S ↑ ↑)) ▸
       at 16 2 (CK43 ∷ Sw01 ∷ []) (c₂ (Swap) (CK₁₀ ↑)) ▸ done

  b5 : Chain (CK43 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ S4 ∷ Sb3-1-42-0 ∷ CK42 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sw01 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sw01 ∷ []) (CK43 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ S4 ∷ Sb3-1-42-0 ∷ CK42 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK43 ∷ S4 ∷ [])
  b5 = at 17 2 (Sb1-2-43-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·2·43·1⟩ c4) ▸
       at 18 2 (Sb1-2-43-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·2·43·1⟩ c4) ▸
       at 19 2 (CK43 ∷ Sw01 ∷ []) (c₂ (Swap) (CK₁₀ ↑)) ▸
       at 20 2 (S4 ∷ Sw01 ∷ []) (c₂ (Swap) (S ↑ ↑)) ▸
       at 21 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- tr rel-266 at 1: 19 steps
lem-tr-rel-266-at-1 : Complete 4 → ⟪ (CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ []) ⟫ʷ
lem-tr-rel-266-at-1 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ []) (CK41 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ Sb1-2-43-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb3-1-42-0 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ [])
  b0 = at 1 1 (Sb3-1-42-0 ∷ []) (lem-F0-at011220 c4) ▸
       at 2 1 (Sb3-1-42-0 ∷ []) (lem-F0-at011220 c4) ▸
       at 6 1 (Sb3-1-42-0 ∷ []) (lem-F0-at011220 c4) ▸
       at 7 1 (Sb3-1-42-0 ∷ []) (lem-F0-at011220 c4) ▸
       at 10 1 (Sb1-2-43-0 ∷ []) (lem-F0-at02132031 c4) ▸
       at 12 1 (Sb3-1-42-0 ∷ []) (lem-F0-at011220 c4) ▸
       at 13 1 (Sb3-1-42-0 ∷ []) (lem-F0-at011220 c4) ▸
       at 17 1 (Sb3-1-42-0 ∷ []) (lem-F0-at011220 c4) ▸ done

  b1 : Chain (CK41 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ Sb1-2-43-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb3-1-42-0 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ []) (CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb1-2-43-0 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK43 ∷ S4 ∷ [])
  b1 = at 18 1 (Sb3-1-42-0 ∷ []) (lem-F0-at011220 c4) ▸
       at 0 21 (CK43 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ S4 ∷ Sb3-1-42-0 ∷ CK42 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK43 ∷ S4 ∷ []) (lem-F1-rel-266-at01122330 c4) ▸
       at 1 1 (Sb0-2-43-1 ∷ []) (lem-F0-at02132130 c4) ▸
       at 2 1 (Sb0-2-43-1 ∷ []) (lem-F0-at02132130 c4) ▸
       at 6 1 (Sb0-2-43-1 ∷ []) (lem-F0-at02132130 c4) ▸
       at 7 1 (Sb0-2-43-1 ∷ []) (lem-F0-at02132130 c4) ▸
       at 10 1 (Sb0-1-42-3 ∷ []) (lem-F0-at01122330 c4) ▸
       at 12 1 (Sb0-2-43-1 ∷ []) (lem-F0-at02132130 c4) ▸ done

  b2 : Chain (CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb1-2-43-0 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK43 ∷ S4 ∷ []) (CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ [])
  b2 = at 13 1 (Sb0-2-43-1 ∷ []) (lem-F0-at02132130 c4) ▸
       at 17 1 (Sb0-2-43-1 ∷ []) (lem-F0-at02132130 c4) ▸
       at 18 1 (Sb0-2-43-1 ∷ []) (lem-F0-at02132130 c4) ▸ done


-- tr rel-267 at 0: 1 steps
lem-tr-rel-267-at-0 : Complete 4 → ⟪ (CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ S4 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-tr-rel-267-at-0 c4 = run b0
  where
  b0 : Chain (CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ S4 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ S4 ∷ []) (CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ [])
  b0 = at 0 22 (CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ []) (lem-F1-rel-267 c4) ▸ done


-- F1 rel-267 @2332: 39 steps
lem-F1-rel-267-at2332 : Complete 4 → ⟪ (CK40 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK40 ∷ S4 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ CK40 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK40 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ
lem-F1-rel-267-at2332 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (run b4))))
  where
  b0 : Chain (CK40 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK40 ∷ S4 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ CK40 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK40 ∷ S4 ∷ []) (Sw23 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ S4 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sw23 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ CK40 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK40 ∷ S4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CK40 ∷ Sw23 ∷ []) (lem-nat-2-CK40 c4) ▸
       at 2 2 (Sb2-0-41-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·0·41·2⟩ c4) ▸
       at 3 2 (Sb2-0-41-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·0·41·2⟩ c4) ▸
       at 4 2 (CK40 ∷ Sw23 ∷ []) (lem-nat-2-CK40 c4) ▸
       at 5 2 (S4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (S)) ▸
       at 6 2 (CK41 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CK41 ∷ []) (CK41 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Sb2-0-41-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·0·41·2⟩ c4) ▸ done

  b1 : Chain (Sw23 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ S4 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sw23 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ CK40 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK40 ∷ S4 ∷ []) (Sw23 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ S4 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sw23 ∷ CK41 ∷ S4 ∷ CK40 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK40 ∷ S4 ∷ [])
  b1 = at 8 2 (Sb2-0-41-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·0·41·2⟩ c4) ▸
       at 9 2 (CK41 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CK41 ∷ []) (CK41 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (S4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (S)) ▸
       at 11 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·43·2⟩ c4) ▸
       at 12 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·43·2⟩ c4) ▸
       at 13 2 (CK41 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CK41 ∷ []) (CK41 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 14 2 (Sb2-0-41-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·0·41·2⟩ c4) ▸
       at 15 2 (Sb2-0-41-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·0·41·2⟩ c4) ▸ done

  b2 : Chain (Sw23 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ S4 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sw23 ∷ CK41 ∷ S4 ∷ CK40 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK40 ∷ S4 ∷ []) (Sw23 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sw23 ∷ [])
  b2 = at 16 2 (CK41 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CK41 ∷ []) (CK41 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 17 2 (S4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (S)) ▸
       at 18 2 (CK40 ∷ Sw23 ∷ []) (lem-nat-2-CK40 c4) ▸
       at 19 2 (Sb2-0-41-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·0·41·2⟩ c4) ▸
       at 20 2 (Sb2-0-41-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·0·41·2⟩ c4) ▸
       at 21 2 (CK40 ∷ Sw23 ∷ []) (lem-nat-2-CK40 c4) ▸
       at 22 2 (S4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (S)) ▸
       at 1 22 (CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ []) (lem-F1-rel-267 c4) ▸ done

  b3 : Chain (Sw23 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sw23 ∷ []) (CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sw23 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sw23 ∷ [])
  b3 = at 0 2 (CK41 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CK41 ∷ []) (CK41 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb3-0-41-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨2·0·41·3⟩ c4) ▸
       at 2 2 (Sb3-0-41-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨2·0·41·3⟩ c4) ▸
       at 3 2 (CK41 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CK41 ∷ []) (CK41 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (S4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (S)) ▸
       at 5 2 (Sb0-1-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·42·3⟩ c4) ▸
       at 6 2 (Sb0-1-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·42·3⟩ c4) ▸
       at 7 2 (CK41 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CK41 ∷ []) (CK41 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸ done

  b4 : Chain (CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sw23 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sw23 ∷ []) (CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ [])
  b4 = at 8 2 (Sb3-0-41-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨2·0·41·3⟩ c4) ▸
       at 9 2 (Sb3-0-41-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨2·0·41·3⟩ c4) ▸
       at 10 2 (CK41 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CK41 ∷ []) (CK41 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (S4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (S)) ▸
       at 12 2 (Sb0-1-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·42·3⟩ c4) ▸
       at 13 2 (Sb0-1-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·42·3⟩ c4) ▸
       at 14 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- F1 rel-267 @122331: 39 steps
lem-F1-rel-267-at122331 : Complete 4 → ⟪ (CK40 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK40 ∷ S4 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ CK40 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK40 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-F1-rel-267-at122331 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (run b4))))
  where
  b0 : Chain (CK40 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK40 ∷ S4 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ CK40 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK40 ∷ S4 ∷ []) (Sw12 ∷ CK40 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK40 ∷ S4 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sw12 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ CK40 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK40 ∷ S4 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CK40 ∷ Sw12 ∷ []) (lem-nat-1-CK40 c4) ▸
       at 2 2 (Sb3-0-41-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·42·1⟩ c4) ▸
       at 3 2 (Sb3-0-41-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·42·1⟩ c4) ▸
       at 4 2 (CK40 ∷ Sw12 ∷ []) (lem-nat-1-CK40 c4) ▸
       at 5 2 (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑)) ▸
       at 6 2 (CK41 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CK42 ∷ []) (CK41 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Sb3-0-41-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·42·1⟩ c4) ▸ done

  b1 : Chain (Sw12 ∷ CK40 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK40 ∷ S4 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sw12 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ CK40 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK40 ∷ S4 ∷ []) (Sw12 ∷ CK40 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK40 ∷ S4 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ Sw12 ∷ CK42 ∷ S4 ∷ CK40 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK40 ∷ S4 ∷ [])
  b1 = at 8 2 (Sb3-0-41-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·42·1⟩ c4) ▸
       at 9 2 (CK41 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CK42 ∷ []) (CK41 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑)) ▸
       at 11 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·43·1⟩ c4) ▸
       at 12 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·43·1⟩ c4) ▸
       at 13 2 (CK41 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CK42 ∷ []) (CK41 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 14 2 (Sb3-0-41-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·42·1⟩ c4) ▸
       at 15 2 (Sb3-0-41-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·42·1⟩ c4) ▸ done

  b2 : Chain (Sw12 ∷ CK40 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK40 ∷ S4 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ Sw12 ∷ CK42 ∷ S4 ∷ CK40 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK40 ∷ S4 ∷ []) (Sw12 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sw12 ∷ [])
  b2 = at 16 2 (CK41 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CK42 ∷ []) (CK41 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 17 2 (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑)) ▸
       at 18 2 (CK40 ∷ Sw12 ∷ []) (lem-nat-1-CK40 c4) ▸
       at 19 2 (Sb3-0-41-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·42·1⟩ c4) ▸
       at 20 2 (Sb3-0-41-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·42·1⟩ c4) ▸
       at 21 2 (CK40 ∷ Sw12 ∷ []) (lem-nat-1-CK40 c4) ▸
       at 22 2 (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑)) ▸
       at 1 22 (CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ []) (lem-F1-rel-267-at2332 c4) ▸ done

  b3 : Chain (Sw12 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sw12 ∷ []) (CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sw12 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sw12 ∷ [])
  b3 = at 0 2 (CK42 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CK41 ∷ []) (CK42 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb3-0-42-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·41·2⟩ c4) ▸
       at 2 2 (Sb3-0-42-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·41·2⟩ c4) ▸
       at 3 2 (CK42 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CK41 ∷ []) (CK42 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑)) ▸
       at 5 2 (Sb0-2-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·43·2⟩ c4) ▸
       at 6 2 (Sb0-2-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·43·2⟩ c4) ▸
       at 7 2 (CK42 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CK41 ∷ []) (CK42 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸ done

  b4 : Chain (CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sw12 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sw12 ∷ []) (CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ [])
  b4 = at 8 2 (Sb3-0-42-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·41·2⟩ c4) ▸
       at 9 2 (Sb3-0-42-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·41·2⟩ c4) ▸
       at 10 2 (CK42 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CK41 ∷ []) (CK42 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑)) ▸
       at 12 2 (Sb0-2-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·43·2⟩ c4) ▸
       at 13 2 (Sb0-2-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·43·2⟩ c4) ▸
       at 14 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done


-- F1 rel-267 @01122330: 39 steps
lem-F1-rel-267-at01122330 : Complete 4 → ⟪ (CK41 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK41 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ []) ⟫ʷ
lem-F1-rel-267-at01122330 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (run b4))))
  where
  b0 : Chain (CK41 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK41 ∷ S4 ∷ []) (Sw01 ∷ CK40 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK40 ∷ S4 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sw01 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK41 ∷ S4 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CK40 ∷ Sw01 ∷ []) (lem-nat-0-CK41 c4) ▸
       at 2 2 (Sb3-0-42-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·1·42·0⟩ c4) ▸
       at 3 2 (Sb3-0-42-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·1·42·0⟩ c4) ▸
       at 4 2 (CK40 ∷ Sw01 ∷ []) (lem-nat-0-CK41 c4) ▸
       at 5 2 (S4 ∷ Sw01 ∷ []) (c₂ (Swap) (S ↑ ↑)) ▸
       at 6 2 (CK42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑)) ▸
       at 7 2 (Sb3-0-42-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·1·42·0⟩ c4) ▸ done

  b1 : Chain (Sw01 ∷ CK40 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK40 ∷ S4 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sw01 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK41 ∷ S4 ∷ []) (Sw01 ∷ CK40 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK40 ∷ S4 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ Sw01 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK41 ∷ S4 ∷ [])
  b1 = at 8 2 (Sb3-0-42-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·1·42·0⟩ c4) ▸
       at 9 2 (CK42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑)) ▸
       at 10 2 (S4 ∷ Sw01 ∷ []) (c₂ (Swap) (S ↑ ↑)) ▸
       at 11 2 (Sb0-2-43-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·2·43·0⟩ c4) ▸
       at 12 2 (Sb0-2-43-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·2·43·0⟩ c4) ▸
       at 13 2 (CK42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑)) ▸
       at 14 2 (Sb3-0-42-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·1·42·0⟩ c4) ▸
       at 15 2 (Sb3-0-42-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·1·42·0⟩ c4) ▸ done

  b2 : Chain (Sw01 ∷ CK40 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK40 ∷ S4 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ Sw01 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK41 ∷ S4 ∷ []) (Sw01 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sw01 ∷ [])
  b2 = at 16 2 (CK42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑)) ▸
       at 17 2 (S4 ∷ Sw01 ∷ []) (c₂ (Swap) (S ↑ ↑)) ▸
       at 18 2 (CK40 ∷ Sw01 ∷ []) (lem-nat-0-CK41 c4) ▸
       at 19 2 (Sb3-0-42-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·1·42·0⟩ c4) ▸
       at 20 2 (Sb3-0-42-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·1·42·0⟩ c4) ▸
       at 21 2 (CK40 ∷ Sw01 ∷ []) (lem-nat-0-CK41 c4) ▸
       at 22 2 (S4 ∷ Sw01 ∷ []) (c₂ (Swap) (S ↑ ↑)) ▸
       at 1 22 (CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ []) (lem-F1-rel-267-at122331 c4) ▸ done

  b3 : Chain (Sw01 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sw01 ∷ []) (CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ Sw01 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sw01 ∷ [])
  b3 = at 0 2 (CK42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑)) ▸
       at 1 2 (Sb3-1-42-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·0·42·1⟩ c4) ▸
       at 2 2 (Sb3-1-42-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·0·42·1⟩ c4) ▸
       at 3 2 (CK42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑)) ▸
       at 4 2 (S4 ∷ Sw01 ∷ []) (c₂ (Swap) (S ↑ ↑)) ▸
       at 5 2 (Sb1-2-43-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·2·43·1⟩ c4) ▸
       at 6 2 (Sb1-2-43-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·2·43·1⟩ c4) ▸
       at 7 2 (CK42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑)) ▸ done

  b4 : Chain (CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ Sw01 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sw01 ∷ []) (CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ [])
  b4 = at 8 2 (Sb3-1-42-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·0·42·1⟩ c4) ▸
       at 9 2 (Sb3-1-42-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·0·42·1⟩ c4) ▸
       at 10 2 (CK42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑)) ▸
       at 11 2 (S4 ∷ Sw01 ∷ []) (c₂ (Swap) (S ↑ ↑)) ▸
       at 12 2 (Sb1-2-43-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·2·43·1⟩ c4) ▸
       at 13 2 (Sb1-2-43-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·2·43·1⟩ c4) ▸
       at 14 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- tr rel-267 at 1: 19 steps
lem-tr-rel-267-at-1 : Complete 4 → ⟪ (CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-tr-rel-267-at-1 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ []) (CK41 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ [])
  b0 = at 1 1 (Sb3-1-42-0 ∷ []) (lem-F0-at011220 c4) ▸
       at 2 1 (Sb3-1-42-0 ∷ []) (lem-F0-at011220 c4) ▸
       at 6 1 (Sb3-1-42-0 ∷ []) (lem-F0-at011220 c4) ▸
       at 7 1 (Sb3-1-42-0 ∷ []) (lem-F0-at011220 c4) ▸
       at 10 1 (Sb1-2-43-0 ∷ []) (lem-F0-at02132031 c4) ▸
       at 11 1 (Sb1-2-43-0 ∷ []) (lem-F0-at02132031 c4) ▸
       at 13 1 (Sb3-1-42-0 ∷ []) (lem-F0-at011220 c4) ▸
       at 14 1 (Sb3-1-42-0 ∷ []) (lem-F0-at011220 c4) ▸ done

  b1 : Chain (CK41 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ []) (CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ [])
  b1 = at 18 1 (Sb3-1-42-0 ∷ []) (lem-F0-at011220 c4) ▸
       at 19 1 (Sb3-1-42-0 ∷ []) (lem-F0-at011220 c4) ▸
       at 0 22 (CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ []) (lem-F1-rel-267-at01122330 c4) ▸
       at 1 1 (Sb0-1-42-3 ∷ []) (lem-F0-at01122330 c4) ▸
       at 2 1 (Sb0-1-42-3 ∷ []) (lem-F0-at01122330 c4) ▸
       at 5 1 (Sb0-2-43-1 ∷ []) (lem-F0-at02132130 c4) ▸
       at 6 1 (Sb0-2-43-1 ∷ []) (lem-F0-at02132130 c4) ▸
       at 8 1 (Sb0-1-42-3 ∷ []) (lem-F0-at01122330 c4) ▸ done

  b2 : Chain (CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ []) (CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ [])
  b2 = at 9 1 (Sb0-1-42-3 ∷ []) (lem-F0-at01122330 c4) ▸
       at 12 1 (Sb0-2-43-1 ∷ []) (lem-F0-at02132130 c4) ▸
       at 13 1 (Sb0-2-43-1 ∷ []) (lem-F0-at02132130 c4) ▸ done


-- tr rel-268 at 0: 1 steps
lem-tr-rel-268-at-0 : Complete 4 → ⟪ (Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ []) ⟫ʷ
lem-tr-rel-268-at-0 c4 = run b0
  where
  b0 : Chain (Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ []) (Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ [])
  b0 = at 0 14 (Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ []) (lem-F1-rel-268 c4) ▸ done


-- F1 rel-268 @2332: 31 steps
lem-F1-rel-268-at2332 : Complete 4 → ⟪ (Sb0-1-43-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-41-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ S4 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ S4 ∷ []) ⟫ʷ
lem-F1-rel-268-at2332 c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (Sb0-1-43-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ []) (Sw23 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sw23 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·43·2⟩ c4) ▸
       at 2 2 (CK41 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CK41 ∷ []) (CK41 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Sb2-0-41-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·0·41·2⟩ c4) ▸
       at 4 2 (Sb2-0-41-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·0·41·2⟩ c4) ▸
       at 5 2 (CK41 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CK41 ∷ []) (CK41 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (S4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (S)) ▸
       at 7 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·43·2⟩ c4) ▸ done

  b1 : Chain (Sw23 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sw23 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ []) (Sw23 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ Sw23 ∷ [])
  b1 = at 8 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·43·2⟩ c4) ▸
       at 9 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·43·2⟩ c4) ▸
       at 10 2 (CK41 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CK41 ∷ []) (CK41 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (Sb2-0-41-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·0·41·2⟩ c4) ▸
       at 12 2 (Sb2-0-41-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·0·41·2⟩ c4) ▸
       at 13 2 (CK41 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CK41 ∷ []) (CK41 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 14 2 (S4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (S)) ▸
       at 1 14 (Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ []) (lem-F1-rel-268 c4) ▸ done

  b2 : Chain (Sw23 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ Sw23 ∷ []) (Sb3-0-41-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ S4 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ Sw23 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ Sw23 ∷ [])
  b2 = at 0 2 (Sb3-0-41-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨2·0·41·3⟩ c4) ▸
       at 1 2 (CK41 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CK41 ∷ []) (CK41 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb0-1-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·42·3⟩ c4) ▸
       at 3 2 (Sb0-1-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·42·3⟩ c4) ▸
       at 4 2 (CK41 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CK41 ∷ []) (CK41 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (S4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (S)) ▸
       at 6 2 (Sb3-0-41-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨2·0·41·3⟩ c4) ▸
       at 7 2 (Sb3-0-41-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨2·0·41·3⟩ c4) ▸ done

  b3 : Chain (Sb3-0-41-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ S4 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ Sw23 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ Sw23 ∷ []) (Sb3-0-41-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ S4 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ S4 ∷ [])
  b3 = at 8 2 (Sb3-0-41-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨2·0·41·3⟩ c4) ▸
       at 9 2 (CK41 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CK41 ∷ []) (CK41 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (Sb0-1-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·42·3⟩ c4) ▸
       at 11 2 (Sb0-1-43-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·42·3⟩ c4) ▸
       at 12 2 (CK41 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ CK41 ∷ []) (CK41 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 13 2 (S4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (S)) ▸
       at 14 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸ done


-- F1 rel-268 @122331: 31 steps
lem-F1-rel-268-at122331 : Complete 4 → ⟪ (Sb0-2-43-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-42-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ []) ⟫ʷ
lem-F1-rel-268-at122331 c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (Sb0-2-43-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ []) (Sw12 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ Sw12 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·43·1⟩ c4) ▸
       at 2 2 (CK41 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CK42 ∷ []) (CK41 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Sb3-0-41-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·42·1⟩ c4) ▸
       at 4 2 (Sb3-0-41-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·42·1⟩ c4) ▸
       at 5 2 (CK41 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CK42 ∷ []) (CK41 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑)) ▸
       at 7 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·43·1⟩ c4) ▸ done

  b1 : Chain (Sw12 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ Sw12 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ []) (Sw12 ∷ Sb3-0-41-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ S4 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ S4 ∷ Sw12 ∷ [])
  b1 = at 8 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·43·1⟩ c4) ▸
       at 9 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·43·1⟩ c4) ▸
       at 10 2 (CK41 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CK42 ∷ []) (CK41 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (Sb3-0-41-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·42·1⟩ c4) ▸
       at 12 2 (Sb3-0-41-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·42·1⟩ c4) ▸
       at 13 2 (CK41 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CK42 ∷ []) (CK41 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 14 2 (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑)) ▸
       at 1 14 (Sb3-0-41-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ S4 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ S4 ∷ []) (lem-F1-rel-268-at2332 c4) ▸ done

  b2 : Chain (Sw12 ∷ Sb3-0-41-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ S4 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ S4 ∷ Sw12 ∷ []) (Sb3-0-42-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ Sw12 ∷ Sb3-0-41-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ S4 ∷ Sw12 ∷ [])
  b2 = at 0 2 (Sb3-0-42-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·41·2⟩ c4) ▸
       at 1 2 (CK42 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CK41 ∷ []) (CK42 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb0-2-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·43·2⟩ c4) ▸
       at 3 2 (Sb0-2-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·43·2⟩ c4) ▸
       at 4 2 (CK42 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CK41 ∷ []) (CK42 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑)) ▸
       at 6 2 (Sb3-0-42-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·41·2⟩ c4) ▸
       at 7 2 (Sb3-0-42-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·41·2⟩ c4) ▸ done

  b3 : Chain (Sb3-0-42-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ Sw12 ∷ Sb3-0-41-2 ∷ CK41 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ S4 ∷ Sw12 ∷ []) (Sb3-0-42-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ [])
  b3 = at 8 2 (Sb3-0-42-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·41·2⟩ c4) ▸
       at 9 2 (CK42 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CK41 ∷ []) (CK42 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (Sb0-2-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·43·2⟩ c4) ▸
       at 11 2 (Sb0-2-43-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·43·2⟩ c4) ▸
       at 12 2 (CK42 ∷ Sw12 ∷ []) (lw0 c4 (Sw12 ∷ CK41 ∷ []) (CK42 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 13 2 (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑)) ▸
       at 14 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done

