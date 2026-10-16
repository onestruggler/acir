{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D232 where

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
open import Examples.Groups.Clifford+CS.Five.D.D138 using (lem-F0-at011220)
open import Examples.Groups.Clifford+CS.Five.D.D144 using (lem-F1-cx-ccz)
open import Examples.Groups.Clifford+CS.Five.D.D151 using (lem-F1-toff-ccz ; lem-F2-K0∣CS12 ; lem-F2-K0∣CS23 ; lem-F2-S0∣CS12 ; lem-F2-S0∣CS23 ; lem-F2-S1∣CS23 ; lem-F2-S2∣CS01 ; lem-F2-S3∣CS01 ; lem-F2-S3∣CS12 ; lem-F2-iI∣CS01 ; lem-F2-iI∣CS12 ; lem-F2-iI∣CS23)
open import Examples.Groups.Clifford+CS.Five.D.D152 using (lem-F2-K1∣CS23 ; lem-F2-K2∣CS01 ; lem-F2-K3∣CS01 ; lem-F2-K3∣CS12)
open import Examples.Groups.Clifford+CS.Five.D.D154 using (lem-F4-iIᵖ0∣CS01ᵖ1 ; lem-F4-iIᵖ0∣CS12ᵖ1 ; lem-F4-iIᵖ0∣CS23ᵖ1)
open import Examples.Groups.Clifford+CS.Five.D.D191 using (lem-F0-at02132031)
open import Examples.Groups.Clifford+CS.Five.D.D225 using (lem-F2-CS01∣CS23)
open import Examples.Groups.Clifford+CS.Five.D.D231 using (lem-F0-at01122330 ; lem-F0-at02132130 ; lem-F1-rel-268-at122331)
open import Examples.Groups.Clifford+CS.Five.D.R021 using (lem-nat-0-SBOX⟨0·2·43·1⟩ ; lem-nat-0-SBOX⟨1·2·43·0⟩)
open import Examples.Groups.Clifford+CS.Five.D.R032 using (lem-nat-0-SBOX⟨3·0·42·1⟩)
open import Examples.Groups.Clifford+CS.Five.D.R043 using (lem-nat-0-SBOX⟨3·1·42·0⟩)
-- F1 rel-268 @01122330: 31 steps
lem-F1-rel-268-at01122330 : Complete 4 → ⟪ (Sb1-2-43-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-1-42-0 ∷ CK42 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ S4 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ S4 ∷ []) ⟫ʷ
lem-F1-rel-268-at01122330 c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (Sb1-2-43-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ []) (Sw01 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sw01 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ [])
  b0 = at 0 0 (Sw01 ∷ Sw01 ∷ []) (lw4 c4 [] (Sw01 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb0-2-43-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·2·43·0⟩ c4) ▸
       at 2 2 (CK42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑)) ▸
       at 3 2 (Sb3-0-42-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·1·42·0⟩ c4) ▸
       at 4 2 (Sb3-0-42-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·1·42·0⟩ c4) ▸
       at 5 2 (CK42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑)) ▸
       at 6 2 (S4 ∷ Sw01 ∷ []) (c₂ (Swap) (S ↑ ↑)) ▸
       at 7 2 (Sb0-2-43-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·2·43·0⟩ c4) ▸ done

  b1 : Chain (Sw01 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sw01 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ []) (Sw01 ∷ Sb3-0-42-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ Sw01 ∷ [])
  b1 = at 8 2 (Sb0-2-43-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·2·43·0⟩ c4) ▸
       at 9 2 (Sb0-2-43-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·2·43·0⟩ c4) ▸
       at 10 2 (CK42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑)) ▸
       at 11 2 (Sb3-0-42-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·1·42·0⟩ c4) ▸
       at 12 2 (Sb3-0-42-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·1·42·0⟩ c4) ▸
       at 13 2 (CK42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑)) ▸
       at 14 2 (S4 ∷ Sw01 ∷ []) (c₂ (Swap) (S ↑ ↑)) ▸
       at 1 14 (Sb3-0-42-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ []) (lem-F1-rel-268-at122331 c4) ▸ done

  b2 : Chain (Sw01 ∷ Sb3-0-42-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ Sb3-0-42-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ Sw01 ∷ []) (Sb3-1-42-0 ∷ CK42 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ S4 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ Sw01 ∷ Sb3-0-42-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ Sw01 ∷ [])
  b2 = at 0 2 (Sb3-1-42-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·0·42·1⟩ c4) ▸
       at 1 2 (CK42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑)) ▸
       at 2 2 (Sb1-2-43-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·2·43·1⟩ c4) ▸
       at 3 2 (Sb1-2-43-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·2·43·1⟩ c4) ▸
       at 4 2 (CK42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑)) ▸
       at 5 2 (S4 ∷ Sw01 ∷ []) (c₂ (Swap) (S ↑ ↑)) ▸
       at 6 2 (Sb3-1-42-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·0·42·1⟩ c4) ▸
       at 7 2 (Sb3-1-42-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·0·42·1⟩ c4) ▸ done

  b3 : Chain (Sb3-1-42-0 ∷ CK42 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ S4 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ Sw01 ∷ Sb3-0-42-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ Sw01 ∷ []) (Sb3-1-42-0 ∷ CK42 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ S4 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ S4 ∷ [])
  b3 = at 8 2 (Sb3-1-42-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·0·42·1⟩ c4) ▸
       at 9 2 (CK42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑)) ▸
       at 10 2 (Sb1-2-43-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·2·43·1⟩ c4) ▸
       at 11 2 (Sb1-2-43-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·2·43·1⟩ c4) ▸
       at 12 2 (CK42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑)) ▸
       at 13 2 (S4 ∷ Sw01 ∷ []) (c₂ (Swap) (S ↑ ↑)) ▸
       at 14 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸ done


-- tr rel-268 at 1: 17 steps
lem-tr-rel-268-at-1 : Complete 4 → ⟪ (Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ []) ⟫ʷ
lem-tr-rel-268-at-1 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ []) (Sb1-2-43-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ [])
  b0 = at 0 1 (Sb1-2-43-0 ∷ []) (lem-F0-at02132031 c4) ▸
       at 2 1 (Sb3-1-42-0 ∷ []) (lem-F0-at011220 c4) ▸
       at 3 1 (Sb3-1-42-0 ∷ []) (lem-F0-at011220 c4) ▸
       at 6 1 (Sb1-2-43-0 ∷ []) (lem-F0-at02132031 c4) ▸
       at 7 1 (Sb1-2-43-0 ∷ []) (lem-F0-at02132031 c4) ▸
       at 8 1 (Sb1-2-43-0 ∷ []) (lem-F0-at02132031 c4) ▸
       at 10 1 (Sb3-1-42-0 ∷ []) (lem-F0-at011220 c4) ▸
       at 11 1 (Sb3-1-42-0 ∷ []) (lem-F0-at011220 c4) ▸ done

  b1 : Chain (Sb1-2-43-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ []) (Sb0-1-42-3 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb1-2-43-0 ∷ CK42 ∷ S4 ∷ [])
  b1 = at 0 14 (Sb3-1-42-0 ∷ CK42 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ S4 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ Sb1-2-43-0 ∷ Sb1-2-43-0 ∷ CK42 ∷ S4 ∷ []) (lem-F1-rel-268-at01122330 c4) ▸
       at 0 1 (Sb0-1-42-3 ∷ []) (lem-F0-at01122330 c4) ▸
       at 2 1 (Sb0-2-43-1 ∷ []) (lem-F0-at02132130 c4) ▸
       at 3 1 (Sb0-2-43-1 ∷ []) (lem-F0-at02132130 c4) ▸
       at 6 1 (Sb0-1-42-3 ∷ []) (lem-F0-at01122330 c4) ▸
       at 7 1 (Sb0-1-42-3 ∷ []) (lem-F0-at01122330 c4) ▸
       at 8 1 (Sb0-1-42-3 ∷ []) (lem-F0-at01122330 c4) ▸
       at 10 1 (Sb0-2-43-1 ∷ []) (lem-F0-at02132130 c4) ▸ done

  b2 : Chain (Sb0-1-42-3 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb1-2-43-0 ∷ CK42 ∷ S4 ∷ []) (Sb0-1-42-3 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ [])
  b2 = at 11 1 (Sb0-2-43-1 ∷ []) (lem-F0-at02132130 c4) ▸ done


-- tr cx-ccz at 0: 1 steps
lem-tr-cx-ccz-at-0 : Complete 4 → ⟪ (CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ []) ⟫ʷ
lem-tr-cx-ccz-at-0 c4 = run b0
  where
  b0 : Chain (CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ []) (Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ [])
  b0 = at 0 55 (Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ []) (lem-F1-cx-ccz c4) ▸ done


-- tr toff-ccz at 0: 1 steps
lem-tr-toff-ccz-at-0 : Complete 4 → ⟪ (CK40 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK40 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK40 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK40 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ []) ⟫ʷ
lem-tr-toff-ccz-at-0 c4 = run b0
  where
  b0 : Chain (CK40 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK40 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK40 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK40 ∷ S4 ∷ []) (CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ [])
  b0 = at 0 171 (CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ []) (lem-F1-toff-ccz c4) ▸ done


-- tr comm1 S I at 0: 1 steps
lem-tr-comm1-S-I-at-0 : Complete 4 → ⟪ (S4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ S4 ∷ []) ⟫ʷ
lem-tr-comm1-S-I-at-0 c4 = run b0
  where
  b0 : Chain (S4 ∷ CS04 ∷ []) (CS04 ∷ S4 ∷ [])
  b0 = at 0 2 (CS04 ∷ S4 ∷ []) (pw1 c4 (S4 ∷ CS04 ∷ []) (CS04 ∷ S4 ∷ []) tt tt Eq.refl) ▸ done


-- tr comm1 S S0 at 0: 1 steps
lem-tr-comm1-S-S0-at-0 : Complete 4 → ⟪ (CS14 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ CS14 ∷ []) ⟫ʷ
lem-tr-comm1-S-S0-at-0 c4 = run b0
  where
  b0 : Chain (CS14 ∷ CS04 ∷ []) (CS04 ∷ CS14 ∷ [])
  b0 = at 0 2 (CS04 ∷ CS14 ∷ []) (pw2 c4 (CS14 ∷ CS04 ∷ []) (CS04 ∷ CS14 ∷ []) tt tt Eq.refl) ▸ done


-- tr comm1 S K0 at 0: 1 steps
lem-tr-comm1-S-K0-at-0 : Complete 4 → ⟪ (CK41 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ CK41 ∷ []) ⟫ʷ
lem-tr-comm1-S-K0-at-0 c4 = run b0
  where
  b0 : Chain (CK41 ∷ CS04 ∷ []) (CS04 ∷ CK41 ∷ [])
  b0 = at 0 2 (CS04 ∷ CK41 ∷ []) (pw2 c4 (CK41 ∷ CS04 ∷ []) (CS04 ∷ CK41 ∷ []) tt tt Eq.refl) ▸ done


-- tr comm1 S S1 at 0: 1 steps
lem-tr-comm1-S-S1-at-0 : Complete 4 → ⟪ (CS24 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ CS24 ∷ []) ⟫ʷ
lem-tr-comm1-S-S1-at-0 c4 = run b0
  where
  b0 : Chain (CS24 ∷ CS04 ∷ []) (CS04 ∷ CS24 ∷ [])
  b0 = at 0 2 (CS04 ∷ CS24 ∷ []) (pw1 c4 (CS24 ∷ CS04 ∷ []) (CS04 ∷ CS24 ∷ []) tt tt Eq.refl) ▸ done


-- tr comm1 S K1 at 0: 1 steps
lem-tr-comm1-S-K1-at-0 : Complete 4 → ⟪ (CK42 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ CK42 ∷ []) ⟫ʷ
lem-tr-comm1-S-K1-at-0 c4 = run b0
  where
  b0 : Chain (CK42 ∷ CS04 ∷ []) (CS04 ∷ CK42 ∷ [])
  b0 = at 0 2 (CS04 ∷ CK42 ∷ []) (pw1 c4 (CK42 ∷ CS04 ∷ []) (CS04 ∷ CK42 ∷ []) tt tt Eq.refl) ▸ done


-- tr comm1 S S2 at 0: 1 steps
lem-tr-comm1-S-S2-at-0 : Complete 4 → ⟪ (CS34 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ CS34 ∷ []) ⟫ʷ
lem-tr-comm1-S-S2-at-0 c4 = run b0
  where
  b0 : Chain (CS34 ∷ CS04 ∷ []) (CS04 ∷ CS34 ∷ [])
  b0 = at 0 2 (CS04 ∷ CS34 ∷ []) (pw1 c4 (CS34 ∷ CS04 ∷ []) (CS04 ∷ CS34 ∷ []) tt tt Eq.refl) ▸ done


-- tr comm1 S K2 at 0: 1 steps
lem-tr-comm1-S-K2-at-0 : Complete 4 → ⟪ (CK43 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ CK43 ∷ []) ⟫ʷ
lem-tr-comm1-S-K2-at-0 c4 = run b0
  where
  b0 : Chain (CK43 ∷ CS04 ∷ []) (CS04 ∷ CK43 ∷ [])
  b0 = at 0 2 (CS04 ∷ CK43 ∷ []) (pw1 c4 (CK43 ∷ CS04 ∷ []) (CS04 ∷ CK43 ∷ []) tt tt Eq.refl) ▸ done


-- tr comm1 S CS01 at 0: 1 steps
lem-tr-comm1-S-CS01-at-0 : Complete 4 → ⟪ (Sb0-1-42-3 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-tr-comm1-S-CS01-at-0 c4 = run b0
  where
  b0 : Chain (Sb0-1-42-3 ∷ CS04 ∷ []) (CS04 ∷ Sb0-1-42-3 ∷ [])
  b0 = at 0 2 (CS04 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F2-S0∣CS12 c4)) ▸ done


-- tr comm1 S CS12 at 0: 1 steps
lem-tr-comm1-S-CS12-at-0 : Complete 4 → ⟪ (Sb0-2-43-1 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-tr-comm1-S-CS12-at-0 c4 = run b0
  where
  b0 : Chain (Sb0-2-43-1 ∷ CS04 ∷ []) (CS04 ∷ Sb0-2-43-1 ∷ [])
  b0 = at 0 2 (CS04 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F2-S0∣CS23 c4)) ▸ done


-- tr comm1 K I at 0: 1 steps
lem-tr-comm1-K-I-at-0 : Complete 4 → ⟪ (S4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ S4 ∷ []) ⟫ʷ
lem-tr-comm1-K-I-at-0 c4 = run b0
  where
  b0 : Chain (S4 ∷ CK40 ∷ []) (CK40 ∷ S4 ∷ [])
  b0 = at 0 2 (CK40 ∷ S4 ∷ []) (pw1 c4 (S4 ∷ CK40 ∷ []) (CK40 ∷ S4 ∷ []) tt tt Eq.refl) ▸ done


-- tr comm1 K S0 at 0: 1 steps
lem-tr-comm1-K-S0-at-0 : Complete 4 → ⟪ (CS14 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ CS14 ∷ []) ⟫ʷ
lem-tr-comm1-K-S0-at-0 c4 = run b0
  where
  b0 : Chain (CS14 ∷ CK40 ∷ []) (CK40 ∷ CS14 ∷ [])
  b0 = at 0 2 (CK40 ∷ CS14 ∷ []) (pw2 c4 (CS14 ∷ CK40 ∷ []) (CK40 ∷ CS14 ∷ []) tt tt Eq.refl) ▸ done


-- tr comm1 K K0 at 0: 1 steps
lem-tr-comm1-K-K0-at-0 : Complete 4 → ⟪ (CK41 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ CK41 ∷ []) ⟫ʷ
lem-tr-comm1-K-K0-at-0 c4 = run b0
  where
  b0 : Chain (CK41 ∷ CK40 ∷ []) (CK40 ∷ CK41 ∷ [])
  b0 = at 0 2 (CK40 ∷ CK41 ∷ []) (pw2 c4 (CK41 ∷ CK40 ∷ []) (CK40 ∷ CK41 ∷ []) tt tt Eq.refl) ▸ done


-- tr comm1 K S1 at 0: 1 steps
lem-tr-comm1-K-S1-at-0 : Complete 4 → ⟪ (CS24 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ CS24 ∷ []) ⟫ʷ
lem-tr-comm1-K-S1-at-0 c4 = run b0
  where
  b0 : Chain (CS24 ∷ CK40 ∷ []) (CK40 ∷ CS24 ∷ [])
  b0 = at 0 2 (CK40 ∷ CS24 ∷ []) (pw1 c4 (CS24 ∷ CK40 ∷ []) (CK40 ∷ CS24 ∷ []) tt tt Eq.refl) ▸ done


-- tr comm1 K K1 at 0: 1 steps
lem-tr-comm1-K-K1-at-0 : Complete 4 → ⟪ (CK42 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ CK42 ∷ []) ⟫ʷ
lem-tr-comm1-K-K1-at-0 c4 = run b0
  where
  b0 : Chain (CK42 ∷ CK40 ∷ []) (CK40 ∷ CK42 ∷ [])
  b0 = at 0 2 (CK40 ∷ CK42 ∷ []) (pw1 c4 (CK42 ∷ CK40 ∷ []) (CK40 ∷ CK42 ∷ []) tt tt Eq.refl) ▸ done


-- tr comm1 K S2 at 0: 1 steps
lem-tr-comm1-K-S2-at-0 : Complete 4 → ⟪ (CS34 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ CS34 ∷ []) ⟫ʷ
lem-tr-comm1-K-S2-at-0 c4 = run b0
  where
  b0 : Chain (CS34 ∷ CK40 ∷ []) (CK40 ∷ CS34 ∷ [])
  b0 = at 0 2 (CK40 ∷ CS34 ∷ []) (pw1 c4 (CS34 ∷ CK40 ∷ []) (CK40 ∷ CS34 ∷ []) tt tt Eq.refl) ▸ done


-- tr comm1 K K2 at 0: 1 steps
lem-tr-comm1-K-K2-at-0 : Complete 4 → ⟪ (CK43 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ CK43 ∷ []) ⟫ʷ
lem-tr-comm1-K-K2-at-0 c4 = run b0
  where
  b0 : Chain (CK43 ∷ CK40 ∷ []) (CK40 ∷ CK43 ∷ [])
  b0 = at 0 2 (CK40 ∷ CK43 ∷ []) (pw1 c4 (CK43 ∷ CK40 ∷ []) (CK40 ∷ CK43 ∷ []) tt tt Eq.refl) ▸ done


-- tr comm1 K CS01 at 0: 1 steps
lem-tr-comm1-K-CS01-at-0 : Complete 4 → ⟪ (Sb0-1-42-3 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-tr-comm1-K-CS01-at-0 c4 = run b0
  where
  b0 : Chain (Sb0-1-42-3 ∷ CK40 ∷ []) (CK40 ∷ Sb0-1-42-3 ∷ [])
  b0 = at 0 2 (CK40 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F2-K0∣CS12 c4)) ▸ done


-- tr comm1 K CS12 at 0: 1 steps
lem-tr-comm1-K-CS12-at-0 : Complete 4 → ⟪ (Sb0-2-43-1 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-tr-comm1-K-CS12-at-0 c4 = run b0
  where
  b0 : Chain (Sb0-2-43-1 ∷ CK40 ∷ []) (CK40 ∷ Sb0-2-43-1 ∷ [])
  b0 = at 0 2 (CK40 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F2-K0∣CS23 c4)) ▸ done


-- tr comm1 S I at 1: 1 steps
lem-tr-comm1-S-I-at-1 : Complete 4 → ⟪ (S4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ S4 ∷ []) ⟫ʷ
lem-tr-comm1-S-I-at-1 c4 = run b0
  where
  b0 : Chain (S4 ∷ CS14 ∷ []) (CS14 ∷ S4 ∷ [])
  b0 = at 0 2 (CS14 ∷ S4 ∷ []) (lw0 c4 (S4 ∷ CS14 ∷ []) (CS14 ∷ S4 ∷ []) tt tt Eq.refl) ▸ done


-- tr comm1 S S0 at 1: 1 steps
lem-tr-comm1-S-S0-at-1 : Complete 4 → ⟪ (CS24 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ CS24 ∷ []) ⟫ʷ
lem-tr-comm1-S-S0-at-1 c4 = run b0
  where
  b0 : Chain (CS24 ∷ CS14 ∷ []) (CS14 ∷ CS24 ∷ [])
  b0 = at 0 2 (CS14 ∷ CS24 ∷ []) (lw0 c4 (CS24 ∷ CS14 ∷ []) (CS14 ∷ CS24 ∷ []) tt tt Eq.refl) ▸ done


-- tr comm1 S K0 at 1: 1 steps
lem-tr-comm1-S-K0-at-1 : Complete 4 → ⟪ (CK42 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ CK42 ∷ []) ⟫ʷ
lem-tr-comm1-S-K0-at-1 c4 = run b0
  where
  b0 : Chain (CK42 ∷ CS14 ∷ []) (CS14 ∷ CK42 ∷ [])
  b0 = at 0 2 (CS14 ∷ CK42 ∷ []) (lw0 c4 (CK42 ∷ CS14 ∷ []) (CS14 ∷ CK42 ∷ []) tt tt Eq.refl) ▸ done


-- tr comm1 S S1 at 1: 1 steps
lem-tr-comm1-S-S1-at-1 : Complete 4 → ⟪ (CS34 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ CS34 ∷ []) ⟫ʷ
lem-tr-comm1-S-S1-at-1 c4 = run b0
  where
  b0 : Chain (CS34 ∷ CS14 ∷ []) (CS14 ∷ CS34 ∷ [])
  b0 = at 0 2 (CS14 ∷ CS34 ∷ []) (lw0 c4 (CS34 ∷ CS14 ∷ []) (CS14 ∷ CS34 ∷ []) tt tt Eq.refl) ▸ done


-- tr comm1 S K1 at 1: 1 steps
lem-tr-comm1-S-K1-at-1 : Complete 4 → ⟪ (CK43 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ CK43 ∷ []) ⟫ʷ
lem-tr-comm1-S-K1-at-1 c4 = run b0
  where
  b0 : Chain (CK43 ∷ CS14 ∷ []) (CS14 ∷ CK43 ∷ [])
  b0 = at 0 2 (CS14 ∷ CK43 ∷ []) (lw0 c4 (CK43 ∷ CS14 ∷ []) (CS14 ∷ CK43 ∷ []) tt tt Eq.refl) ▸ done


-- tr comm1 S CS01 at 1: 1 steps
lem-tr-comm1-S-CS01-at-1 : Complete 4 → ⟪ (Sb0-2-43-1 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-tr-comm1-S-CS01-at-1 c4 = run b0
  where
  b0 : Chain (Sb0-2-43-1 ∷ CS14 ∷ []) (CS14 ∷ Sb0-2-43-1 ∷ [])
  b0 = at 0 2 (CS14 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F2-S1∣CS23 c4)) ▸ done


-- tr comm1 K I at 1: 1 steps
lem-tr-comm1-K-I-at-1 : Complete 4 → ⟪ (S4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ S4 ∷ []) ⟫ʷ
lem-tr-comm1-K-I-at-1 c4 = run b0
  where
  b0 : Chain (S4 ∷ CK41 ∷ []) (CK41 ∷ S4 ∷ [])
  b0 = at 0 2 (CK41 ∷ S4 ∷ []) (lw0 c4 (S4 ∷ CK41 ∷ []) (CK41 ∷ S4 ∷ []) tt tt Eq.refl) ▸ done


-- tr comm1 K S0 at 1: 1 steps
lem-tr-comm1-K-S0-at-1 : Complete 4 → ⟪ (CS24 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ CS24 ∷ []) ⟫ʷ
lem-tr-comm1-K-S0-at-1 c4 = run b0
  where
  b0 : Chain (CS24 ∷ CK41 ∷ []) (CK41 ∷ CS24 ∷ [])
  b0 = at 0 2 (CK41 ∷ CS24 ∷ []) (lw0 c4 (CS24 ∷ CK41 ∷ []) (CK41 ∷ CS24 ∷ []) tt tt Eq.refl) ▸ done


-- tr comm1 K K0 at 1: 1 steps
lem-tr-comm1-K-K0-at-1 : Complete 4 → ⟪ (CK42 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ CK42 ∷ []) ⟫ʷ
lem-tr-comm1-K-K0-at-1 c4 = run b0
  where
  b0 : Chain (CK42 ∷ CK41 ∷ []) (CK41 ∷ CK42 ∷ [])
  b0 = at 0 2 (CK41 ∷ CK42 ∷ []) (lw0 c4 (CK42 ∷ CK41 ∷ []) (CK41 ∷ CK42 ∷ []) tt tt Eq.refl) ▸ done


-- tr comm1 K S1 at 1: 1 steps
lem-tr-comm1-K-S1-at-1 : Complete 4 → ⟪ (CS34 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ CS34 ∷ []) ⟫ʷ
lem-tr-comm1-K-S1-at-1 c4 = run b0
  where
  b0 : Chain (CS34 ∷ CK41 ∷ []) (CK41 ∷ CS34 ∷ [])
  b0 = at 0 2 (CK41 ∷ CS34 ∷ []) (lw0 c4 (CS34 ∷ CK41 ∷ []) (CK41 ∷ CS34 ∷ []) tt tt Eq.refl) ▸ done


-- tr comm1 K K1 at 1: 1 steps
lem-tr-comm1-K-K1-at-1 : Complete 4 → ⟪ (CK43 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ CK43 ∷ []) ⟫ʷ
lem-tr-comm1-K-K1-at-1 c4 = run b0
  where
  b0 : Chain (CK43 ∷ CK41 ∷ []) (CK41 ∷ CK43 ∷ [])
  b0 = at 0 2 (CK41 ∷ CK43 ∷ []) (lw0 c4 (CK43 ∷ CK41 ∷ []) (CK41 ∷ CK43 ∷ []) tt tt Eq.refl) ▸ done


-- tr comm1 K CS01 at 1: 1 steps
lem-tr-comm1-K-CS01-at-1 : Complete 4 → ⟪ (Sb0-2-43-1 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-tr-comm1-K-CS01-at-1 c4 = run b0
  where
  b0 : Chain (Sb0-2-43-1 ∷ CK41 ∷ []) (CK41 ∷ Sb0-2-43-1 ∷ [])
  b0 = at 0 2 (CK41 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F2-K1∣CS23 c4)) ▸ done


-- tr comm1 S I at 2: 1 steps
lem-tr-comm1-S-I-at-2 : Complete 4 → ⟪ (S4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ S4 ∷ []) ⟫ʷ
lem-tr-comm1-S-I-at-2 c4 = run b0
  where
  b0 : Chain (S4 ∷ CS24 ∷ []) (CS24 ∷ S4 ∷ [])
  b0 = at 0 2 (CS24 ∷ S4 ∷ []) (lw0 c4 (S4 ∷ CS24 ∷ []) (CS24 ∷ S4 ∷ []) tt tt Eq.refl) ▸ done


-- tr comm1 S S0 at 2: 1 steps
lem-tr-comm1-S-S0-at-2 : Complete 4 → ⟪ (CS34 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CS34 ∷ []) ⟫ʷ
lem-tr-comm1-S-S0-at-2 c4 = run b0
  where
  b0 : Chain (CS34 ∷ CS24 ∷ []) (CS24 ∷ CS34 ∷ [])
  b0 = at 0 2 (CS24 ∷ CS34 ∷ []) (lw0 c4 (CS34 ∷ CS24 ∷ []) (CS24 ∷ CS34 ∷ []) tt tt Eq.refl) ▸ done


-- tr comm1 S K0 at 2: 1 steps
lem-tr-comm1-S-K0-at-2 : Complete 4 → ⟪ (CK43 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CK43 ∷ []) ⟫ʷ
lem-tr-comm1-S-K0-at-2 c4 = run b0
  where
  b0 : Chain (CK43 ∷ CS24 ∷ []) (CS24 ∷ CK43 ∷ [])
  b0 = at 0 2 (CS24 ∷ CK43 ∷ []) (lw0 c4 (CK43 ∷ CS24 ∷ []) (CS24 ∷ CK43 ∷ []) tt tt Eq.refl) ▸ done


-- tr comm1 K I at 2: 1 steps
lem-tr-comm1-K-I-at-2 : Complete 4 → ⟪ (S4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ S4 ∷ []) ⟫ʷ
lem-tr-comm1-K-I-at-2 c4 = run b0
  where
  b0 : Chain (S4 ∷ CK42 ∷ []) (CK42 ∷ S4 ∷ [])
  b0 = at 0 2 (CK42 ∷ S4 ∷ []) (lw0 c4 (S4 ∷ CK42 ∷ []) (CK42 ∷ S4 ∷ []) tt tt Eq.refl) ▸ done


-- tr comm1 K S0 at 2: 1 steps
lem-tr-comm1-K-S0-at-2 : Complete 4 → ⟪ (CS34 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ CS34 ∷ []) ⟫ʷ
lem-tr-comm1-K-S0-at-2 c4 = run b0
  where
  b0 : Chain (CS34 ∷ CK42 ∷ []) (CK42 ∷ CS34 ∷ [])
  b0 = at 0 2 (CK42 ∷ CS34 ∷ []) (lw0 c4 (CS34 ∷ CK42 ∷ []) (CK42 ∷ CS34 ∷ []) tt tt Eq.refl) ▸ done


-- tr comm1 K K0 at 2: 1 steps
lem-tr-comm1-K-K0-at-2 : Complete 4 → ⟪ (CK43 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ CK43 ∷ []) ⟫ʷ
lem-tr-comm1-K-K0-at-2 c4 = run b0
  where
  b0 : Chain (CK43 ∷ CK42 ∷ []) (CK42 ∷ CK43 ∷ [])
  b0 = at 0 2 (CK42 ∷ CK43 ∷ []) (lw0 c4 (CK43 ∷ CK42 ∷ []) (CK42 ∷ CK43 ∷ []) tt tt Eq.refl) ▸ done


-- tr comm1 S I at 3: 1 steps
lem-tr-comm1-S-I-at-3 : Complete 4 → ⟪ (S4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ S4 ∷ []) ⟫ʷ
lem-tr-comm1-S-I-at-3 c4 = run b0
  where
  b0 : Chain (S4 ∷ CS34 ∷ []) (CS34 ∷ S4 ∷ [])
  b0 = at 0 2 (CS34 ∷ S4 ∷ []) (lw0 c4 (S4 ∷ CS34 ∷ []) (CS34 ∷ S4 ∷ []) tt tt Eq.refl) ▸ done


-- tr comm1 K I at 3: 1 steps
lem-tr-comm1-K-I-at-3 : Complete 4 → ⟪ (S4 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ S4 ∷ []) ⟫ʷ
lem-tr-comm1-K-I-at-3 c4 = run b0
  where
  b0 : Chain (S4 ∷ CK43 ∷ []) (CK43 ∷ S4 ∷ [])
  b0 = at 0 2 (CK43 ∷ S4 ∷ []) (lw0 c4 (S4 ∷ CK43 ∷ []) (CK43 ∷ S4 ∷ []) tt tt Eq.refl) ▸ done


-- tr comm2 I at 0: 1 steps
lem-tr-comm2-I-at-0 : Complete 4 → ⟪ (S4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ S4 ∷ []) ⟫ʷ
lem-tr-comm2-I-at-0 c4 = run b0
  where
  b0 : Chain (S4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S4 ∷ [])
  b0 = at 0 2 (Sb2-0-41-3 ∷ S4 ∷ []) (lem-F2-iI∣CS01 c4) ▸ done


-- tr comm2 S0 at 0: 1 steps
lem-tr-comm2-S0-at-0 : Complete 4 → ⟪ (CS24 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ CS24 ∷ []) ⟫ʷ
lem-tr-comm2-S0-at-0 c4 = run b0
  where
  b0 : Chain (CS24 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ CS24 ∷ [])
  b0 = at 0 2 (Sb2-0-41-3 ∷ CS24 ∷ []) (lem-F2-S2∣CS01 c4) ▸ done


-- tr comm2 K0 at 0: 1 steps
lem-tr-comm2-K0-at-0 : Complete 4 → ⟪ (CK42 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ CK42 ∷ []) ⟫ʷ
lem-tr-comm2-K0-at-0 c4 = run b0
  where
  b0 : Chain (CK42 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ CK42 ∷ [])
  b0 = at 0 2 (Sb2-0-41-3 ∷ CK42 ∷ []) (lem-F2-K2∣CS01 c4) ▸ done


-- tr comm2 S1 at 0: 1 steps
lem-tr-comm2-S1-at-0 : Complete 4 → ⟪ (CS34 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ CS34 ∷ []) ⟫ʷ
lem-tr-comm2-S1-at-0 c4 = run b0
  where
  b0 : Chain (CS34 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ CS34 ∷ [])
  b0 = at 0 2 (Sb2-0-41-3 ∷ CS34 ∷ []) (lem-F2-S3∣CS01 c4) ▸ done


-- tr comm2 K1 at 0: 1 steps
lem-tr-comm2-K1-at-0 : Complete 4 → ⟪ (CK43 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ CK43 ∷ []) ⟫ʷ
lem-tr-comm2-K1-at-0 c4 = run b0
  where
  b0 : Chain (CK43 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ CK43 ∷ [])
  b0 = at 0 2 (Sb2-0-41-3 ∷ CK43 ∷ []) (lem-F2-K3∣CS01 c4) ▸ done


-- tr comm2 CS01 at 0: 1 steps
lem-tr-comm2-CS01-at-0 : Complete 4 → ⟪ (Sb0-2-43-1 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-tr-comm2-CS01-at-0 c4 = run b0
  where
  b0 : Chain (Sb0-2-43-1 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ Sb0-2-43-1 ∷ [])
  b0 = at 0 2 (Sb2-0-41-3 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F2-CS01∣CS23 c4)) ▸ done


-- tr comm2 I at 1: 1 steps
lem-tr-comm2-I-at-1 : Complete 4 → ⟪ (S4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ S4 ∷ []) ⟫ʷ
lem-tr-comm2-I-at-1 c4 = run b0
  where
  b0 : Chain (S4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ S4 ∷ [])
  b0 = at 0 2 (Sb0-1-42-3 ∷ S4 ∷ []) (lem-F2-iI∣CS12 c4) ▸ done


-- tr comm2 S0 at 1: 1 steps
lem-tr-comm2-S0-at-1 : Complete 4 → ⟪ (CS34 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ CS34 ∷ []) ⟫ʷ
lem-tr-comm2-S0-at-1 c4 = run b0
  where
  b0 : Chain (CS34 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ CS34 ∷ [])
  b0 = at 0 2 (Sb0-1-42-3 ∷ CS34 ∷ []) (lem-F2-S3∣CS12 c4) ▸ done


-- tr comm2 K0 at 1: 1 steps
lem-tr-comm2-K0-at-1 : Complete 4 → ⟪ (CK43 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ CK43 ∷ []) ⟫ʷ
lem-tr-comm2-K0-at-1 c4 = run b0
  where
  b0 : Chain (CK43 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ CK43 ∷ [])
  b0 = at 0 2 (Sb0-1-42-3 ∷ CK43 ∷ []) (lem-F2-K3∣CS12 c4) ▸ done


-- tr comm2 I at 2: 1 steps
lem-tr-comm2-I-at-2 : Complete 4 → ⟪ (S4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ S4 ∷ []) ⟫ʷ
lem-tr-comm2-I-at-2 c4 = run b0
  where
  b0 : Chain (S4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ S4 ∷ [])
  b0 = at 0 2 (Sb0-2-43-1 ∷ S4 ∷ []) (lem-F2-iI∣CS23 c4) ▸ done


-- calc F4 I I: 1 steps
lem-calc-F4-I-I : Complete 4 → ⟪ (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-I-I c4 = run b0
  where
  b0 : Chain (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  b0 = at 0 4 (S4 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ S4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- calc F4 I S0: 1 steps
lem-calc-F4-I-S0 : Complete 4 → ⟪ (X4 ∷ S4 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-I-S0 c4 = run b0
  where
  b0 : Chain (X4 ∷ S4 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  b0 = at 0 4 (CS04 ∷ X4 ∷ S4 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ S4 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ S4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- calc F4 I K0: 1 steps
lem-calc-F4-I-K0 : Complete 4 → ⟪ (X4 ∷ S4 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-I-K0 c4 = run b0
  where
  b0 : Chain (X4 ∷ S4 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  b0 = at 0 4 (CK40 ∷ X4 ∷ S4 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ S4 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ S4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- calc F4 I S1: 1 steps
lem-calc-F4-I-S1 : Complete 4 → ⟪ (X4 ∷ S4 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-I-S1 c4 = run b0
  where
  b0 : Chain (X4 ∷ S4 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  b0 = at 0 4 (CS14 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ S4 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ S4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- calc F4 I K1: 1 steps
lem-calc-F4-I-K1 : Complete 4 → ⟪ (X4 ∷ S4 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-I-K1 c4 = run b0
  where
  b0 : Chain (X4 ∷ S4 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  b0 = at 0 4 (CK41 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ S4 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ S4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- calc F4 I S2: 1 steps
lem-calc-F4-I-S2 : Complete 4 → ⟪ (X4 ∷ S4 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-I-S2 c4 = run b0
  where
  b0 : Chain (X4 ∷ S4 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  b0 = at 0 4 (CS24 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ S4 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ S4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- calc F4 I K2: 1 steps
lem-calc-F4-I-K2 : Complete 4 → ⟪ (X4 ∷ S4 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-I-K2 c4 = run b0
  where
  b0 : Chain (X4 ∷ S4 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  b0 = at 0 4 (CK42 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ S4 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ S4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- calc F4 I S3: 1 steps
lem-calc-F4-I-S3 : Complete 4 → ⟪ (X4 ∷ S4 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-I-S3 c4 = run b0
  where
  b0 : Chain (X4 ∷ S4 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  b0 = at 0 4 (CS34 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ S4 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ S4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- calc F4 I K3: 1 steps
lem-calc-F4-I-K3 : Complete 4 → ⟪ (X4 ∷ S4 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-I-K3 c4 = run b0
  where
  b0 : Chain (X4 ∷ S4 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  b0 = at 0 4 (CK43 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ S4 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ S4 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- calc F4 I CS01: 1 steps
lem-calc-F4-I-CS01 : Complete 4 → ⟪ (X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-I-CS01 c4 = run b0
  where
  b0 : Chain (X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  b0 = at 0 4 (Sb2-0-41-3 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-iIᵖ0∣CS01ᵖ1 c4) ▸ done


-- calc F4 I CS12: 1 steps
lem-calc-F4-I-CS12 : Complete 4 → ⟪ (X4 ∷ S4 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-I-CS12 c4 = run b0
  where
  b0 : Chain (X4 ∷ S4 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  b0 = at 0 4 (Sb0-1-42-3 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-iIᵖ0∣CS12ᵖ1 c4) ▸ done


-- calc F4 I CS23: 1 steps
lem-calc-F4-I-CS23 : Complete 4 → ⟪ (X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ
lem-calc-F4-I-CS23 c4 = run b0
  where
  b0 : Chain (X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ S4 ∷ X4 ∷ [])
  b0 = at 0 4 (Sb0-2-43-1 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-iIᵖ0∣CS23ᵖ1 c4) ▸ done

