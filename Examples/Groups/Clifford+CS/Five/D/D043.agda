{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D043 where

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
open import Examples.Groups.Clifford+CS.Five.D.D042 using (lem-auto-TOFF012-∣-SBOX⟨0·1·23·4⟩-at0110243243)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-1-TOFF104 ; lem-nat-1-TOFF204)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-nat-1-SBOX⟨1·0·42·3⟩ ; lem-nat-1-SBOX⟨2·0·41·3⟩)
-- auto TOFF012 | SBOX(0;1;23;4) @0210243143: 7 steps
lem-auto-TOFF012-∣-SBOX⟨0·1·23·4⟩-at0210243143 : Complete 4 → ⟪ (Toff204 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ Toff204 ∷ []) ⟫ʷ
lem-auto-TOFF012-∣-SBOX⟨0·1·23·4⟩-at0210243143 c4 = run b0
  where
  b0 : Chain (Toff204 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ Toff204 ∷ [])
  b0 = at 0 0 (Sw12 ∷ Sw12 ∷ []) (lw4 c4 [] (Sw12 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff104 ∷ Sw12 ∷ []) (lem-nat-1-TOFF204 c4) ▸
       at 2 2 (Sb1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·41·3⟩ c4) ▸
       at 1 2 (Sb1-0-42-3 ∷ Toff104 ∷ []) (lem-auto-TOFF012-∣-SBOX⟨0·1·23·4⟩-at0110243243 c4) ▸
       at 0 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ c4) ▸
       at 1 2 (Toff204 ∷ Sw12 ∷ []) (lem-nat-1-TOFF104 c4) ▸
       at 2 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸ done

